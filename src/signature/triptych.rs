#![allow(non_snake_case)]
use bincode::ErrorKind;
use serde::{Deserialize, Serialize};
use std::fs::File;
use curve25519_dalek::ristretto::{RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;
use libc::size_t;

use crate::util;
use crate::Errors::{self, TriptychError};
use std::convert::TryInto;
use std::ffi::CStr;
use sha2::Sha512;

// use serde::{Serialize, Deserialize};

use std::mem::size_of_val;
use std::ptr::drop_in_place;
use std::alloc::Layout;
use std::alloc::dealloc;

// #[derive(Clone, Debug, Serialize, Deserialize)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TriptychEllipticCurveState {
    J: RistrettoPoint,
    A: RistrettoPoint,
    B: RistrettoPoint,
    C: RistrettoPoint,
    D: RistrettoPoint,
    X: Vec<RistrettoPoint>,
    Y: Vec<RistrettoPoint>
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TriptychScalarState {
    f: Vec<Vec<Scalar>>,
    zA: Scalar,
    zC: Scalar,
    z: Scalar
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Signature {
    a: TriptychEllipticCurveState,
    z: TriptychScalarState
}

//deserialize signature
pub fn SerializeSignature(S: &Signature) -> Result<Vec<u8>, Box<ErrorKind>>{
    let encoded = bincode::serialize(&S);
    return encoded;
}

pub fn DeserializeSignature(bytes: &[u8]) -> Result<Signature, Box<bincode::ErrorKind>>{
    return bincode::deserialize(&bytes[..]);
}

pub fn GetSize(sgn: &Signature) ->  usize {
    let mut size = size_of_val(&sgn.a.J);
    size += size_of_val(&sgn.a.A);
    size += size_of_val(&sgn.a.B);
    size += size_of_val(&sgn.a.C);
    size += size_of_val(&sgn.a.D);
    size += size_of_val(&*sgn.a.X);
    size += size_of_val(&*sgn.a.Y);

    for s in sgn.z.f.iter() {
        size += size_of_val(&*s);
    }

    size += size_of_val(&sgn.z.zA);
    size += size_of_val(&sgn.z.zC);
    size += size_of_val(&sgn.z.z);
    return size;
}

// This is the core Sigma Protocol being implemented, not the signature protocol
fn base_prove(M: &[RistrettoPoint], l: &usize, r: &Scalar, m: &usize, message: &[u8]) -> Signature{
    let n: usize = 2; // base of decomposition, Tryptich supports arbitary base, we prefer binary here

    let U = util::hash_to_point("U");

    let G = util::hash_to_point("G"); 
    // In Risretto Curve, all POINTS are generators. G choice is arbitary here
    let mut rng = rand::thread_rng();

    let mut transcript: Vec<u8> = Vec::with_capacity(40000);

    let J = r.invert()*U;
    let rA = Scalar::random(&mut rng);
    let rB = Scalar::random(&mut rng);
    let rC = Scalar::random(&mut rng);
    let rD = Scalar::random(&mut rng); 


    let mut a = (0..*m).map(|_| (0..n).map(|_| Scalar::random(&mut rng)).collect::<Vec<Scalar>>()).collect::<Vec<Vec<Scalar>>>();

    for entry in &mut a {
        entry[0] = (1..n).fold(Scalar::zero(), |acc, x|{
            acc - entry[x]
        });
    }

    let A = util::pedersen_commitment(&a, &rA);

    for entry in M {
        transcript.extend_from_slice(entry.compress().as_bytes());
    }

    transcript.extend_from_slice(message);
    transcript.extend_from_slice(J.compress().as_bytes());
    transcript.extend_from_slice(A.compress().as_bytes());
    


    let s = util::pad(&l, &m);

    let b = (0..*m).map(|j| (0..n).map(|i| util::delta(&s[j], &i)).collect::<Vec<Scalar>>()).collect::<Vec<Vec<Scalar>>>();

    let B = util::pedersen_commitment(&b, &rB);

    let c = (0..*m).map(|j| (0..n).map(|i| a[j][i]*(Scalar::one() - b[j][i] - b[j][i])).collect::<Vec<Scalar>>()).collect::<Vec<Vec<Scalar>>>();

    let C = util::pedersen_commitment(&c, &rC);

   
    let d = (0..*m).map(|j| (0..n).map(|i| -a[j][i]*a[j][i]).collect::<Vec<Scalar>>()).collect::<Vec<Vec<Scalar>>>();

    let D = util::pedersen_commitment(&d, &rD);

    transcript.extend_from_slice(B.compress().as_bytes());
    transcript.extend_from_slice(C.compress().as_bytes());
    transcript.extend_from_slice(D.compress().as_bytes());


    let m_u32: u32 = (*m).try_into().unwrap();
    let N = usize::pow(n, m_u32); // we have n = 2, N = 2**m = len(M)

    let mut p = (0..N).map(|_| vec![]).collect::<Vec<Vec<Scalar>>>();

    for k in 0..N {
        let binary_k = util::pad(&k, &m); 
        p[k] = vec![a[0][binary_k[0]], util::delta(&s[0], &binary_k[0])];

        for j in 1..*m {
            p[k] = util::convolve(&p[k], &vec![a[j][binary_k[j]], util::delta(&s[j], &binary_k[j])]);
        }
    }

    

    let rho = (0..*m).map(|_| Scalar::random(&mut rng)).collect::<Vec<Scalar>>();

    let Y = (0..*m).map(|i| rho[i]*J).collect::<Vec<RistrettoPoint>>();

    let X = (0..*m).map(|j| (0..N).fold(rho[j]*G, |acc, k|{
                                            acc + p[k][j]*M[k]
                                        })).collect::<Vec<RistrettoPoint>>();

    for i in 0..*m {
        transcript.extend_from_slice(Y[i].compress().as_bytes());
        transcript.extend_from_slice(X[i].compress().as_bytes());
    }

    let ellipticstate: TriptychEllipticCurveState = TriptychEllipticCurveState {
        J, A, B, C, D, X, Y
    };
   
    let challenge = Scalar::hash_from_bytes::<Sha512>(&transcript);

    let f = (0..*m).map(|j| (1..n).map(|i| util::delta(&s[j], &i)*challenge + a[j][i]).collect::<Vec<Scalar>>()).collect::<Vec<Vec<Scalar>>>();

    let zA = rA + challenge*rB;
    let zC = challenge*rC + rD;

    

    let z = r*util::power(&challenge, &m) - (0..*m).fold(Scalar::zero(), |acc, j|{ acc + rho[j]*util::power(&challenge, &j)});

    let scalarstate: TriptychScalarState = TriptychScalarState {
        f, zA, zC, z
    };

    return Signature {
        a: ellipticstate, z: scalarstate
    };

}

// Verification of the base sigma protocol
fn base_verify(M: &[RistrettoPoint], sgn: &Signature, m: &usize, message: &[u8]) -> Result<(), Errors> {
    
    let mut transcript: Vec<u8> = Vec::with_capacity(1000);
    let ellipticState = &sgn.a;
    let scalarState = &sgn.z;
    let G = util::hash_to_point("G"); 
    let U = util::hash_to_point("U");


    let n = 2;
    let m_u32: u32 = (*m).try_into().unwrap();
    let N = usize::pow(n, m_u32); // we have n = 2, N = 2**m = len(M)

    for entry in M {
        transcript.extend_from_slice(entry.compress().as_bytes());
    }
    transcript.extend_from_slice(message);
    transcript.extend_from_slice(ellipticState.J.compress().as_bytes());
    transcript.extend_from_slice(ellipticState.A.compress().as_bytes());
    transcript.extend_from_slice(ellipticState.B.compress().as_bytes());
    transcript.extend_from_slice(ellipticState.C.compress().as_bytes());
    transcript.extend_from_slice(ellipticState.D.compress().as_bytes());

    for i in 0..*m {
        transcript.extend_from_slice(ellipticState.Y[i].compress().as_bytes());
        transcript.extend_from_slice(ellipticState.X[i].compress().as_bytes());
    }

    let challenge = Scalar::hash_from_bytes::<Sha512>(&transcript);

    let mut f: Vec<Vec<Scalar>> = vec![vec![Scalar::zero(); n]; *m];

    for i in 0..*m {
        f[i][0] = challenge;
        for j in 1..n {
            f[i][j] = scalarState.f[i][j-1];
            f[i][0] = f[i][0] - f[i][j];
        }
    }

    let comFirst = util::pedersen_commitment(&f, &scalarState.zA);

    let fMult = (0..*m).map(|j| (0..n).map(|i| f[j][i]*(challenge - f[j][i])).collect::<Vec<Scalar>>()).collect::<Vec<Vec<Scalar>>>();

    let comSecond = util::pedersen_commitment(&fMult, &scalarState.zC);

    let firstLHS = ellipticState.A + ellipticState.B*challenge;
    let secondLHS = ellipticState.D + ellipticState.C*challenge;

    let thirdLHS = (0..*m).fold(scalarState.z*G, |acc, j|{
        acc + ellipticState.X[j]*util::power(&challenge, &j)
    });

    let fourthLHS = (0..*m).fold(scalarState.z*ellipticState.J, |acc, j|{
        acc + ellipticState.Y[j]*util::power(&challenge, &j)
    });

    let mut thirdRHS = RistrettoPoint::identity();

    let mut fourthRHSScalar = Scalar::zero();
    for k in 0..N {
        let binary_k = util::pad(&k, &m); 
        
        let mut product_term = Scalar::one();

        for j in 0..*m {
            product_term = f[j][binary_k[j]]*product_term;
        }

        thirdRHS = thirdRHS + M[k]*product_term;

        fourthRHSScalar = fourthRHSScalar + product_term;
    }
    let fourthRHS = U*fourthRHSScalar;

    if firstLHS == comFirst && secondLHS == comSecond && thirdLHS == thirdRHS && fourthLHS == fourthRHS {
        return Ok(());
    }
    else {
        return Err(TriptychError);
    }
    
}

pub fn KeyGen() -> (Scalar, RistrettoPoint) {
    let mut rng = rand::thread_rng();
    let r = Scalar::random(&mut rng);
    let G = util::hash_to_point("G"); 

    return (r, r*G);
}



pub fn SerializePublicKey(R: &RistrettoPoint) -> Result<Vec<u8>, Box<bincode::ErrorKind>> {
    let encoded = bincode::serialize(&R);
    return  encoded;
}

pub fn DeserializePublicKey(bytes: &[u8]) -> Result<RistrettoPoint, Box<bincode::ErrorKind>> {
    return bincode::deserialize(&bytes[..]);
}

const PRIVATE_KEY_SIZE:usize = 32;

pub fn SerializePrivateKey(sc: &Scalar) ->  [u8; PRIVATE_KEY_SIZE] {
    let encoded = sc.to_bytes();
    return encoded;
}

pub fn DeserializePrivateKey(bytes: &Box<[u8; 32]>) ->  Option<Scalar> {
    return  Scalar::from_canonical_bytes(**bytes).into();
}

pub fn SerializePublicKeysList(R: &[RistrettoPoint]) -> Result<Vec<u8>, Box<bincode::ErrorKind>> {
    let encoded = bincode::serialize(&R);
    return  encoded;
}

pub fn DeserializePublicKeysList(bytes: Vec<u8>) -> Result<Vec<RistrettoPoint>, Box<bincode::ErrorKind>> {
    return  bincode::deserialize(&bytes[..]);
}

fn PrivateKeyBytesFromPointer(ptr: *mut u8) -> Box<[u8; PRIVATE_KEY_SIZE]>  {
    let private_key_bytes: Box<[u8; PRIVATE_KEY_SIZE]> = unsafe {
        Box::from_raw(ptr as *mut [u8; PRIVATE_KEY_SIZE])
    };
    return private_key_bytes;
}

fn BytesFromPointer(ptr: *mut u8, len: size_t) -> Box<[u8]>  {
    let ret = unsafe {
        Vec::from_raw_parts(ptr, len, len)
    };
    return ret.into_boxed_slice();
}


#[no_mangle]
pub extern "C" fn FreeVector(ptr: *mut u8, len: size_t) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        Vec::from_raw_parts(ptr, len, len);
    }
}


#[repr(C)]
#[derive(Clone)]
pub struct DynArray {
    array: *mut u8,
    length: libc::size_t,
}

fn EmptyDynArray() -> DynArray {
    return DynArray{
        length: 0,
        array: 0 as *mut u8,
    };
}


#[no_mangle]
pub extern "C" fn AllocDynArrayVector(len: size_t) -> *mut DynArray {
    let c = vec![DynArray{ length: 0, array: 0 as *mut u8};len];
    let BoxC = c.into_boxed_slice();
    return Box::into_raw(BoxC) as *mut DynArray;
}

#[no_mangle]
pub extern "C" fn FreeDynArrayVector(ptr: *mut DynArray, len: size_t) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        Vec::from_raw_parts(ptr, len, len);
    }
}

fn PublicKeysBytes2dVectorFromPointer(public_keys_raw: *mut DynArray, public_keys_size: size_t) -> Result<Vec<RistrettoPoint>, bool> {
    // getting public keys
    let public_keys_bytes = unsafe { std::slice::from_raw_parts(public_keys_raw, public_keys_size) };

    // proccessing keys
    let mut public_keys: Vec<RistrettoPoint> = Vec::with_capacity(public_keys_size);
    for key_bytes in public_keys_bytes.iter() {
        let ser_pk = BytesFromPointer(key_bytes.array, key_bytes.length);
        // getting key
        let key_result = DeserializePublicKey(&ser_pk);
        // prevents deallocation
        let mut ser_pk = std::mem::ManuallyDrop::new(ser_pk);
        // checking result
        match key_result {
            Ok(key) => {
                public_keys.push(key);
            },
            Err(e) => {
                // prevents deallocation
                std::mem::forget(public_keys_bytes);
                return Err(true);
            }
        }
    }
    
    // prevents deallocation
    std::mem::forget(public_keys_bytes);
    
    return Ok(public_keys);
}

fn SignaturesBytes2dVectorFromPointer(signatures_raw: *mut DynArray, num_of_signatures: size_t) -> Result<Vec<Signature>, bool> {
    // getting public keys
    let signatures_bytes = unsafe { std::slice::from_raw_parts(signatures_raw, num_of_signatures) };

    // proccessing keys
    let mut signatures: Vec<Signature> = Vec::with_capacity(num_of_signatures);
    for sgn_bytes in signatures_bytes.iter() {
        let ser_sgn = BytesFromPointer(sgn_bytes.array, sgn_bytes.length);
        // prevents deallocation
        let mut ser_sgn = std::mem::ManuallyDrop::new(ser_sgn);
        // getting signature
        let signature_result = DeserializeSignature(&ser_sgn);

        match signature_result {
            Ok(signature) => {
                signatures.push(signature);
            },
            Err(e) => {
                // prevents deallocation
                std::mem::forget(signatures_bytes);
                return Err(true);
            }
        }

    }
    
    // prevents deallocation
    std::mem::forget(signatures_bytes);
    
    return Ok(signatures);
}

#[no_mangle]
pub extern "C" fn FreePrivateKey(ptr: *mut u8) {
    if ptr.is_null() {
        return;
    }
    
    PrivateKeyBytesFromPointer(ptr);
}

#[no_mangle]
pub extern "C" fn FreePublicKey(ptr: *mut u8, len: size_t) {
    FreeVector(ptr, len);
}

#[no_mangle]
pub extern "C" fn GeneratePrivateKey() -> *mut u8 {
    let mut rng = rand::thread_rng();
    let r = Scalar::random(&mut rng);

    let mut ser= SerializePrivateKey(&r);
    
    // println!("priv key rust:{:?}", ser);
    
    let ser_vec = ser.to_vec();

    return Box::into_raw(ser_vec.into_boxed_slice()) as *mut u8;
}

#[no_mangle]
pub extern "C" fn GeneratePublicKeyFromPrivateKey(private_key_ptr: *mut u8, error_occured: *mut libc::c_char) -> DynArray {
    let private_key = PrivateKeyBytesFromPointer(private_key_ptr);
    
    
    let r_result = DeserializePrivateKey(&private_key);

    let deallo_prevent = || {
        // prevents deallocation in rust
        Box::into_raw(private_key);
    };

    let r: Scalar;
    if let Some(sc) = r_result {
        r = sc;
    } else {
        deallo_prevent();
        unsafe {
            *error_occured = 1;
        }
        return EmptyDynArray();
    }

    let G = util::hash_to_point("G"); 
    
    let public_key: RistrettoPoint = r*G;
    // bad code. should check if good before unwraaping
    let mut ser_result = SerializePublicKey(&public_key);
    let ser: Box<[u8]>;
    match ser_result {
        Ok(bytes) => {
            ser = bytes.into_boxed_slice();
        },
        Err(e) => {
            deallo_prevent();
            unsafe {
                *error_occured = 1;
            }
            
            return EmptyDynArray();
        }
    }
    
    // println!("pub key rust: {:?}", ser);

    let arr = DynArray{
        length: ser.len(),
        array: Box::into_raw(ser) as *mut u8,
    };

    deallo_prevent();

    return arr;
}

#[no_mangle]
pub extern "C" fn RSSign(private_key_ptr: *mut u8, message_raw: *mut u8, message_size: libc::size_t, public_keys_raw: *mut DynArray, public_keys_size: size_t, error_occured: *mut libc::c_char) -> DynArray {
    // getting private keys
    let private_key_bytes = PrivateKeyBytesFromPointer(private_key_ptr);
    
    let private_key_option = DeserializePrivateKey(&private_key_bytes);
    let private_key: Scalar;
    match private_key_option {
        Some(s) => {
            private_key = s;
        },
        None => {
            unsafe {
                *error_occured = 1;
            }
            return EmptyDynArray();
        },
    }
    
    let deallo_prevent = || {
        // preventing deallocation
        Box::into_raw(private_key_bytes);
    };
    
    // getting m
    let m = BytesFromPointer(message_raw, message_size);
    
    let public_keys_result = PublicKeysBytes2dVectorFromPointer(public_keys_raw, public_keys_size);
    let public_keys: Vec<RistrettoPoint>;
    match public_keys_result {
        Ok(r) => {
            public_keys = r;
        },
        Err(e) => {
            deallo_prevent();
            unsafe {
                *error_occured = 1;
            }
            return EmptyDynArray();
        }
    }
    
    // function end
    deallo_prevent();
    
    // calling function
    let res = Sign(&private_key, &m, &public_keys);
    
    let signature_result = SerializeSignature(&res);
    match signature_result {
        Ok(sig) => {
            let sigRes = sig.into_boxed_slice();
            return DynArray{
                length: sigRes.len(),
                array: Box::into_raw(sigRes) as *mut u8
            };
        },
        Err(e) => {
            unsafe {
                *error_occured = 1;
            }
        }
    }
    return DynArray{array: std::ptr::null_mut(), length: 0};
}

#[no_mangle]
pub extern "C" fn RSVerify(signature_raw: DynArray, message_raw: *mut u8, message_size: libc::size_t, public_keys_raw: *mut DynArray, public_keys_size: size_t, error_occured: *mut libc::c_char) -> libc::c_char {
    // getting signature
    let signature_bytes = BytesFromPointer(signature_raw.array, signature_raw.length);
    

    let signature_result = DeserializeSignature(&signature_bytes);

    let deallo_prevent = || {
        // preventing deallocation
        Box::into_raw(signature_bytes);
    };

    let signature: Signature;
    match signature_result {
        Ok(s) => {
            signature = s;
        },
        Err(e) => {
            deallo_prevent();
            unsafe {
                *error_occured = 1;
            }
            return 0;
        }
    }
    
    // getting m
    let m = BytesFromPointer(message_raw, message_size);
    
    let public_keys_result = PublicKeysBytes2dVectorFromPointer(public_keys_raw, public_keys_size);
    let public_keys: Vec<RistrettoPoint>;
    match public_keys_result {
        Ok(r) => {
            public_keys = r;
        },
        Err(e) => {
            deallo_prevent();
            unsafe {
                *error_occured = 1;
            }
            return 0;
        }
    }

    // function end
    deallo_prevent();
    
    // calling function
    let res = Verify(&signature, &m, &public_keys);
    
    // let res_bytes = SerializeSignature()
    return if res.is_ok() { 1 } else { 0 };
}

#[no_mangle]
pub extern "C" fn HasLinkInList(signature_raw: DynArray, signatures_raw: *mut DynArray, num_of_signatures: size_t, error_occured: *mut libc::c_char) -> libc::c_char {
    // getting signature
    let signature_bytes = BytesFromPointer(signature_raw.array, signature_raw.length);
    let signature_result = DeserializeSignature(&signature_bytes);
    
    // preventing deallocation
    Box::into_raw(signature_bytes);

    let signature: Signature;
    match signature_result {
        Ok(s) => {
            signature = s;
        },
        Err(e) => {
            unsafe {
                *error_occured = 1;
            }
            return 0;
        }
    }
    
    let signatures_array_reult = SignaturesBytes2dVectorFromPointer(signatures_raw, num_of_signatures);
    let signatures_array: Vec<Signature>;
    match signatures_array_reult {
        Ok(s) => {
            signatures_array = s;
        },
        Err(e) => {
            unsafe {
                *error_occured = 1;
            }
            return 0;
        }
    }

    for sgn in signatures_array.iter() {
        if Link(&signature, sgn) {
            return 1;
        }
    }
    
    return 0;
}

pub fn Sign(x: &Scalar, M: &[u8], R: &[RistrettoPoint]) -> Signature {
    let G = util::hash_to_point("G"); 

    let mut l: usize = 0;
    for (i, element) in R.iter().enumerate() {
        if  *element == x*G {
            l = i;
        }
    }

    let size = R.len();
    let mut base = 1;
    let mut m = 0;
    while base < size {
        base = base*2;
        m = m+1;
    }

    return base_prove(R, &l, x, &m, M);
}

pub fn Verify(sgn: &Signature, M: &[u8], R: &[RistrettoPoint]) ->  Result<(), Errors> {
    let size = R.len();
    let mut base = 1;
    let mut m = 0;

    while base < size {
        base = base*2;
        m = m+1;
    }

    return base_verify(R, sgn, &m, M);
}

pub fn Link(sgn_a: &Signature, sgn_b: &Signature) -> bool {
    return sgn_a.a.J == sgn_b.a.J;
}

#[cfg(test)]
mod triptych_test {

    use curve25519_dalek::digest::generic_array::typenum::assert_type;
    use curve25519_dalek::ristretto::{RistrettoPoint};
    use curve25519_dalek::scalar::Scalar;
    use curve25519_dalek::traits::Identity;
    use crate::signature::triptych;
    use crate::util;

    use super::{GeneratePrivateKey, FreeVector, GeneratePublicKeyFromPrivateKey, FreePublicKey, FreePrivateKey};
    
    #[test]
    pub fn test_base_signature(){
        let G = util::hash_to_point("G"); 
        let m: usize = 4;
        let l: usize = 12;
        let len_M = 16;

        let mut M: Vec<RistrettoPoint> = vec![RistrettoPoint::identity(); len_M];

        let mut rng = rand::thread_rng();
        let mut r: Scalar = Scalar::one();
        for i in 0..len_M {
            let sk = Scalar::random(&mut rng);
            M[i] = sk*G;

            if i == l {
                r = sk;
            }
        }

        let sgn: triptych::Signature = triptych::base_prove(&M, &l, &r, &m, "demo");

        let result = triptych::base_verify(&M, &sgn, &m, "demo");

        assert!(result.is_ok());

    }

    #[test]
    pub fn test_signature(){
        let size = 64;
        let mut R: Vec<RistrettoPoint> = vec![RistrettoPoint::identity(); size];
        let mut x: Scalar = Scalar::one();
        let index = 14;

        for i in 0..size {
            let (sk, pk) = triptych::KeyGen();
            R[i] = pk;

            if i == index {
                x = sk;
            }
        }
        let M = "This is a triptych signature test, lets see if it works or not";

        let sgn = triptych::Sign(&x, &M, &R);

        let result = triptych::Verify(&sgn, &M, &R);

        assert!(result.is_ok());

    }

    #[test]
    pub fn test_serialize_scalar(){
        let (sc, _) = triptych::KeyGen();

        let encoded = triptych::SerializePrivateKey(sc);
        
        let decoded: Option<Scalar> = triptych::DeserializePrivateKey(encoded);
        
        assert!(!decoded.is_none());
        
        let sc_decoded = decoded.unwrap();
        
        assert_eq!(sc, sc_decoded);

    }

    #[test]
    pub fn test_serialize_rissoto_point(){
        let (_, rp) = triptych::KeyGen();
        
        let encoded = triptych::SerializePublicKey(&rp).unwrap();
        
        let decoded = bincode::deserialize(&encoded[..]).unwrap();
        assert_eq!(rp, decoded);
    }

    #[test]
    pub fn test_wrapper_free() {
        let priv_key = GeneratePrivateKey();
        
        let mut pub_key_len:libc::size_t = 0;
        let pub_key = GeneratePublicKeyFromPrivateKey(priv_key, &mut pub_key_len);
        
        FreePublicKey(pub_key, pub_key_len);
        FreePrivateKey(priv_key);
    }

}
