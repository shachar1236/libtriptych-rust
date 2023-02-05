#![allow(non_snake_case)]

use curve25519_dalek::ristretto::{RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::Identity;
use libc::size_t;

use crate::util;
use crate::Errors::{self, TriptychError};
use std::convert::TryInto;
use sha2::Sha512;

// use serde::{Serialize, Deserialize};

use std::mem::size_of_val;
use std::ptr::drop_in_place;
use std::alloc::Layout;
use std::alloc::dealloc;

// #[derive(Clone, Debug, Serialize, Deserialize)]
#[derive(Clone, Debug)]
pub struct TriptychEllipticCurveState {
    J: RistrettoPoint,
    A: RistrettoPoint,
    B: RistrettoPoint,
    C: RistrettoPoint,
    D: RistrettoPoint,
    X: Vec<RistrettoPoint>,
    Y: Vec<RistrettoPoint>
}

#[derive(Clone, Debug)]
pub struct TriptychScalarState {
    f: Vec<Vec<Scalar>>,
    zA: Scalar,
    zC: Scalar,
    z: Scalar
}

#[derive(Clone, Debug)]
pub struct Signature {
    a: TriptychEllipticCurveState,
    z: TriptychScalarState
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
fn base_prove(M: &[RistrettoPoint], l: &usize, r: &Scalar, m: &usize, message: &str) -> Signature{
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

    transcript.extend_from_slice(message.as_bytes());
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
fn base_verify(M: &[RistrettoPoint], sgn: &Signature, m: &usize, message: &str) -> Result<(), Errors> {
    
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
    transcript.extend_from_slice(message.as_bytes());
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

pub fn DeserializePublicKey(bytes: Vec<u8>) -> Result<RistrettoPoint, Box<bincode::ErrorKind>> {
    return bincode::deserialize(&bytes[..]);
}

const PRIVATE_KEY_SIZE:usize = 32;

pub fn SerializePrivateKey(sc: Scalar) ->  [u8; PRIVATE_KEY_SIZE] {
    let encoded = sc.to_bytes();
    return encoded;
}

pub fn DeserializePrivateKey(bytes: [u8; 32]) ->  Option<Scalar> {
    return  Scalar::from_canonical_bytes(bytes).into();
}

pub fn SerializePublicKeysList(R: &[RistrettoPoint]) -> Result<Vec<u8>, Box<bincode::ErrorKind>> {
    let encoded = bincode::serialize(&R);
    return  encoded;
}

pub fn DeserializePublicKeysList(bytes: Vec<u8>) -> Result<Vec<RistrettoPoint>, Box<bincode::ErrorKind>> {
    return  bincode::deserialize(&bytes[..]);
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

#[no_mangle]
pub extern "C" fn FreePublicKey(ptr: *mut u8, len: size_t) {
    FreeVector(ptr, len);
}

#[no_mangle]
pub extern "C" fn FreeSlice(ptr: *mut u8, len: size_t) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        std::slice::from_raw_parts(ptr, len);
    }
}

#[no_mangle]
pub extern "C" fn FreePrivateKey(ptr: *mut u8) {
    FreeSlice(ptr, PRIVATE_KEY_SIZE);
}

#[no_mangle]
pub extern "C" fn GeneratePrivateKey() -> *mut u8 {
    let mut rng = rand::thread_rng();
    let r = Scalar::random(&mut rng);

    let mut ser= SerializePrivateKey(r);
    
    println!("priv key rust:{:?}", ser);

    // prevents deallocation in rust
    std::mem::forget(ser);
    
    return ser.as_mut_ptr();
}

#[no_mangle]
pub extern "C" fn GeneratePublicKeyFromPrivateKey(private_key_ptr: *mut u8, recive_len: *mut size_t) -> *mut u8 {
    let private_key: &[u8; PRIVATE_KEY_SIZE];
    unsafe {
        // bad code should not user unwrap!!!
        private_key = std::slice::from_raw_parts(private_key_ptr, PRIVATE_KEY_SIZE).try_into().unwrap();
    }
    // bad code. should check if good before unwraaping
    let r = DeserializePrivateKey(*private_key).unwrap();

    let G = util::hash_to_point("G"); 
    
    let public_key: RistrettoPoint = r*G;
    // bad code. should check if good before unwraaping
    let mut ser = SerializePublicKey(&public_key).unwrap();
    
    println!("pub key rust: {:?}", ser);

    unsafe {
        *recive_len = ser.len();
    }

    ser.shrink_to_fit();

    let ret = ser.as_mut_ptr();

    // prevents deallocation in rust
    std::mem::forget(ser);
    std::mem::forget(private_key);

    return ret;
}

pub fn Sign(x: &Scalar, M: &str, R: &[RistrettoPoint]) -> Signature {
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

pub fn Verify(sgn: &Signature, M: &str, R: &[RistrettoPoint]) ->  Result<(), Errors> {
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
