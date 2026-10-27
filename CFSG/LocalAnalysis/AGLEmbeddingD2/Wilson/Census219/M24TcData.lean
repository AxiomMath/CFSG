module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.TcNative
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24Check

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24 CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def m24xA : Array ℕ := natArr (wT xW)

@[expose] def m24caA : Array (Array ℕ) := #[natArr (wT ca1W), natArr (wT ca2W)]

@[expose] def m24sA : Array (Array ℕ) := #[natArr (wT s1W), natArr (wT s2W)]

@[expose] def m24TcD : TcData where
  gQ := #[#[5, 13, 22, 0, 15, 3, 11, 7, 18, 16, 10, 6, 9, 20, 23, 17, 4, 12, 14, 21, 1, 19, 8, 2], #[18, 4, 13, 23, 15, 22, 11, 6, 1, 16, 21, 19, 14, 9, 20, 8, 2, 12, 0, 7, 17, 10, 5, 3]]
  cu := #[#[16, 17, 5, 15, 18, 12, 21, 6, 0, 22, 11, 19, 2, 4, 3, 14, 8, 23, 13, 10, 9, 7, 20, 1], #[12, 8, 5, 16, 23, 15, 21, 19, 0, 18, 11, 7, 20, 2, 3, 1, 13, 22, 17, 10, 14, 6, 4, 9]]
  cv := #[#[22, 0, 12, 18, 17, 23, 6, 10, 16, 4, 21, 7, 20, 5, 15, 1, 13, 9, 14, 11, 3, 19, 8, 2], #[16, 23, 20, 15, 4, 12, 6, 21, 13, 9, 11, 19, 2, 18, 1, 14, 8, 17, 0, 7, 22, 10, 5, 3]]
  gK := #[#[16, 17, 2, 15, 13, 12, 7, 6, 8, 20, 11, 10, 5, 4, 14, 3, 0, 1, 18, 19, 9, 21, 22, 23], #[3, 12, 14, 5, 4, 0, 6, 11, 2, 9, 10, 21, 23, 15, 8, 18, 22, 17, 13, 19, 16, 7, 20, 1], m24xA]
  reps := #[idA 24, #[0, 1, 4, 3, 2, 5, 19, 7, 17, 14, 10, 21, 18, 13, 9, 22, 23, 8, 12, 6, 20, 11, 15, 16], #[0, 1, 12, 3, 18, 5, 21, 7, 16, 22, 10, 19, 2, 13, 15, 14, 8, 23, 4, 11, 20, 6, 9, 17], #[0, 1, 18, 3, 12, 5, 11, 7, 23, 15, 10, 6, 4, 13, 22, 9, 17, 16, 2, 21, 20, 19, 14, 8], #[0, 2, 1, 3, 23, 5, 21, 19, 20, 18, 10, 11, 12, 14, 13, 15, 16, 22, 9, 7, 8, 6, 17, 4], #[1, 2, 0, 20, 23, 13, 21, 19, 3, 18, 7, 6, 4, 14, 5, 9, 17, 22, 15, 10, 8, 11, 16, 12]]
  sig := #[#[3, 2, 1, 0, 4, 5], #[4, 2, 0, 5, 1, 3]]

@[expose] def m24TcCQ (_ : Unit := ()) : ArrCert := enumBfs 24 m24TcD.gQ (List.range 24) 1200

@[expose] def m24TcCK (_ : Unit := ()) : ArrCert := enumBfs 24 m24TcD.gK (List.range 24) 250

@[expose] def m24TcCS (_ : Unit := ()) : ArrCert := enumBfs 6 m24TcD.sig (List.range 6) 500

@[expose] def m24CC (_ : Unit := ()) : ArrCert := enumBfs 24 m24caA (List.range 24) 1200

@[expose] def m24SC (_ : Unit := ()) : ArrCert := enumBfs 24 m24sA (List.range 24) 40

@[expose] def m24TcOK (_ : Unit := ()) : Bool :=
  tcOK 24 6 (List.range 24) m24xA m24TcD (m24TcCQ ()) (m24TcCK ()) (m24TcCS ()) &&
    enumOK 24 m24caA (List.range 24) (m24CC ()) &&
    allLt m24TcD.gQ.size (fun l => (m24CC ()).pts.toList.any (eqA 24 m24TcD.gQ[l]!)) &&
    enumOK 24 m24sA (List.range 24) (m24SC ()) && ((m24SC ()).pts.size == 27) &&
    allLt (m24SC ()).pts.size (fun k => eqA 24 (powArr 24 (m24SC ()).pts[k]! 3) (idA 24))

end CFSG.AGLEmbeddingD2.Wilson.Census219
