module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYLin

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def m12A : Array ℕ := #[3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]

@[expose] def m12B : Array ℕ := #[7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]

@[expose] def m12Gens : Array (Array ℕ) := #[m12A, m12B]

@[expose] def m12Keys : List ℕ := [0, 1, 2, 3, 4]

@[expose] def m12Cert : ArrCert := enumBfs 12 m12Gens m12Keys 100000

@[expose] def m12Pts : List (Array ℕ) := m12Cert.pts.toList

@[expose] def m12Inv0 : Array ℕ := #[8, 5, 3, 2, 6, 1, 4, 11, 0, 10, 9, 7]

@[expose] def m12Inv1 : Array ℕ := #[5, 1, 8, 6, 4, 0, 3, 7, 2, 10, 9, 11]

@[expose] def m12Act (k : ℕ) (a : Array ℕ) : Array ℕ := conjA 12 m12Gens[k]! a

@[expose] def m12Cls0 : ArrCert := arrBfs m12Act m12Gens.size (keyA 12 m12Keys) m12Inv0 2000

@[expose] def m12Cls1 : ArrCert := arrBfs m12Act m12Gens.size (keyA 12 m12Keys) m12Inv1 2000

@[expose] def m12Pts0 : List (Array ℕ) := m12Cls0.pts.toList

@[expose] def m12Pts1 : List (Array ℕ) := m12Cls1.pts.toList

@[expose] def m12CGens : Array (Array ℕ) :=
  #[#[2, 6, 1, 5, 7, 4, 11, 10, 3, 0, 8, 9], #[1, 4, 2, 3, 11, 6, 7, 8, 5, 9, 10, 0],
    #[0, 3, 5, 1, 11, 2, 7, 6, 8, 9, 10, 4], m12Inv0]

@[expose] def m12CCert : ArrCert := enumBfs 12 m12CGens m12Keys 2000

@[expose] def m12CPts : List (Array ℕ) := m12CCert.pts.toList

@[expose] def m12DGens : Array (Array ℕ) :=
  #[#[1, 4, 9, 10, 3, 6, 2, 7, 5, 8, 0, 11], #[11, 4, 5, 1, 0, 6, 8, 2, 7, 9, 10, 3]]

@[expose] def m12DCert : ArrCert := enumBfs 12 m12DGens m12Keys 2000

@[expose] def m12DPts : List (Array ℕ) := m12DCert.pts.toList

@[expose] def isInvol12 (x : Array ℕ) : Bool :=
  validA 12 x && eqA 12 (compA 12 x x) (idA 12) && !eqA 12 x (idA 12)

@[expose] def m12OK : Bool :=
  enumOKL 12 m12Gens m12Keys m12Cert && m12Cert.pts.size == 95040 &&
    isInvol12 m12Inv0 && isInvol12 m12Inv1 &&
    arrCertOKL m12Act m12Gens.size (validA 12) (keyA 12 m12Keys) m12Inv0 m12Cls0 &&
    m12Cls0.pts.size == 396 &&
    arrCertOKL m12Act m12Gens.size (validA 12) (keyA 12 m12Keys) m12Inv1 m12Cls1 &&
    m12Cls1.pts.size == 495 &&
    m12Pts.all (fun x => !eqA 12 (compA 12 x x) (idA 12) || eqA 12 x (idA 12) ||
      m12Pts0.any (eqA 12 x) || m12Pts1.any (eqA 12 x)) &&
    enumOKL 12 m12CGens m12Keys m12CCert && m12CCert.pts.size == 240 &&
    allLt m12CGens.size (fun k => eqA 12 (compA 12 m12Inv0 m12CGens[k]!)
      (compA 12 m12CGens[k]! m12Inv0) && m12Pts.any (eqA 12 m12CGens[k]!)) &&
    enumOKL 12 m12DGens m12Keys m12DCert && m12DCert.pts.size == 60 &&
    m12CPts.all (fun x => m12CPts.all (fun y => m12DPts.any (eqA 12 (commutatorA 12 x y)))) &&
    m12DPts.all (fun d => !eqA 12 (compA 12 d d) (idA 12) ||
      m12Pts0.any (eqA 12 (compA 12 m12Inv0 d)))

end CFSG.EvenSporadicStandard.HSStd.FiveY
