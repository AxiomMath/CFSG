module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Kit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer

@[expose] def m24ThreeA : Array ℕ := #[3, 6, 16, 0, 12, 8, 1, 14, 5, 18, 17, 20, 4, 15, 7, 13, 2, 10, 9, 23, 11, 22, 21, 19]

@[expose] def m24ThreeB : Array ℕ := #[3, 20, 8, 5, 17, 0, 6, 7, 14, 4, 10, 11, 16, 1, 2, 12, 15, 9, 23, 19, 13, 21, 18, 22]

@[expose] def m24ThreeArrs : Array (Array ℕ) :=
  #[m24ThreeA, m24ThreeB,
    #[0, 11, 5, 8, 10, 3, 1, 14, 7, 12, 17, 20, 2, 6, 16, 4, 13, 18, 19, 23, 15, 22, 9, 21],
    #[0, 22, 20, 19, 4, 7, 17, 2, 15, 14, 3, 11, 6, 23, 12, 21, 5, 1, 10, 8, 13, 18, 9, 16],
    #[0, 15, 14, 16, 4, 21, 18, 7, 12, 17, 11, 23, 5, 8, 13, 20, 1, 3, 10, 6, 9, 2, 19, 22],
    #[0, 21, 15, 9, 4, 7, 6, 12, 3, 18, 14, 16, 1, 2, 22, 23, 13, 11, 10, 5, 19, 20, 8, 17],
    #[0, 14, 16, 15, 4, 21, 6, 2, 9, 10, 11, 19, 12, 18, 7, 17, 1, 23, 20, 8, 5, 13, 3, 22],
    #[0, 10, 17, 16, 4, 13, 6, 1, 11, 7, 15, 22, 12, 21, 23, 9, 19, 3, 5, 2, 18, 20, 14, 8],
    #[0, 17, 15, 8, 4, 13, 6, 11, 3, 14, 10, 7, 12, 5, 9, 2, 16, 1, 18, 23, 21, 20, 22, 19],
    #[0, 2, 1, 23, 4, 21, 6, 14, 19, 11, 10, 9, 12, 20, 7, 17, 16, 15, 18, 8, 13, 5, 22, 3],
    #[0, 11, 9, 20, 4, 19, 6, 17, 21, 2, 10, 1, 12, 23, 15, 14, 16, 7, 18, 5, 3, 8, 22, 13],
    #[0, 21, 3, 17, 4, 15, 6, 23, 13, 1, 18, 7, 12, 20, 5, 14, 16, 2, 22, 19, 8, 9, 10, 11]]

@[expose] def m24ThreeWords : Array (List ℤ) :=
  #[[], [], [-1, 2], [-3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -3, -1, -3, -3, 2, 3, 3, 1], [-3, -4, -4, 3, 3, 3, 3], [-5, -4, 5, 5], [-5, -4, 6, 5], [6, 7, 7, 6], [7, 8, 8], [-8, -9, 8, 7, 7], [-7, -10, -6, -6, -6, 8, 6, 6], [-9, -10, -11, -7, -11, 7, 8, 7]]

@[expose] def m24ThreeBase : List (Fin 24) := [0, 4, 6, 12, 16, 19, 1, 21, 9]

@[expose] def m24ThreeBaseArr : Array ℕ := (m24ThreeBase.map Fin.val).toArray

@[expose] def m24ThreeKeys : List ℕ := m24ThreeBase.map Fin.val

@[expose] def m24ThreeRels : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 0, 2), (1, 1, 1), (1, 1, 2), (2, 2, 1), (2, 2, 2), (3, 3, 1), (3, 3, 2), (4, 4, 1), (4, 4, 2), (5, 5, 1), (5, 5, 2), (6, 7, 1), (6, 8, 2), (7, 8, 1), (7, 6, 2), (8, 6, 1), (8, 7, 2)]

@[expose] def m24ThreeGens : Array (Array ℕ) :=
  #[#[0, 21, 3, 17, 4, 15, 6, 23, 13, 1, 18, 7, 12, 20, 5, 14, 16, 2, 22, 19, 8, 9, 10, 11], #[16, 17, 18, 22, 19, 8, 12, 9, 5, 3, 23, 21, 4, 15, 20, 13, 0, 10, 11, 6, 14, 2, 7, 1], #[6, 10, 14, 5, 16, 21, 0, 20, 11, 22, 17, 13, 19, 7, 1, 9, 12, 15, 2, 4, 23, 18, 3, 8]]

@[expose] def m24ThreeCert (_ : Unit := ()) : ArrCert :=
  enumBfs 24 m24ThreeGens m24ThreeKeys 1100

@[expose] def m24ThreeCheck (_ : Unit := ()) : Bool :=
  caseChainOK2P 24 m24ThreeArrs m24ThreeBaseArr m24ThreeWords m24ThreeA m24ThreeB &&
    validA 24 m24ThreeA && validA 24 m24ThreeB &&
    (rawOrbitSizes 24 m24ThreeArrs m24ThreeBaseArr == [24, 23, 22, 21, 20, 16, 3, 1, 1]) &&
    centOKP 3 24 m24ThreeArrs m24ThreeBaseArr m24ThreeGens[0]! m24ThreeRels m24ThreeGens
      m24ThreeKeys (m24ThreeCert ()) 1080 &&
    eqA 24 (powArr 24 m24ThreeGens[0]! 3) (idA 24) &&
    !(eqA 24 m24ThreeGens[0]! (idA 24)) &&
    gfr3ClassOK 24 (m24ThreeCert ()).pts 1080 3 1

end CFSG.HardMathSupport.Solomon.Coordinator
