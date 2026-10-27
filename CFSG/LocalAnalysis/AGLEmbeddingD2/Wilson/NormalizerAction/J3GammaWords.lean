module

public import Certificates.Data.CoverCenterThreeJ3
public import CFSG.Quasithin.Background.C48SporCoverStab

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.CosetTable CFSG.Quasithin.C48Cover

@[expose] def zw : List (Fin 6 × Bool) := [(5, true), (1, true), (5, false), (1, false)]

@[expose] def powW (i : Fin 6) (n : ℕ) : List (Fin 6 × Bool) := List.replicate n (i, true)

@[expose] def toWordB (a : Fin 4 → ZMod 3) : List (Fin 6 × Bool) :=
  powW 3 (a 0).val ++ powW 4 (a 1).val ++ powW 5 (a 2).val ++ (List.replicate (a 3).val zw).flatten

@[expose] def allVecs : List (Fin 4 → ZMod 3) :=
  (List.range 3).flatMap fun a0 => (List.range 3).flatMap fun a1 =>
    (List.range 3).flatMap fun a2 => (List.range 3).map fun a3 =>
      ![(a0 : ZMod 3), a1, a2, a3]

@[expose] def moveWords : List (List (Fin 6 × Bool)) :=
  (allVecs.filter fun a => decide (a ≠ 0)).map toWordB

@[expose] def actMat : Fin 6 → Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  ![!![2, 0, 0, 0; 0, 0, 1, 0; 1, 1, 1, 0; 0, 0, 0, 1],
    !![1, 0, 0, 0; 2, 1, 0, 0; 2, 0, 1, 0; 1, 0, 2, 1],
    !![1, 0, 0, 0; 1, 1, 0, 0; 2, 0, 1, 0; 2, 2, 0, 1],
    1, 1, 1]

@[expose] def actWord (i : Fin 6) (j : Fin 3) : List (Fin 6 × Bool) :=
  [(i, true), (⟨3 + j.val, by omega⟩, true), (i, false)] ++
    invW (toWordB fun r => actMat i r j.castSucc)

@[expose] def eqWords : List (List (Fin 6 × Bool)) :=
  [powW 3 3, powW 4 3, powW 5 3,
    [(3, true), (4, true), (3, false), (4, false)],
    [(3, true), (5, true), (3, false), (5, false)],
    [(4, true), (5, true), (4, false), (5, false)],
    powW 1 9, powW 2 9, (List.replicate 3 zw).flatten] ++
  ((List.finRange 3).flatMap fun i => (List.finRange 3).map fun j => actWord ⟨i.val, by omega⟩ j)

@[expose] def GammaWordFacts : Prop :=
  (∀ u ∈ eqWords,
      PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ j3GammaWords.map FreeGroup.mk}
        (FreeGroup.mk u) = 1) ∧
    ∀ u ∈ moveWords,
      PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ j3GammaWords.map FreeGroup.mk}
        (FreeGroup.mk u) ≠ 1

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
