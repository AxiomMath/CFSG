module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.SectionRank.QTK

open Matrix
open scoped commutatorElement

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def unitOfCube (M : Matrix ι ι (ZMod 2)) (h : M * (M * M) = 1) : GL ι (ZMod 2) :=
  ⟨M, M * M, h, (mul_assoc M M M).trans h⟩

@[expose] def unitOfSq (M : Matrix ι ι (ZMod 2)) (h : M * M = 1) : GL ι (ZMod 2) :=
  ⟨M, M, h, h⟩

@[expose] def encPlus : Fin 4 ⊕ Fin 4 → Fin 8 := Sum.elim ![0, 1, 2, 3] ![4, 5, 6, 7]

@[expose] def matPlus (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  M.submatrix encPlus encPlus

@[expose] def pLg₁ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfCube (matPlus
    !![0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 1, 0, 0, 1, 0, 0, 0;
       1, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pRg₁ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfCube (matPlus
    !![0, 1, 0, 0, 0, 0, 0, 0;
       1, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 1, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pLs₁ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 1, 0, 0;
       0, 1, 0, 0, 1, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pRs₁ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       1, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 1, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pLg₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfCube (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 1, 0, 0, 1, 0;
       0, 0, 1, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pRg₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfCube (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 1, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 1;
       0, 0, 0, 0, 0, 0, 1, 0]) (by decide +kernel)

@[expose] def pLs₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 1;
       0, 0, 0, 1, 0, 0, 1, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pRs₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 1, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 1;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pX₁₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 1, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 1, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def pX₂₀ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       1, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 1, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def plusZ₃ : Fin 3 → GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ![pLg₁, pLg₂, pRg₂]

@[expose] def plusA₃ : Fin 3 → GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ![pLs₁, pLs₂, pRs₂]

theorem plus₃_relations :
    (∀ i, plusZ₃ i ^ 3 = 1) ∧ (∀ i, plusZ₃ i * plusA₃ i ≠ plusA₃ i * plusZ₃ i) ∧
      (∀ i, plusZ₃ i ^ 2 * plusA₃ i ≠ plusA₃ i * plusZ₃ i ^ 2) ∧
      (∀ i j, i ≠ j → plusZ₃ j * plusA₃ i = plusA₃ i * plusZ₃ j) ∧
      (∀ i j, i ≠ j → plusZ₃ i * plusZ₃ j = plusZ₃ j * plusZ₃ i) ∧
      (∀ i, ⁅plusA₃ i, plusZ₃ i⁆ = plusZ₃ i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem plus_involution :
    ⁅pX₁₂, pX₂₀⁆ = pRs₁ ∧ pRs₁ ^ 2 = 1 ∧ pRs₁ * pRg₁ ≠ pRg₁ * pRs₁ ∧
      ∀ i, plusZ₃ i * pRs₁ = pRs₁ * plusZ₃ i := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

@[expose] def PlusBasisIsom (M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) : Prop :=
  (∀ i, CFSG.Assembly.LowTwoRank.StatedQuadPlus 4 (ZMod 2) (M *ᵥ Pi.single i 1) =
      CFSG.Assembly.LowTwoRank.StatedQuadPlus 4 (ZMod 2) (Pi.single i 1)) ∧
    ∀ i j, CFSG.Assembly.LowTwoRank.StatedQuadPlus 4 (ZMod 2)
        (M *ᵥ (Pi.single i 1 + Pi.single j 1)) =
      CFSG.Assembly.LowTwoRank.StatedQuadPlus 4 (ZMod 2) (Pi.single i 1 + Pi.single j 1)

theorem plus_basisIsom :
    (∀ i, PlusBasisIsom (plusZ₃ i : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))) ∧
      (∀ i, PlusBasisIsom (plusA₃ i : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))) ∧
      PlusBasisIsom (pX₁₂ : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) ∧
      PlusBasisIsom (pX₂₀ : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) := by
  unfold PlusBasisIsom
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.SectionRank.QTK
