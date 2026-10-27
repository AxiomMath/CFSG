module

public import CFSG.LocalAnalysis.SectionRank.QTK.EvenPlus8M

public section

namespace CFSG.SectionRank.QTK

open Matrix
open scoped commutatorElement

@[expose] def encMinus : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → Fin 8 :=
  Sum.elim ![0, 1, 2] (Sum.elim ![3, 4, 5] ![6, 7])

@[expose] def matMinus (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  M.submatrix encMinus encMinus

@[expose] def mLg : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfCube (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 1, 0, 1, 0, 0, 0;
       0, 1, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mRg : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfCube (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 1, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 1, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mOm : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfCube (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 0, 0, 1, 1]) (by decide +kernel)

@[expose] def mLs : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 1, 0, 0;
       0, 0, 1, 0, 1, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mRs : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 1, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 1, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mCj : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 1;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mE₁ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 1, 0, 0, 0, 1;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 1, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mE₂ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 1, 0, 0, 1, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 1, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def mE₃ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) :=
  unitOfSq (matMinus
    !![1, 0, 0, 1, 0, 0, 1, 1;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 1, 0, 0, 1, 0;
       0, 0, 0, 1, 0, 0, 0, 1]) (by decide +kernel)

@[expose] def minusZ : Fin 3 → GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) := ![mLg, mRg, mOm]

@[expose] def minusA : Fin 3 → GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2) := ![mLs, mRs, mCj]

theorem minus_relations :
    (∀ i, minusZ i ^ 3 = 1) ∧ (∀ i, minusZ i * minusA i ≠ minusA i * minusZ i) ∧
      (∀ i, minusZ i ^ 2 * minusA i ≠ minusA i * minusZ i ^ 2) ∧
      (∀ i j, i ≠ j → minusZ j * minusA i = minusA i * minusZ j) ∧
      (∀ i j, i ≠ j → minusZ i * minusZ j = minusZ j * minusZ i) ∧
      (∀ i, ⁅minusA i, minusZ i⁆ = minusZ i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem minus_fourGroup :
    mE₁ ^ 2 = 1 ∧ mE₂ ^ 2 = 1 ∧ mE₁ * mE₂ = mE₂ * mE₁ ∧ ⁅mOm, mE₂⁆ = mE₁ ∧
      ⁅mOm, mE₃⁆ = mE₂ ∧ mE₁ * mOm ≠ mOm * mE₁ ∧ mOm * mE₁ * mOm⁻¹ = mE₂ ∧
      mOm * mE₂ * mOm⁻¹ = mE₁ * mE₂ ∧ mOm⁻¹ * mE₁ * mOm = mE₁ * mE₂ ∧
      mOm⁻¹ * mE₂ * mOm = mE₁ ∧ mLg * mE₁ = mE₁ * mLg ∧ mLg * mE₂ = mE₂ * mLg ∧
      mRg * mE₁ = mE₁ * mRg ∧ mRg * mE₂ = mE₂ * mRg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

@[expose] def MinusBasisIsom
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) : Prop :=
  (∀ i, CFSG.Assembly.LowTwoRank.StatedQuadMinus 4 (ZMod 2) 1 1 (M *ᵥ Pi.single i 1) =
      CFSG.Assembly.LowTwoRank.StatedQuadMinus 4 (ZMod 2) 1 1 (Pi.single i 1)) ∧
    ∀ i j, CFSG.Assembly.LowTwoRank.StatedQuadMinus 4 (ZMod 2) 1 1
        (M *ᵥ (Pi.single i 1 + Pi.single j 1)) =
      CFSG.Assembly.LowTwoRank.StatedQuadMinus 4 (ZMod 2) 1 1 (Pi.single i 1 + Pi.single j 1)

theorem minus_basisIsom :
    (∀ i, MinusBasisIsom
      (minusZ i : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2))) ∧
    (∀ i, MinusBasisIsom
      (minusA i : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2))) ∧
    MinusBasisIsom (mE₂ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) ∧
    MinusBasisIsom (mE₃ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) := by
  unfold MinusBasisIsom
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.SectionRank.QTK
