module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataConjugation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public section

open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

variable {F : Type} [Field F] {d : ℕ}

theorem exists_det_neg_one_of_swap (Q₀ : QuadraticForm F (Fin d → F)) {a b : Fin d} (hab : a ≠ b)
    (hQ : ∀ v : Fin d → F, Q₀ (v ∘ Equiv.swap a b) = Q₀ v) :
    ∃ g : matrixIsometries Q₀,
      ((Matrix.GeneralLinearGroup.det (g : GL (Fin d) F) : Fˣ) : F) = -1 := by
  classical
  set σ : Equiv.Perm (Fin d) := Equiv.swap a b with hσ
  have hmul : (σ.permMatrix F) * (σ.permMatrix F) = 1 := by
    rw [← Matrix.permMatrix_mul, hσ, Equiv.swap_mul_self, Matrix.permMatrix_one]
  let P : GL (Fin d) F := ⟨σ.permMatrix F, σ.permMatrix F, hmul, hmul⟩
  refine ⟨⟨P, ?_⟩, ?_⟩
  · rw [mem_matrixIsometries_iff]
    intro v
    rw [matrixLinearEquiv_apply]
    change Q₀ (σ.permMatrix F *ᵥ v) = Q₀ v
    rw [Matrix.permMatrix_mulVec]
    exact hQ v
  · change Matrix.det (σ.permMatrix F) = -1
    rw [Matrix.det_permutation, hσ, Equiv.Perm.sign_swap hab]
    simp

section Forms

variable (n : ℕ)

theorem coordinateQuadOdd_swap (hn : 1 ≤ n) (v : Fin (2 * n + 1) → F) :
    coordinateQuadOdd n F (v ∘ Equiv.swap (oddIndexEquiv n (.inl ⟨0, hn⟩))
      (oddIndexEquiv n (.inr (.inl ⟨0, hn⟩)))) = coordinateQuadOdd n F v := by
  rw [coordinateQuadOdd_apply, coordinateQuadOdd_apply]
  have hsw : ∀ z, Equiv.swap (oddIndexEquiv n (.inl ⟨0, hn⟩))
      (oddIndexEquiv n (.inr (.inl ⟨0, hn⟩))) (oddIndexEquiv n z) =
      oddIndexEquiv n (Equiv.swap (Sum.inl ⟨0, hn⟩ : Fin n ⊕ Fin n ⊕ Unit)
        (Sum.inr (Sum.inl ⟨0, hn⟩)) z) := fun z => (oddIndexEquiv n).injective.swap_apply _ _ _
  simp only [Function.comp_apply, hsw]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      simp [mul_comm]
    · have h1 : (Sum.inl i : Fin n ⊕ Fin n ⊕ Unit) ≠ .inl ⟨0, hn⟩ := by simpa using hi
      have h2 : (Sum.inr (Sum.inl i) : Fin n ⊕ Fin n ⊕ Unit) ≠ .inr (.inl ⟨0, hn⟩) := by
        simpa using hi
      rw [Equiv.swap_apply_of_ne_of_ne h1 (by simp),
        Equiv.swap_apply_of_ne_of_ne (by simp) h2]

theorem coordinateQuadPlus_swap (hn : 1 ≤ n) (v : Fin (2 * n) → F) :
    coordinateQuadPlus n F (v ∘ Equiv.swap (plusIndexEquiv n (.inl ⟨0, hn⟩))
      (plusIndexEquiv n (.inr ⟨0, hn⟩))) = coordinateQuadPlus n F v := by
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply]
  have hsw : ∀ z, Equiv.swap (plusIndexEquiv n (.inl ⟨0, hn⟩))
      (plusIndexEquiv n (.inr ⟨0, hn⟩)) (plusIndexEquiv n z) =
      plusIndexEquiv n (Equiv.swap (Sum.inl ⟨0, hn⟩ : Fin n ⊕ Fin n)
        (Sum.inr ⟨0, hn⟩) z) := fun z => (plusIndexEquiv n).injective.swap_apply _ _ _
  simp only [Function.comp_apply, hsw]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = ⟨0, hn⟩
  · subst hi
    simp [mul_comm]
  · have h1 : (Sum.inl i : Fin n ⊕ Fin n) ≠ .inl ⟨0, hn⟩ := by simpa using hi
    have h2 : (Sum.inr i : Fin n ⊕ Fin n) ≠ .inr ⟨0, hn⟩ := by simpa using hi
    rw [Equiv.swap_apply_of_ne_of_ne h1 (by simp), Equiv.swap_apply_of_ne_of_ne (by simp) h2]

theorem coordinateQuadMinus_swap (hn : 1 ≤ n) (hn1 : 0 < n - 1) (b c : F) (v : Fin (2 * n) → F) :
    coordinateQuadMinus n F hn b c (v ∘ Equiv.swap (minusIndexEquiv n hn (.inl ⟨0, hn1⟩))
      (minusIndexEquiv n hn (.inr (.inl ⟨0, hn1⟩)))) = coordinateQuadMinus n F hn b c v := by
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  have hsw : ∀ z, Equiv.swap (minusIndexEquiv n hn (.inl ⟨0, hn1⟩))
      (minusIndexEquiv n hn (.inr (.inl ⟨0, hn1⟩))) (minusIndexEquiv n hn z) =
      minusIndexEquiv n hn (Equiv.swap (Sum.inl ⟨0, hn1⟩ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Sum.inr (Sum.inl ⟨0, hn1⟩)) z) := fun z =>
    (minusIndexEquiv n hn).injective.swap_apply _ _ _
  simp only [Function.comp_apply, hsw]
  have hs : ∑ i : Fin (n - 1), v (Equiv.swap (minusIndexEquiv n hn (.inl ⟨0, hn1⟩))
      (minusIndexEquiv n hn (.inr (.inl ⟨0, hn1⟩))) (minusIndexEquiv n hn (.inl i))) *
      v (Equiv.swap (minusIndexEquiv n hn (.inl ⟨0, hn1⟩))
      (minusIndexEquiv n hn (.inr (.inl ⟨0, hn1⟩))) (minusIndexEquiv n hn (.inr (.inl i)))) =
      ∑ i : Fin (n - 1), v (minusIndexEquiv n hn (.inl i)) *
        v (minusIndexEquiv n hn (.inr (.inl i))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsw, hsw]
    by_cases hi : i = ⟨0, hn1⟩
    · subst hi
      simp [mul_comm]
    · have h1 : (Sum.inl i : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) ≠ .inl ⟨0, hn1⟩ := by
        simpa using hi
      have h2 : (Sum.inr (Sum.inl i) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) ≠
          .inr (.inl ⟨0, hn1⟩) := by simpa using hi
      rw [Equiv.swap_apply_of_ne_of_ne h1 (by simp),
        Equiv.swap_apply_of_ne_of_ne (by simp) h2]
  rw [← hs]
  simp only [hsw]
  rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp),
    Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)]

end Forms

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
