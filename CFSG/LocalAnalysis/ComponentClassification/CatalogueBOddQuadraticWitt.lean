module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOddQuadratic

open QuadraticMap TauCeti

variable {K : Type*} [Field K]

@[expose] def hyperbolicPairForm (K : Type*) [Field K] : QuadraticForm K (K × K) :=
  linMulLin (LinearMap.fst K K K) (LinearMap.snd K K K)

theorem hyperbolicPairForm_apply (x : K × K) : hyperbolicPairForm K x = x.1 * x.2 := rfl

@[expose] def hyperbolicSumForm (K : Type*) [Field K] (m : ℕ) :
    QuadraticForm K (Fin m → K × K) :=
  QuadraticMap.pi fun _ : Fin m => hyperbolicPairForm K

theorem hyperbolicSumForm_apply (m : ℕ) (x : Fin m → K × K) :
    hyperbolicSumForm K m x = ∑ i, (x i).1 * (x i).2 := by
  simp [hyperbolicSumForm, hyperbolicPairForm_apply]

section TwoInvertible

variable [Invertible (2 : K)]

@[expose] def hyperbolicPlanePairEquiv :
    (hyperbolicPlane K).IsometryEquiv (hyperbolicPairForm K) where
  toLinearEquiv :=
    { toFun := fun x => (x 0 + x 1, x 0 - x 1)
      invFun := fun x => ![(x.1 + x.2) * ⅟(2 : K), (x.1 - x.2) * ⅟(2 : K)]
      left_inv := by
        intro x
        have h2 : (2 : K) * ⅟(2 : K) = 1 := mul_invOf_self 2
        funext i
        fin_cases i
        · change (x 0 + x 1 + (x 0 - x 1)) * ⅟(2 : K) = x 0
          linear_combination x 0 * h2
        · change (x 0 + x 1 - (x 0 - x 1)) * ⅟(2 : K) = x 1
          linear_combination x 1 * h2
      right_inv := by
        intro x
        have h2 : (2 : K) * ⅟(2 : K) = 1 := mul_invOf_self 2
        apply Prod.ext
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linear_combination x.1 * h2
        · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
          linear_combination x.2 * h2
      map_add' := by
        intro x y
        apply Prod.ext <;> simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add] <;> ring
      map_smul' := by
        intro a x
        apply Prod.ext <;> simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul, RingHom.id_apply] <;> ring }
  map_app' x := by
    change (x 0 + x 1) * (x 0 - x 1) = hyperbolicPlane K x
    rw [hyperbolicPlane_apply]
    ring

theorem hyperbolicPlanePairEquiv_apply (x : Fin 2 → K) :
    hyperbolicPlanePairEquiv x = (x 0 + x 1, x 0 - x 1) := rfl

theorem hyperbolicPlanePairEquiv_symm_apply (x : K × K) :
    hyperbolicPlanePairEquiv.symm x =
      ![(x.1 + x.2) * ⅟(2 : K), (x.1 - x.2) * ⅟(2 : K)] := rfl

private def hyperbolicSumSuccEquiv (m : ℕ) :
    ((hyperbolicPairForm K).prod (hyperbolicSumForm K m)).IsometryEquiv
      (hyperbolicSumForm K (m + 1)) where
  toLinearEquiv := Fin.consLinearEquiv K fun _ : Fin (m + 1) => K × K
  map_app' x := by
    change hyperbolicSumForm K (m + 1) (Fin.cons x.1 x.2) = _
    rw [hyperbolicSumForm_apply, Fin.sum_univ_succ, QuadraticMap.prod_apply,
      hyperbolicPairForm_apply, hyperbolicSumForm_apply]
    simp

def hyperbolicPresentationEquiv : (m : ℕ) →
    (presentedForm (hyperbolicPresentation K m)).IsometryEquiv (hyperbolicSumForm K m)
  | 0 => by
    have hclass : Quotient.mk (regularFormSetoid K) (hyperbolicPresentation K 0) =
        Quotient.mk (regularFormSetoid K) ⟨0, Fin.elim0⟩ := by
      rw [mk_hyperbolicPresentation, zero_nsmul, RegularFormClass.zero_def]
    let e := Classical.choice (RegularFormClass.mk_eq_mk_iff.mp hclass)
    refine e.trans { toLinearEquiv := ?_, map_app' := ?_ }
    · exact
        { toFun := fun _ => 0
          invFun := fun _ => 0
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _
          map_add' := fun _ _ => by simp
          map_smul' := fun _ _ => by simp }
    · intro x
      rw [Subsingleton.elim x 0]
      exact (QuadraticMap.map_zero _).trans (QuadraticMap.map_zero _).symm
  | m + 1 => by
    have hclass : Quotient.mk (regularFormSetoid K) (hyperbolicPresentation K (m + 1)) =
        Quotient.mk (regularFormSetoid K)
          (RegularFormPresentation.append ⟨2, ![1, -1]⟩ (hyperbolicPresentation K m)) := by
      rw [← RegularFormClass.mk_add_mk, mk_hyperbolicPresentation,
        mk_hyperbolicPresentation, ← hyperbolicClass_def, succ_nsmul']
    let e := Classical.choice (RegularFormClass.mk_eq_mk_iff.mp hclass)
    have eplane : (presentedForm (⟨2, ![1, -1]⟩ : RegularFormPresentation K)).IsometryEquiv
        (hyperbolicPairForm K) := by
      rw [presentedForm_one_neg_one]
      exact hyperbolicPlanePairEquiv
    exact e.trans
      ((presentedFormAppendIsometryEquiv ⟨2, ![1, -1]⟩ (hyperbolicPresentation K m)).trans
        ((eplane.prod (hyperbolicPresentationEquiv m)).trans (hyperbolicSumSuccEquiv m)))

end TwoInvertible

variable [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_hyperbolic_decomposition (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) :
    ∃ (m k : ℕ) (w : Fin k → Kˣ),
      k ≤ 2 ∧ (weightedSumSquares K w).Anisotropic ∧
      Module.finrank K V = 2 * m + k ∧
      Nonempty (Q.IsometryEquiv ((hyperbolicSumForm K m).prod (weightedSumSquares K w))) := by
  let : Invertible (2 : K) := invertibleOfNonzero (two_ne_zero_of_odd_card hodd)
  have hnd : Q.Nondegenerate := nondegenerate_polar_iff.mp hQ
  obtain ⟨p, hani, hrank, ⟨e⟩⟩ := Q.exists_equivalent_hyperbolicPresentation_prod hnd
  have hk : p.1 ≤ 2 := by
    have hndp := nondegenerate_presentedForm p
    have hbound := anisotropic_finrank_le_two hodd (presentedForm p)
      (nondegenerate_polar_iff.mpr hndp) hani
    simpa using hbound
  refine ⟨RegularFormClass.wittIndex (formClass Q hnd), p.1, p.2, hk, ?_, hrank, ?_⟩
  · rwa [presentedForm_eq_weightedSumSquares] at hani
  · refine ⟨e.trans ((hyperbolicPresentationEquiv _).prod ?_)⟩
    rw [presentedForm_eq_weightedSumSquares]

end CFSG.ComponentClassification.CatalogueBOddQuadratic
