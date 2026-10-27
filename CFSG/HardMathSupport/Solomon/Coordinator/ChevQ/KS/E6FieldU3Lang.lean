module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Model

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux OuterFourInAux

namespace U3Bridge

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.Burgoyne.U

theorem conj_uFieldAut_of_order_three {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)
    (a : MulAut (StatedProj (StatedSU 3 (2 ^ 3) K))) (ha : orderOf a = 3)
    (σ : K ≃+* K) (hσ : orderOf σ = 3)
    (hfac : uFactor h (by norm_num) (by norm_num) a = σ) :
    ∃ M : uU h 3, (uConjAut h (by norm_num) M)⁻¹ * a * uConjAut h (by norm_num) M =
      uFieldAut h (by norm_num) σ := by
  have hn : 3 ≤ 3 := le_refl 3
  have hq : ¬((3 : ℕ) = 3 ∧ 2 ^ 3 = 2) := by norm_num
  set E := MulAut.congr (uTransport h (by norm_num : 1 ≤ 3)) with hE
  set a' : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := E a with ha'
  have ha'3 : orderOf a' = 3 := by rw [ha', MulEquiv.orderOf_eq, ha]
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hn hq
      Nat.prime_three (by norm_num) a' ha'3 σ hfac hσ
  refine ⟨M, ?_⟩
  have h1 := congrArg E.symm hM
  rw [map_mul, map_mul, map_inv, ha', MulEquiv.symm_apply_apply] at h1
  exact h1

end U3Bridge

section Lang

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.Burgoyne.U

theorem uFactor_eq_one_iff_exists_uConjAut {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)
    (α : MulAut (StatedProj (StatedSU 3 (2 ^ 3) K))) :
    uFactor h (by norm_num) (by norm_num) α = 1 ↔
      ∃ A : uU h 3, α = uConjAut h (by norm_num) A := by
  constructor
  · intro h1
    obtain ⟨A, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h (by norm_num : 3 ≤ 3)
      (by norm_num) α
    rw [uFactor_apply] at h1
    subst h1
    exact ⟨A, by rw [map_one, mul_one]⟩
  · rintro ⟨A, rfl⟩
    have := uFactor_apply h (n := 3) (by norm_num) (by norm_num) A 1
    rw [map_one, mul_one] at this
    exact this

theorem fieldAutU_three_of_uFactor_ne_one {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)
    {S : Type} [Group S] (e : S ≃* StatedProj (StatedSU 3 (2 ^ 3) K)) {φ : MulAut S}
    (hφ3 : φ ^ 3 = 1)
    (hfac : uFactor h (by norm_num) (by norm_num) (MulAut.congr e φ) ≠ 1) :
    FieldAutU 3 S φ := by
  haveI := h.finite
  set a : MulAut (StatedProj (StatedSU 3 (2 ^ 3) K)) := MulAut.congr e φ with ha
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hφ3, map_one]
  have ha1 : a ≠ 1 := by
    intro h1
    apply hfac
    rw [h1, map_one]
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  set σ := uFactor h (by norm_num) (by norm_num) a with hσdef
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, ha3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hfac
  obtain ⟨M, hM⟩ := U3Bridge.conj_uFieldAut_of_order_three h a haord σ hσord rfl
  refine ⟨K, inferInstance, h.finite, e, σ, (uConjAut h (by norm_num) M)⁻¹, h.card, hfac,
    ?_, ?_⟩
  · rw [hσord]
    decide
  · rw [inv_inv, hM]
    exact U6Bridge.isEntrywiseProj_uFieldAut h (by norm_num) σ

end Lang

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
