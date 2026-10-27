module

public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowConj

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient
  onCenterQuotient_apply_mk)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem fixed_of_comm (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {A : GL (HypIndex r ε) K}
    (hx : (⟨A, RingEquiv.refl K⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε)
    {H : Type*} [Group H] (ψ : H →* hypSU h r ε)
    (hψ : ∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) :
    ∀ s ∈ ((hypProj h r ε).comp ψ).range, semilinearAutHom h hr hε ⟨_, hx⟩ s = s := by
  rintro _ ⟨x, rfl⟩
  refine semilinearAutHom_hypProj_of_mul_eq h hr hε hx (ψ x) ?_
  rw [glAut_refl]
  exact Units.ext (hψ x)

theorem fixed_of_comm_bar (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {A : GL (HypIndex r ε) K} {σ : K ≃+* K} (hσ : ∀ c, σ c = h.bar c)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε)
    {H : Type*} [Group H] (ψ : H →* hypSU h r ε)
    (hψ : ∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) :
    ∀ s ∈ ((hypProj h r ε).comp ψ).range, semilinearAutHom h hr hε ⟨_, hx⟩ s = s := by
  rintro _ ⟨x, rfl⟩
  refine semilinearAutHom_hypProj_of_mul_eq h hr hε hx (ψ x) (Units.ext ?_)
  rw [Units.val_mul, Units.val_mul, coe_glAut_of_bar h hσ]
  exact hψ x

theorem exists_fixed_even_sl2 (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 4 ≤ 2 * r + ε) (α : MulAut (hypPSU h r ε)) (hα : α ^ 2 = 1) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), ringChar k ≠ 2 ∧
      ∃ ρ : SpecialLinearGroup (Fin 2) k →* hypPSU h r ε, Even (Nat.card ρ.range) ∧
        ∀ s ∈ ρ.range, α s = s := by
  have := h.finite
  have hk2 : ringChar h.fixedField ≠ 2 := ringChar_fixedField_ne_two h hp
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K p := h.charP
    rwa [ringChar.eq K p]
  by_cases hα1 : α = 1
  · subst hα1
    obtain ⟨ψ, -, hψs⟩ := exists_comm_planeHom_of_norm_eq_one h hp (by omega)
      (one_mem (hypUnitary h r ε)) one_ne_zero (by simp) (by simp [UnitaryFieldData.norm])
    exact ⟨h.fixedField, inferInstance, inferInstance, hk2, (hypProj h r ε).comp ψ,
      even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
      fun s _ => rfl⟩
  have hα2 : orderOf α = 2 := orderOf_eq_prime hα hα1
  obtain ⟨A, σ, hx, hA, hαeq, hσ, hrefl, hbar⟩ :=
    (odd_unitary_automorphism_semilinear_representation h hp hr hε (by omega)).2.2.2 α hα2
  subst hαeq
  rcases hσ with rfl | hσ
  ·
    have hord := hrefl rfl
    have hsq : (QuotientGroup.mk (⟨A, hA⟩ * ⟨A, hA⟩) : hypUnitaryMod h r ε) = 1 := by
      rw [QuotientGroup.mk_mul, ← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
    obtain ⟨d, hd, -, hAA⟩ := mem_normOneScalars.mp ((QuotientGroup.eq_one_iff _).mp hsq)
    obtain ⟨l, hl0, hld⟩ := exists_sq_eq_of_norm_eq_one h hp hd
    have hAA' : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * A = (l ^ 2) • 1 := by
      have h1 := congrArg (fun g : GL (HypIndex r ε) K =>
        (g : Matrix (HypIndex r ε) (HypIndex r ε) K)) hAA
      simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
      rw [h1, hld, scalar_apply, smul_one_eq_diagonal]
    have hN : h.norm l = 1 ∨ h.norm l = -1 := by
      have h1 : h.norm l * h.norm l = 1 := by
        rw [← norm_mul_eq h, ← pow_two, hld, hd]
      exact mul_self_eq_one_iff.mp h1
    rcases hN with hN | hN
    · obtain ⟨ψ, hψ, hψs⟩ := exists_comm_planeHom_of_norm_eq_one h hp (by omega) hA hl0 hAA' hN
      exact ⟨h.fixedField, inferInstance, inferInstance, hk2, (hypProj h r ε).comp ψ,
        even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
        fixed_of_comm h hr hε hx ψ hψ⟩
    · obtain ⟨ψ, hψ, hψs⟩ := exists_comm_pairHom_of_norm_eq_neg_one h hp hn hA hl0 hAA' hN
      exact ⟨K, inferInstance, inferInstance, hK2, (hypProj h r ε).comp ψ,
        even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
        fixed_of_comm h hr hε hx ψ hψ⟩
  ·
    obtain ⟨c, hc, hAA⟩ := hbar hσ
    obtain ⟨ψ, hψ, hψs⟩ := exists_comm_conj_of_bar h hp hn hA hc hAA
    exact ⟨h.fixedField, inferInstance, inferInstance, hk2, (hypProj h r ε).comp ψ,
      even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
      fixed_of_comm_bar h hr hε hσ hx ψ hψ⟩

end CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
