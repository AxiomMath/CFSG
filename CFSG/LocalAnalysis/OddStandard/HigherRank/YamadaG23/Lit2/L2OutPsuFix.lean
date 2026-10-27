module

public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

theorem l2out_exists_fixed_even_sl2_card {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}
    (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 4 ≤ 2 * r + ε)
    (α : MulAut (hypPSU h r ε)) (hα : α ^ 2 = 1) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), ringChar k ≠ 2 ∧ p ^ f ≤ Nat.card k ∧
      ∃ ρ : SpecialLinearGroup (Fin 2) k →* hypPSU h r ε, Even (Nat.card ρ.range) ∧
        ∀ s ∈ ρ.range, α s = s := by
  have := h.finite
  have hk2 : ringChar h.fixedField ≠ 2 := ringChar_fixedField_ne_two h hp
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K p := h.charP
    rwa [ringChar.eq K p]
  have hsizeF : p ^ f ≤ Nat.card h.fixedField := h.card_fixedField.ge
  have hsizeK : p ^ f ≤ Nat.card K := by
    rw [h.card]
    exact Nat.pow_le_pow_right h.prime.pos (by omega)
  by_cases hα1 : α = 1
  · subst hα1
    obtain ⟨ψ, -, hψs⟩ := exists_comm_planeHom_of_norm_eq_one h hp (by omega)
      (one_mem (hypUnitary h r ε)) one_ne_zero (by simp) (by simp [UnitaryFieldData.norm])
    exact ⟨h.fixedField, inferInstance, inferInstance, hk2, hsizeF, (hypProj h r ε).comp ψ,
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
      exact ⟨h.fixedField, inferInstance, inferInstance, hk2, hsizeF, (hypProj h r ε).comp ψ,
        even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
        fixed_of_comm h hr hε hx ψ hψ⟩
    · obtain ⟨ψ, hψ, hψs⟩ := exists_comm_pairHom_of_norm_eq_neg_one h hp hn hA hl0 hAA' hN
      exact ⟨K, inferInstance, inferInstance, hK2, hsizeK, (hypProj h r ε).comp ψ,
        even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
        fixed_of_comm h hr hε hx ψ hψ⟩
  ·
    obtain ⟨c, hc, hAA⟩ := hbar hσ
    obtain ⟨ψ, hψ, hψs⟩ := exists_comm_conj_of_bar h hp hn hA hc hAA
    exact ⟨h.fixedField, inferInstance, inferInstance, hk2, hsizeF, (hypProj h r ε).comp ψ,
      even_card_range_hypProj_comp ψ (QuaternionMatrices.slQuatI_pow_four) hψs,
      fixed_of_comm_bar h hr hε hσ hx ψ hψ⟩

end CFSG.OddStandard.HigherRank.YamadaG23
