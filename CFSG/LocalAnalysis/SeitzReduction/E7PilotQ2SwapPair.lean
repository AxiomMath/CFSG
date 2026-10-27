module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotSwapUnique
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


variable {K : Type} [Field K]

theorem le_factorization_card_fixedSubgroup_E7_two (hK : Nat.card K = 2)
    {θ : MulAut (adjointGroup .E7 K)} (hθ : θ * θ = 1) (hθ1 : θ ≠ 1) :
    33 ≤ (Nat.card (fixedSubgroup θ)).factorization 2 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK'
  have : Finite (adjointGroup .E7 K) := by
    have : Finite (ModGL Tag.E7 K) := finite_modGL
    infer_instance
  obtain ⟨w, rfl⟩ := E8Pilot.forall_mem_range_conj_E7_E8_two (Or.inl rfl) hK θ
  have hZ := center_adjointGroup_eq_bot_field .E7 K
  have hw2 : w * w = 1 := by
    have h1 : MulAut.conj (w * w) = 1 := by rw [map_mul]; exact hθ
    have hc : w * w ∈ center (adjointGroup .E7 K) := by
      rw [mem_center_iff]
      intro g
      have h2 : w * w * g * (w * w)⁻¹ = g := by
        have := congrArg (fun φ : MulAut (adjointGroup .E7 K) => φ g) h1
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * (w * w) = w * w * g * (w * w)⁻¹ * (w * w) := by rw [h2]
        _ = w * w * g := by group
    rw [hZ, mem_bot] at hc
    exact hc
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hθ1 (map_one _)
  have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  have hdvd := two_pow_dvd_card_centralizer_E7 hK' hwo
  rw [mul_one] at hdvd
  change 33 ≤ (Nat.card (fixedSubgroup (MulAut.conj w))).factorization 2
  rw [E8Pilot.fixedSubgroup_conj_eq_centralizer]
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd

theorem factorization_two_mul_card_mulAut_E7_two_le (hK : Nat.card K = 2) :
    (2 * Nat.card (MulAut (adjointGroup .E7 K))).factorization 2 ≤ 64 := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .E7 K) := by
    have : Finite (ModGL Tag.E7 K) := finite_modGL
    infer_instance
  have h2 := SwapUnique.card_mulAut_adjointGroup_E7_dvd hK'
  rw [mul_one] at h2
  have hC0 : Nat.card (adjointGroup .E7 K) ≠ 0 := Nat.card_pos.ne'
  have h4 : 2 * Nat.card (MulAut (adjointGroup .E7 K)) ∣ 2 * Nat.card (adjointGroup .E7 K) :=
    Nat.mul_dvd_mul_left 2 h2
  have hA0 : 2 * Nat.card (MulAut (adjointGroup .E7 K)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero fun h0 => ?_
    have : Finite (MulAut (adjointGroup .E7 K)) := inferInstance
    exact Nat.card_pos.ne' h0
  have h5 := (Nat.factorization_le_iff_dvd hA0 (mul_ne_zero two_ne_zero hC0)).2 h4 2
  rw [Nat.factorization_mul two_ne_zero hC0, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, E6Pilot.factorization_card_adjointGroup hK',
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_E7] at h5
  omega

theorem swapPairExclusion_adjointGroup_E7_two (hK : Nat.card K = 2) :
    SeitzQ2.SwapPairExclusion (adjointGroup .E7 K) := by
  intro θ θ' hθ hθ1 hθ' hθ'1 h2 _
  have h1 := le_factorization_card_fixedSubgroup_E7_two hK hθ hθ1
  have h1' := le_factorization_card_fixedSubgroup_E7_two hK hθ' hθ'1
  have hA := factorization_two_mul_card_mulAut_E7_two_le hK
  omega

end CFSG.SeitzReduction.E7Pilot
