module

public import CFSG.Alternating.Multipliers.Small

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers
open scoped commutatorElement

theorem card_ker_dvd_two_of_a6 {P : Type} [Group P]
    (hP : Group.IsPerfect P) {π : P →* alternatingGroup (Fin 6)} (hs : Function.Surjective π)
    (hk : π.ker ≤ center P) (h2 : IsPGroup 2 π.ker) : Nat.card π.ker ∣ 2 := by
  have h := Subgroup.card_map_dvd (hopfMultiplier (alternatingGroup (Fin 6))) (hopfLift π hs hk)
  rw [map_hopfMultiplier_hopfLift π hs hk, hopfMultiplier_alternatingGroup_six.2] at h
  have : Finite π.ker := Nat.finite_of_card_ne_zero (by intro h0; rw [h0] at h; simp at h)
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  rw [hn] at h ⊢
  have hn1 : n ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h4 : 4 ∣ 2 ^ n := by
      have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 hlt
      simpa using this
    have := h4.trans h
    omega
  interval_cases n <;> simp

section Swapped

variable {Γ : Type*} [Group Γ] [Finite Γ]

@[expose] def diagMap (t : Γ) (K : Subgroup Γ)
    (hc : ∀ x ∈ K, ∀ y ∈ K, x * (t * y * t⁻¹) = (t * y * t⁻¹) * x) : ↥K →* Γ :=
  MonoidHom.mk' (fun k => (k : Γ) * (t * k * t⁻¹)) (by
    intro k k'
    have h := hc k' k'.2 k k.2
    simp only [Subgroup.coe_mul]
    calc (k : Γ) * k' * (t * ((k : Γ) * k') * t⁻¹)
        = k * (k' * (t * k * t⁻¹)) * (t * k' * t⁻¹) := by group
      _ = k * ((t * k * t⁻¹) * k') * (t * k' * t⁻¹) := by rw [h]
      _ = _ := by group)

end Swapped

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
