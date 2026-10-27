module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Layer

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup
open scoped commutatorElement

theorem comm_mod_central {H : Type*} [Group H] (Z : Subgroup H) [Z.Normal] (u : H) (S : Set H)
    (hu : ∀ c ∈ S, u * c * u⁻¹ * c⁻¹ ∈ Z) {k l c c' : H} {ε ε' : ℕ} (hk : k = u ^ ε * c)
    (hl : l = u ^ ε' * c') (hc : c ∈ S) (hc' : c' ∈ S) : ⁅c, c'⁆⁻¹ * ⁅k, l⁆ ∈ Z := by
  rw [← QuotientGroup.eq]
  let π : H →* H ⧸ Z := QuotientGroup.mk' Z
  have hcomm : ∀ x ∈ S, Commute (π u) (π x) := by
    intro x hx
    have h1 : π (u * x * u⁻¹ * x⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 (hu x hx)
    have h2 : ⁅π u, π x⁆ = 1 := by
      rw [commutatorElement_def]
      simpa [map_mul, map_inv] using h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  show π ⁅c, c'⁆ = π ⁅k, l⁆
  rw [map_commutatorElement, map_commutatorElement, hk, hl, map_mul, map_mul, map_pow, map_pow]
  rw [comm_mul_mul ((hcomm c hc).pow_left ε) ((hcomm c' hc').pow_left ε)
    ((hcomm c hc).pow_left ε') ((hcomm c' hc').pow_left ε')]
  have : ⁅(π u) ^ ε, (π u) ^ ε'⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (((Commute.refl (π u)).pow_pow ε ε').eq)
  rw [this, one_mul]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
