module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53C

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem false_of_three_cycle {T : Subgroup G} (hT : IsPGroup 2 T) {c x z : G} (hc : c ∈ T)
    (h1 : c * z * c⁻¹ = x) (h2 : c * x * c⁻¹ = x * z) (h3 : c * (x * z) * c⁻¹ = z)
    (hxz : x ≠ z) (hx1 : x ≠ 1) : False := by
  obtain ⟨k, hk⟩ := hT ⟨c, hc⟩
  have hck : c ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hc3 : c ^ 3 * z * (c ^ 3)⁻¹ = z := by
    rw [show c ^ 3 = c * c * c by rw [pow_succ, pow_succ, pow_one]]
    rw [show c * c * c * z * (c * c * c)⁻¹ = c * (c * (c * z * c⁻¹) * c⁻¹) * c⁻¹ by group, h1,
      h2, h3]
  have hr : ∀ n : ℕ, c ^ n * z * (c ^ n)⁻¹ = c ^ (n % 3) * z * (c ^ (n % 3))⁻¹ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n 3 with hn | hn
      · rw [Nat.mod_eq_of_lt hn]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
        rw [show (m + 3) % 3 = m % 3 by omega, ← ih m (by omega), pow_add,
          show c ^ m * c ^ 3 * z * (c ^ m * c ^ 3)⁻¹ =
            c ^ m * (c ^ 3 * z * (c ^ 3)⁻¹) * (c ^ m)⁻¹ by group, hc3]
  have hmod : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    have h5 : ¬ 3 ∣ 2 ^ k := fun h6 => by
      have := Nat.prime_three.dvd_of_dvd_pow h6
      omega
    omega
  have h6 := hr (2 ^ k)
  rw [hck, one_mul, inv_one, mul_one] at h6
  rcases hmod with h7 | h7 <;> rw [h7] at h6
  · rw [pow_one, h1] at h6
    exact hxz h6.symm
  · rw [sq, show c * c * z * (c * c)⁻¹ = c * (c * z * c⁻¹) * c⁻¹ by group, h1, h2] at h6
    apply hx1
    calc x = x * z * z⁻¹ := by group
      _ = 1 := by rw [← h6, mul_inv_cancel]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem mem_coreActionKernel_footeF_conjugate {g x y : G} (hx : x ∈ conjugate Q g)
    (hy : y ∈ conjugate Q g) (hx2 : orderOf x = 2) (hxy : x * y = y * x) :
    y ∈ coreActionKernel (footeF L₀ x) := by
  have hv := mem_conjugate_iff.mp hx
  have hv' := mem_conjugate_iff.mp hy
  have hv2 : orderOf (g * x * g⁻¹) = 2 := by rw [orderOf_conj', hx2]
  have h1 : footeF L₀ x = conjugate (footeF L₀ (g * x * g⁻¹)) g := by
    rw [← footeF_conj h.sec4.huniq, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  rw [h1]
  refine mem_coreActionKernel_conjugate ?_
  refine h.mem_coreActionKernel_footeF_of_commute hv hv2 hv' ?_
  calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [hxy]
    _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

end Sec5

end CFSG.ComponentClassification.Foote5
