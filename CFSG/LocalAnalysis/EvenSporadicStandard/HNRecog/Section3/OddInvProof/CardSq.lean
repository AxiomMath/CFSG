module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem oddInv_card_le_sq {G : Type} [Group G] [Finite G] (T : Subgroup G) {a z : G}
    (ha : a ^ 2 = 1) (hz : z ^ 2 = 1) (hT : ∀ u ∈ T, a * u * a⁻¹ ∈ T)
    (hsq : ∀ u ∈ T, u ^ 2 = 1 ∨ u ^ 2 = z) (hne : ∀ u ∈ T, a * u * a⁻¹ ≠ u * z) :
    Nat.card ↥T ≤ Nat.card ↥(T ⊓ Gx a) ^ 2 := by
  have haa : a * a = 1 := by
    rw [← pow_two]
    exact ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hinv : ∀ u ∈ T, a * u * a⁻¹ = u⁻¹ → a * u = u * a := by
    intro u hu h1
    rcases hsq u hu with h2 | h2
    · have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h2)
      rw [hu'] at h1
      calc a * u = a * u * a⁻¹ * a := by group
        _ = u * a := by rw [h1]
    · exfalso
      apply hne u hu
      rw [h1]
      have huu : u * u = z := by
        rw [← pow_two]
        exact h2
      have hzz : z * z = 1 := by
        rw [← pow_two]
        exact hz
      calc u⁻¹ = u⁻¹ * (z * z) := by rw [hzz, mul_one]
        _ = u⁻¹ * (u * u * z) := by rw [huu]
        _ = u * z := by group
  have hψ : ∀ t ∈ T, t * a * t⁻¹ * a⁻¹ ∈ T ⊓ Gx a := by
    intro t ht
    have hT' : t * a * t⁻¹ * a⁻¹ ∈ T := by
      have h2 : t * (a * t⁻¹ * a⁻¹) ∈ T := T.mul_mem ht (hT t⁻¹ (T.inv_mem ht))
      simpa only [mul_assoc] using h2
    refine Subgroup.mem_inf.mpr ⟨hT', mem_Gx.mpr (hinv _ hT' ?_)⟩
    calc a * (t * a * t⁻¹ * a⁻¹) * a⁻¹ = a * t * a * t⁻¹ * (a⁻¹ * a⁻¹) := by group
      _ = a * t * a * t⁻¹ := by rw [hainv, haa, mul_one]
      _ = a * t * a⁻¹ * t⁻¹ := by rw [hainv]
      _ = (t * a * t⁻¹ * a⁻¹)⁻¹ := by group
  let H : Subgroup ↥T := (T ⊓ Gx a).subgroupOf T
  let ψ : ↥T → ↥(T ⊓ Gx a) := fun t => ⟨(t : G) * a * (t : G)⁻¹ * a⁻¹, hψ t t.2⟩
  have hψeq : ∀ t₁ t₂ : ↥T, ψ t₁ = ψ t₂ ↔ t₁⁻¹ * t₂ ∈ H := by
    intro t₁ t₂
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : (t₁ : G) * a * (t₁ : G)⁻¹ * a⁻¹ = (t₂ : G) * a * (t₂ : G)⁻¹ * a⁻¹ :=
        congrArg Subtype.val h
      have h2 : (t₁ : G) * a * (t₁ : G)⁻¹ = (t₂ : G) * a * (t₂ : G)⁻¹ := mul_right_cancel h1
      refine Subgroup.mem_inf.mpr ⟨(t₁⁻¹ * t₂).2, mem_Gx.mpr ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc a * ((t₁ : G)⁻¹ * t₂) = (t₁ : G)⁻¹ * ((t₁ : G) * a * (t₁ : G)⁻¹) * t₂ := by group
        _ = (t₁ : G)⁻¹ * ((t₂ : G) * a * (t₂ : G)⁻¹) * t₂ := by rw [h2]
        _ = (t₁ : G)⁻¹ * t₂ * a := by group
    · intro h
      have h1 : a * ((t₁ : G)⁻¹ * t₂) = (t₁ : G)⁻¹ * t₂ * a := by
        have h0 := mem_Gx.mp (Subgroup.mem_inf.mp h).2
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h0
      have h2 : (t₁ : G) * a * (t₁ : G)⁻¹ = (t₂ : G) * a * (t₂ : G)⁻¹ := by
        calc (t₁ : G) * a * (t₁ : G)⁻¹
            = (t₁ : G) * (a * ((t₁ : G)⁻¹ * t₂)) * (t₂ : G)⁻¹ := by group
          _ = (t₁ : G) * ((t₁ : G)⁻¹ * t₂ * a) * (t₂ : G)⁻¹ := by rw [h1]
          _ = (t₂ : G) * a * (t₂ : G)⁻¹ := by group
      apply Subtype.ext
      show (t₁ : G) * a * (t₁ : G)⁻¹ * a⁻¹ = (t₂ : G) * a * (t₂ : G)⁻¹ * a⁻¹
      rw [h2]
  let φ : ↥T ⧸ H → ↥(T ⊓ Gx a) := fun q =>
    Quotient.liftOn' q ψ (fun t₁ t₂ h => (hψeq t₁ t₂).mpr (QuotientGroup.leftRel_apply.mp h))
  have hφ : Function.Injective φ := by
    intro q₁ q₂ h
    obtain ⟨t₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨t₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    exact QuotientGroup.eq.mpr ((hψeq t₁ t₂).mp h)
  have h1 : Nat.card (↥T ⧸ H) ≤ Nat.card ↥(T ⊓ Gx a) := Nat.card_le_card_of_injective φ hφ
  have h2 : Nat.card ↥T = Nat.card (↥T ⧸ H) * Nat.card ↥H :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup H
  have h3 : Nat.card ↥H = Nat.card ↥(T ⊓ Gx a) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ Gx a ≤ T)).toEquiv
  rw [h2, h3, pow_two]
  exact Nat.mul_le_mul_right _ h1

end CFSG.EvenSporadicStandard.HNRecog.Section3
