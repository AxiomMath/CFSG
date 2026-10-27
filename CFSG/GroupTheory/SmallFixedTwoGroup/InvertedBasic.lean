module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {G : Type*} [Group G]

theorem apply_apply_of_mul_self_eq_one {θ : MulAut G} (hθ : θ * θ = 1) (x : G) : θ (θ x) = x := by
  rw [← MulAut.mul_apply, hθ, MulAut.one_apply]

theorem apply_twist_eq_inv {θ : MulAut G} (hθ : θ * θ = 1) (x : G) :
    θ (x⁻¹ * θ x) = (x⁻¹ * θ x)⁻¹ := by
  rw [map_mul, map_inv, apply_apply_of_mul_self_eq_one hθ, mul_inv_rev, inv_inv]

theorem twist_eq_twist_iff {θ : MulAut G} (x y : G) :
    x⁻¹ * θ x = y⁻¹ * θ y ↔ θ (x * y⁻¹) = x * y⁻¹ := by
  rw [map_mul, map_inv]
  constructor
  · intro h
    calc θ x * (θ y)⁻¹ = x * (x⁻¹ * θ x) * (θ y)⁻¹ := by group
      _ = x * (y⁻¹ * θ y) * (θ y)⁻¹ := by rw [h]
      _ = x * y⁻¹ := by group
  · intro h
    calc x⁻¹ * θ x = x⁻¹ * (θ x * (θ y)⁻¹) * θ y := by group
      _ = x⁻¹ * (x * y⁻¹) * θ y := by rw [h]
      _ = y⁻¹ * θ y := by group

theorem inverted_mul_iff_commute {θ : MulAut G} {x y : G} (hx : θ x = x⁻¹) (hy : θ y = y⁻¹) :
    θ (x * y) = (x * y)⁻¹ ↔ x * y = y * x := by
  rw [map_mul, hx, hy]
  constructor
  · intro h
    have h' := congrArg Inv.inv h
    simp only [mul_inv_rev, inv_inv] at h'
    exact h'.symm
  · intro h
    rw [h, mul_inv_rev]

theorem mul_comm_of_apply_eq_inv {θ : MulAut G} {R : Subgroup G} (hR : ∀ r ∈ R, θ r = r⁻¹) :
    ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
  (inverted_mul_iff_commute (hR a ha) (hR b hb)).1 (hR (a * b) (R.mul_mem ha hb))

theorem card_le_card_fixedSubgroup_mul_card_inverted [Finite G] {θ : MulAut G}
    (hθ : θ * θ = 1) :
    Nat.card G ≤ Nat.card (fixedSubgroup θ) * Nat.card {g : G // θ g = g⁻¹} := by
  let Y := fixedSubgroup θ
  have hY : ∀ x : G, x ∈ Y ↔ θ x = x := fun x => by simp [Y, fixedSubgroup]
  let F : Quotient (QuotientGroup.rightRel Y) → {g : G // θ g = g⁻¹} :=
    Quotient.lift (fun x => ⟨x⁻¹ * θ x, apply_twist_eq_inv hθ x⟩) fun a b hab =>
      Subtype.ext (((twist_eq_twist_iff b a).2
        ((hY (b * a⁻¹)).1 (QuotientGroup.rightRel_apply.1 hab))).symm)
  have hFinj : Function.Injective F := by
    rintro ⟨a⟩ ⟨b⟩ h
    have h' : a⁻¹ * θ a = b⁻¹ * θ b := congrArg Subtype.val h
    have hfixr : θ (a * b⁻¹) = a * b⁻¹ := (twist_eq_twist_iff a b).1 h'
    have hmem : a * b⁻¹ ∈ Y := (hY (a * b⁻¹)).2 hfixr
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    simpa only [mul_inv_rev, inv_inv] using Y.inv_mem hmem
  have hle : Y.index ≤ Nat.card {g : G // θ g = g⁻¹} := by
    have hcard : Y.index = Nat.card (Quotient (QuotientGroup.rightRel Y)) := by
      rw [Subgroup.index]
      exact (Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Y)).symm
    have hle' := Nat.card_le_card_of_injective F hFinj
    simpa [hcard] using hle'
  calc Nat.card G = Y.index * Nat.card Y := (Subgroup.index_mul_card Y).symm
    _ ≤ Nat.card {g : G // θ g = g⁻¹} * Nat.card Y := Nat.mul_le_mul_right _ hle
    _ = Nat.card Y * Nat.card {g : G // θ g = g⁻¹} := by rw [mul_comm]

theorem inverted_of_invariant_of_fixed_eq_one [Finite G] {θ : MulAut G} (hθ : θ * θ = 1)
    {R : Subgroup G} (hR : ∀ r ∈ R, θ r ∈ R) (hfix : ∀ r ∈ R, θ r = r → r = 1) :
    ∀ r ∈ R, θ r = r⁻¹ := by
  haveI : Finite R := Finite.of_injective (fun r : R => (r : G)) Subtype.val_injective
  let f : R → R := fun r => ⟨(r : G)⁻¹ * θ r, R.mul_mem (R.inv_mem r.2) (hR r r.2)⟩
  have hfinj : Function.Injective f := by
    intro r s h
    have h' : (r : G)⁻¹ * θ r = (s : G)⁻¹ * θ s := congrArg Subtype.val h
    have hfixr : θ ((r : G) * (s : G)⁻¹) = (r : G) * (s : G)⁻¹ :=
      (twist_eq_twist_iff (r : G) (s : G)).1 h'
    have hmem : (r : G) * (s : G)⁻¹ ∈ R := R.mul_mem r.2 (R.inv_mem s.2)
    have h1 : (r : G) * (s : G)⁻¹ = 1 := hfix _ hmem hfixr
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
  intro r hr
  obtain ⟨s, hs⟩ := hsurj ⟨r, hr⟩
  have hval : (r : G) = (s : G)⁻¹ * θ s := (congrArg Subtype.val hs).symm
  rw [hval, apply_twist_eq_inv hθ]

end CFSG.GroupTheory.SmallFixedTwoGroup
