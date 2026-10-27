module

public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem relIndex_sup_zpowers_le_two {A : Subgroup G} {s : G} (hs : s * s = 1)
    (hsA : ∀ p ∈ A, s * p * s⁻¹ ∈ A) : A.relIndex (A ⊔ Subgroup.zpowers s) ≤ 2 := by
  have hsN : s ∈ Subgroup.normalizer (A : Set G) := Subgroup.mem_normalizer_iff.mpr fun p =>
    ⟨hsA p, fun h => by
      have h1 := hsA _ h
      rwa [show s * (s * p * s⁻¹) * s⁻¹ = p by
        rw [inv_eq_of_mul_eq_one_right hs]
        calc s * (s * p * s) * s = (s * s) * p * (s * s) := by simp only [mul_assoc]
          _ = p := by rw [hs, one_mul, mul_one]] at h1⟩
  have hle : A ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (A : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hsN)
  have := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hle
  set s' : ↥(A ⊔ Subgroup.zpowers s) := ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩
  have hsup : A.subgroupOf (A ⊔ Subgroup.zpowers s) ⊔ Subgroup.zpowers s' = ⊤ := by
    apply Subgroup.map_injective (A ⊔ Subgroup.zpowers s).subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left le_sup_left, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  rw [Subgroup.relIndex, ← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_left,
    ← Subgroup.inf_relIndex_right]
  have h2 : orderOf s' ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
    rw [Subgroup.coe_pow, sq]
    exact hs))
  refine Nat.le_of_dvd two_pos ((Subgroup.relIndex_dvd_card _ _).trans ?_)
  rwa [Nat.card_zpowers]

end CFSG.GroupTheory
