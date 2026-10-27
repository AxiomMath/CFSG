module

public import CFSG.Holt.StarCase.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Holt

open MulAction Equiv Equiv.Perm CFSG.Open
open scoped Pointwise

section SylowHelpers

variable {G : Type*} [Group G]

instance evenSubgroup_normal {Ω : Type*} [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] :
    (evenSubgroup G Ω).Normal := by
  unfold evenSubgroup
  infer_instance

theorem fusionIsSylowIn_of_isSylowOf {p : ℕ} {P K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) : fusionIsSylowIn p P K := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, fun R hRK hR hQR => ?_⟩
  have hQR' : (Q : Subgroup K) ≤ R.subgroupOf K := fun x hx => hQR ⟨x, hx, rfl⟩
  rw [← Q.is_maximal' (hR.comap_of_injective K.subtype K.subtype_injective) hQR']
  exact ((Subgroup.subgroupOf_map_subtype R K).trans (inf_eq_left.mpr hRK)).symm

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem fusionIsSylowIn_inf_of_le_normalizer {P K N : Subgroup G} (hP : fusionIsSylowIn p P K)
    (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set G)) : fusionIsSylowIn p (P ⊓ N) N :=
  fusionIsSylowIn_of_isSylowOf (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer
    (exists_sylow_map_eq_of_fusionIsSylowIn hP) hNK hKN)

theorem exists_fusionIsSylowIn_mem_normalizer {Y : Subgroup G} {s : G}
    (hs : IsPGroup p (Subgroup.zpowers s)) (hsY : s ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ P, fusionIsSylowIn p P Y ∧ s ∈ Subgroup.normalizer (P : Set G) := by
  have hY' : Y ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hsY)
  obtain ⟨Q, hsQ, hQ⟩ := exists_fusionIsSylowIn_ge hs (le_sup_right : _ ≤ Y ⊔ Subgroup.zpowers s)
  refine ⟨Q ⊓ Y, fusionIsSylowIn_inf_of_le_normalizer hQ le_sup_left hY', ?_⟩
  have hsQ' : s ∈ Q := hsQ (Subgroup.mem_zpowers s)
  refine Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨?_, hsY⟩)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => Q.mul_mem (Q.mul_mem hsQ' hx) (Q.inv_mem hsQ'), fun hx => ?_⟩
  have := Q.mul_mem (Q.mul_mem (Q.inv_mem hsQ') hx) hsQ'
  simpa [mul_assoc] using this

omit [Finite G] [Fact p.Prime] in
theorem mem_of_fusionIsSylowIn_of_commute {P K : Subgroup G} {t : G} (hP : fusionIsSylowIn p P K)
    (htK : t ∈ K) (ht : IsPGroup p (Subgroup.zpowers t)) (hc : ∀ x ∈ P, x * t = t * x) :
    t ∈ P := by
  have hconj : ∀ x ∈ P, t * x * t⁻¹ = x := fun x hx => by rw [← hc x hx, mul_inv_cancel_right]
  have hN : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => (hconj x hx).symm ▸ hx, fun hx => ?_⟩
    have h := hconj _ hx
    rw [mul_left_inj, mul_right_inj] at h
    exact h ▸ hx
  have hsup := hP.2.2 _ (sup_le hP.1 (Subgroup.zpowers_le.mpr htK))
    (hP.2.1.to_sup_of_normal_left' ht hN) le_sup_left
  exact hsup ▸ (le_sup_right : Subgroup.zpowers t ≤ P ⊔ _) (Subgroup.mem_zpowers t)

end SylowHelpers

end CFSG.Holt
