module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec126_mem_sup_zpowers {V' : Subgroup G} {s' : G} (hs'N : s' ∈ normalizer (V' : Set G))
    (hs' : s' * s' = 1) {y : G} (hy : y ∈ V' ⊔ zpowers s') : y ∈ V' ∨ ∃ v ∈ V', y = v * s' := by
  have hsi : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'
  have hconj : ∀ v ∈ V', s' * v * s'⁻¹ ∈ V' := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hs'N v).mp hv
  let W : Subgroup G :=
    { carrier := {y | y ∈ V' ∨ ∃ v ∈ V', y = v * s'}
      mul_mem' := by
        rintro a b (ha | ⟨v1, hv1, rfl⟩) (hb | ⟨v2, hv2, rfl⟩)
        · exact Or.inl (V'.mul_mem ha hb)
        · exact Or.inr ⟨a * v2, V'.mul_mem ha hv2, by simp only [mul_assoc]⟩
        · refine Or.inr ⟨v1 * (s' * b * s'⁻¹), V'.mul_mem hv1 (hconj b hb), ?_⟩
          group
        · refine Or.inl ?_
          have h : v1 * s' * (v2 * s') = v1 * (s' * v2 * s'⁻¹) := by
            rw [hsi]; simp only [mul_assoc]
          rw [h]
          exact V'.mul_mem hv1 (hconj v2 hv2)
      one_mem' := Or.inl V'.one_mem
      inv_mem' := by
        rintro a (ha | ⟨v, hv, rfl⟩)
        · exact Or.inl (V'.inv_mem ha)
        · refine Or.inr ⟨s' * v⁻¹ * s'⁻¹, hconj _ (V'.inv_mem hv), ?_⟩
          rw [mul_inv_rev, inv_mul_cancel_right, hsi] }
  have hle : V' ⊔ zpowers s' ≤ W := by
    refine sup_le (fun v hv => Or.inl hv) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr ⟨1, V'.one_mem, by simp⟩
  exact hle hy

theorem sec126_eq_of_le_sup [Finite G] {V V' : Subgroup G} {s' : G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hV' : CFSG.Open.IsElemAbelian 2 V')
    (hcV : Nat.card ↥V = 2 ^ 8) (hcV' : Nat.card ↥V' = 2 ^ 8)
    (hs'N : s' ∈ normalizer (V' : Set G)) (hs' : s' * s' = 1)
    (hle : V ≤ V' ⊔ zpowers s')
    (hC : Nat.card ↥(V' ⊓ centralizer ({s'} : Set G)) ≤ 16) : V = V' := by
  by_contra hne
  have hnle : ¬ V ≤ V' := fun h => hne (Subgroup.eq_of_le_of_card_ge h (by rw [hcV, hcV']))
  obtain ⟨x0, hx0V, hx0n⟩ := SetLike.not_le_iff_exists.mp hnle
  obtain ⟨v0, hv0, hx0⟩ : ∃ v ∈ V', x0 = v * s' := by
    rcases sec126_mem_sup_zpowers hs'N hs' (hle hx0V) with h | h
    · exact absurd h hx0n
    · exact h
  have hsi : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right hs'
  set U : Subgroup G := V ⊓ V' with hU
  have hUC : U ≤ V' ⊓ centralizer ({s'} : Set G) := by
    intro u hu
    refine Subgroup.mem_inf.mpr ⟨hu.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : u * x0 = x0 * u := hV.comm hu.1 hx0V
    have h2 : u * v0 = v0 * u := hV'.comm hu.2 hv0
    rw [hx0] at h1
    have h3 : v0 * (u * s') = v0 * (s' * u) := by
      calc v0 * (u * s') = (v0 * u) * s' := by simp only [mul_assoc]
        _ = (u * v0) * s' := by rw [h2]
        _ = u * (v0 * s') := by simp only [mul_assoc]
        _ = (v0 * s') * u := h1
        _ = v0 * (s' * u) := by simp only [mul_assoc]
    exact mul_left_cancel h3
  have hcardU : Nat.card ↥U ≤ 16 := (Subgroup.card_le_of_le hUC).trans hC
  have hUV : U ≤ V := inf_le_left
  have hcos : ∀ q : ↥V ⧸ U.subgroupOf V,
      q = QuotientGroup.mk 1 ∨ q = (QuotientGroup.mk (⟨x0, hx0V⟩ : ↥V) : ↥V ⧸ U.subgroupOf V) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    by_cases hx : (x : G) ∈ V'
    · left
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, mul_one]
      exact Subgroup.mem_inf.mpr ⟨V.inv_mem x.2, V'.inv_mem hx⟩
    · right
      obtain ⟨v1, hv1, hx1⟩ : ∃ v ∈ V', (x : G) = v * s' := by
        rcases sec126_mem_sup_zpowers hs'N hs' (hle x.2) with h | h
        · exact absurd h hx
        · exact h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact V.mul_mem (V.inv_mem x.2) hx0V
      · have h : ((x⁻¹ * ⟨x0, hx0V⟩ : ↥V) : G) = s' * (v1⁻¹ * v0) * s'⁻¹ := by
          change (x : G)⁻¹ * x0 = _
          rw [hx1, hx0, mul_inv_rev, hsi]
          simp only [mul_assoc]
        rw [h]
        exact (Subgroup.mem_normalizer_iff.mp hs'N _).mp (V'.mul_mem (V'.inv_mem hv1) hv0)
  have hidx : (U.subgroupOf V).index ≤ 2 := by
    classical
    let f : Bool → ↥V ⧸ U.subgroupOf V := fun b =>
      if b then QuotientGroup.mk 1 else QuotientGroup.mk (⟨x0, hx0V⟩ : ↥V)
    have hf : Function.Surjective f := by
      intro q
      rcases hcos q with h | h
      · exact ⟨true, by simp [f, h]⟩
      · exact ⟨false, by simp [f, h]⟩
    have := Nat.card_le_card_of_surjective f hf
    simpa [Subgroup.index] using this
  have hcard := Subgroup.index_mul_card (U.subgroupOf V)
  have hUcard : Nat.card ↥(U.subgroupOf V) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv
  rw [hUcard, Nat.card_congr (Equiv.refl _), hcV] at hcard
  have : 2 ^ 8 ≤ 2 * 16 := by
    calc 2 ^ 8 = (U.subgroupOf V).index * Nat.card ↥U := hcard.symm
      _ ≤ 2 * 16 := Nat.mul_le_mul hidx hcardU
  omega

end CFSG.OddStandard.SmallF3.Omega
