module

public import CFSG.Open.GLBDefs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open

theorem strongRestrict_mem_glbConj_iff {X : Type*} [Group X] {g y : X} {H : Subgroup X} :
    y ∈ GLBConj g H ↔ g * y * g⁻¹ ∈ H := by
  unfold GLBConj
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro h
    exact ⟨g * y * g⁻¹, h, by simp [mul_assoc]⟩

theorem glbStronglyEmbedded_subgroupOf_inf {G : Type*} [Group G] [Finite G] {p : ℕ}
    {M N : Subgroup G} (hstr : GLBStronglyEmbedded p M) (hNM : ¬ N ≤ M)
    (hp : p ∣ Nat.card (N ⊓ M : Subgroup G)) :
    GLBStronglyEmbedded p ((N ⊓ M).subgroupOf N) := by
  have hcard : Nat.card ((N ⊓ M).subgroupOf N) = Nat.card (N ⊓ M : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ M ≤ N)).toEquiv
  refine ⟨?_, by rw [hcard]; exact hp, ?_⟩
  · intro htop
    apply hNM
    intro x hx
    exact ((Subgroup.subgroupOf_eq_top.mp htop) hx).2
  · intro g hg hdvd
    have hgM : (g : G) ∉ M := fun hm =>
      hg (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨g.2, hm⟩))
    have hS : (((N ⊓ M).subgroupOf N ⊓ GLBConj g ((N ⊓ M).subgroupOf N) : Subgroup N).map
        N.subtype) ≤ M ⊓ GLBConj (g : G) M := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      have hx1 : x ∈ (N ⊓ M).subgroupOf N := (Subgroup.mem_inf.mp hx).1
      have hx2 : g * x * g⁻¹ ∈ (N ⊓ M).subgroupOf N :=
        strongRestrict_mem_glbConj_iff.mp (Subgroup.mem_inf.mp hx).2
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx1)).2,
        strongRestrict_mem_glbConj_iff.mpr ?_⟩
      have h3 := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx2)).2
      simpa using h3
    have hdvdS : p ∣ Nat.card (((N ⊓ M).subgroupOf N ⊓ GLBConj g ((N ⊓ M).subgroupOf N) :
        Subgroup N).map N.subtype : Subgroup G) := by
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ N.subtype Subtype.val_injective).toEquiv]
      exact hdvd
    exact hstr.2.2 (g : G) hgM (hdvdS.trans (Subgroup.card_dvd_of_le hS))

end CFSG.AGLEmbeddingD2.McLaughlin
