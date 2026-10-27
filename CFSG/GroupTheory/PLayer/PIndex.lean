module

public import CFSG.HardMathSupport.Solomon.Proving.LBLayerConj
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover

public section

namespace CFSG

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_isPGroup_sup_eq_of_isPGroup_quotient {p : ℕ} (hp : p.Prime) {N X : Subgroup G}
    (hNX : N ≤ X) (hNnorm : (N.subgroupOf X).Normal)
    (hquot : IsPGroup p (↥X ⧸ N.subgroupOf X)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ P ≤ Subgroup.normalizer (N : Set G) ∧ N ⊔ P = X := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥X := Subtype.finite
  let S : Sylow p ↥X := Classical.choice (Sylow.nonempty (p := p) (G := ↥X))
  set q : ↥X →* (↥X ⧸ N.subgroupOf X) := QuotientGroup.mk' (N.subgroupOf X) with hq
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  let T : Sylow p (↥X ⧸ N.subgroupOf X) := S.mapSurjective hqsurj
  have hTtop : (T : Subgroup (↥X ⧸ N.subgroupOf X)) = ⊤ := by
    have hmax := T.is_maximal' (hquot.to_subgroup (⊤ : Subgroup (↥X ⧸ N.subgroupOf X)))
      (le_top : (T : Subgroup (↥X ⧸ N.subgroupOf X)) ≤ ⊤)
    exact hmax.symm
  have hsplitX : (N.subgroupOf X) ⊔ (S : Subgroup ↥X) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    haveI := hNnorm
    have hxT : q x ∈ (T : Subgroup (↥X ⧸ N.subgroupOf X)) := by
      rw [hTtop]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, hse⟩ := hxT
    have hmem : x * s⁻¹ ∈ N.subgroupOf X := by
      rw [← QuotientGroup.eq_one_iff (x * s⁻¹), QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (QuotientGroup.mk' (N.subgroupOf X)) x *
        ((QuotientGroup.mk' (N.subgroupOf X)) s)⁻¹ = 1
      rw [hse, mul_inv_cancel]
    exact (Subgroup.mem_sup_of_normal_left).2 ⟨x * s⁻¹, hmem, s, hs, by group⟩
  refine ⟨(S : Subgroup ↥X).map X.subtype, S.isPGroup'.map X.subtype, ?_, ?_⟩
  · refine (Subgroup.map_subtype_le _).trans ?_
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).1 hNnorm
  · have h := congrArg (Subgroup.map X.subtype) hsplitX
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hNX, Subgroup.map_top,
      Subgroup.range_subtype] at h
    exact h

theorem glaPComponent_iff_of_isPGroup_quotient {p : ℕ} (hp : p.Prime) {N X J : Subgroup G}
    (hNX : N ≤ X) (hNnorm : (N.subgroupOf X).Normal)
    (hquot : IsPGroup p (↥X ⧸ N.subgroupOf X)) :
    GLAPComponent p X J ↔ GLAPComponent p N J := by
  obtain ⟨P, hP, hPN, hsplit⟩ := exists_isPGroup_sup_eq_of_isPGroup_quotient hp hNX hNnorm hquot
  constructor
  · intro hJ
    exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_of_sup_isPGroup hp hP hPN
      (hsplit.symm ▸ hJ)
  · intro hJ
    exact CFSG.HardMathSupport.Solomon.Proving.glaPComponent_of_normal_overgroup hp hNX hNnorm hJ

end CFSG

end
