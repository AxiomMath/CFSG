module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem isKGroup_subgroup' {G : Type*} [Group G] (hG : CFSG.Open.IsKGroup G)
    (C : Subgroup G) : CFSG.Open.IsKGroup ↥C :=
  hG.subgroup C

theorem isKGroup_quotient' {G : Type*} [Group G] (hG : CFSG.Open.IsKGroup G) (N : Subgroup G)
    [N.Normal] : CFSG.Open.IsKGroup (G ⧸ N) :=
  hG.quotient N

theorem outer_solvable_of_isQuasisimple (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X)
    (hq : CFSG.Open.IsQuasisimple X) : Group.IsSolvable (Outer X) := by
  have : Group.IsPerfect X := ⟨hq.1⟩
  have hsimple : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  have hnab : ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian X hq
  let e : (↥(⊤ : Subgroup X) ⧸ (Subgroup.center X).subgroupOf ⊤) ≃* (X ⧸ Subgroup.center X) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩)
  have : ((Subgroup.center X).subgroupOf ⊤).Normal := Subgroup.Normal.subgroupOf inferInstance ⊤
  have hcat' := hX ⊤ (Subgroup.center X) le_top (e.isSimpleGroup_congr.2 hsimple)
    (by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩)
  have hcat : CFSG.Open.IsCatalogGroup (X ⧸ Subgroup.center X) := by
    obtain ⟨i, ⟨f⟩⟩ := hcat'
    exact ⟨i, ⟨e.symm.trans f⟩⟩
  have : Group.IsSolvable (Outer (X ⧸ Subgroup.center X)) := hSch _ hsimple hnab hcat
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient X

theorem outer_solvable_of_component (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) {Q : Type}
    [Group Q] [Finite Q] (hQ : CFSG.Open.IsKGroup Q) {K : Subgroup Q} (hK : IsComponentOf K ⊤) :
    Group.IsSolvable (Outer ↥K) :=
  outer_solvable_of_isQuasisimple hSch (isKGroup_subgroup' hQ K) hK.2.2

end CFSG.LocalAnalysis.GLTheoremB
