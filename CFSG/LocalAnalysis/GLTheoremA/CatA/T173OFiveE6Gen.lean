module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcWeyl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem eq_of_rootSubgroup_le_of_weylElt_mem_normalizer {F : Type} [Field F]
    {X : Subgroup (ModGL Tag.E6 F)} (hX : X ≤ adjointGroup Tag.E6 F)
    (hW : ∀ i, weylElt Tag.E6 F i 1 ∈ Subgroup.normalizer (X : Set (ModGL Tag.E6 F)))
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hαX : rootSubgroup Tag.E6 F α ≤ X) :
    X = adjointGroup Tag.E6 F := by
  have hN : Subgroup.closure (Set.range fun i : Fin Tag.E6.rank => weylElt Tag.E6 F i 1) ≤
      Subgroup.normalizer (X : Set (ModGL Tag.E6 F)) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hW i
  have hroot : ∀ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β → rootSubgroup Tag.E6 F β ≤ X := by
    intro β hβ
    obtain ⟨w, hw⟩ := exists_weyl_smul_eq_of_isRoot (τ := Tag.E6) (by left; rfl) hα hβ
    rw [← hw, ← (canonical_weyl_root_transport Tag.E6 F).2.1 w α hα]
    have hn := hN (canonicalRep_mem_closure (coxeterSystem Tag.E6) F w)
    rintro y ⟨x, hx, hxy⟩
    rw [← hxy]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp hn x).mp (hαX hx)
  refine le_antisymm hX ?_
  rw [adjointGroup_eq_rootSpan]
  exact iSup₂_le fun β hβ => hroot β hβ

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
