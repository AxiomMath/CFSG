module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open

@[expose] def TypePartition (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    CFSG.Blueprint.OddLieType X ∨ CFSG.Blueprint.EvenLieType X ∨
      CFSG.Blueprint.NativeSporadic.SporadicRep X

private theorem map_subgroupOf_top_center {L : Type*} [Group L] :
    ((Subgroup.center L).subgroupOf ⊤).map
      (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom = Subgroup.center L := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, trivial⟩, hx, rfl⟩

theorem inCatalog_quotient_center_of_kgroup {L : Type*} [Group L] (hq : CFSG.Open.IsQuasisimple L)
    (hK : CFSG.Open.IsKGroup L) : IsCatalogGroup (L ⧸ Subgroup.center L) := by
  have : ((Subgroup.center L).subgroupOf (⊤ : Subgroup L)).Normal := Subgroup.normal_subgroupOf
  let e : ((⊤ : Subgroup L) ⧸ (Subgroup.center L).subgroupOf (⊤ : Subgroup L)) ≃*
      (L ⧸ Subgroup.center L) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv map_subgroupOf_top_center
  have hs : IsSimpleGroup ((⊤ : Subgroup L) ⧸ (Subgroup.center L).subgroupOf (⊤ : Subgroup L)) :=
    e.isSimpleGroup_congr.mpr hq.2
  have hn : ∃ a b : (⊤ : Subgroup L) ⧸ (Subgroup.center L).subgroupOf (⊤ : Subgroup L),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_quotient_center_of_quasisimple hq
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  obtain ⟨i, ⟨φ⟩⟩ := hK ⊤ (Subgroup.center L) le_top hs hn
  exact ⟨i, ⟨e.symm.trans φ⟩⟩

theorem catalog_quotient_center_of_kgroup (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L) (hK : CFSG.Open.IsKGroup L) :
    CFSG.Blueprint.Catalog (L ⧸ Subgroup.center L) := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  exact hbridge _ (exists_noncomm_quotient_center_of_quasisimple hq)
    (inCatalog_quotient_center_of_kgroup hq hK)

theorem quasisimple_kgroup_type_of_bridge (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L) (hK : CFSG.Open.IsKGroup L) :
    TypePartition (L ⧸ Subgroup.center L) :=
  (CFSG.Milestones.ct_catalog_nonabelian_type_partition _
    (exists_noncomm_quotient_center_of_quasisimple hq)).1
    (catalog_quotient_center_of_kgroup hbridge hq hK)

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
