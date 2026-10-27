module

public import CFSG.CGT.PushingUpLit.EightOneRel
public import CFSG.Foundations.Catalog

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement

@[expose] def AschbacherSixThreeCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.IsKGroup G → IsCharacteristicP 2 G →
    ∀ Y : Subgroup G, InClassXG Y →
      ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X

theorem kProper_of_isKGroup' {G : Type} [Group G] (hG : CFSG.IsKGroup G) :
    KProper InCatalog G :=
  CFSG.KCore.KGroupNonab.kProperNonab (CFSG.KCore.KGroupAllSimple.kGroupNonab hG)

theorem AschbacherSixThreeCore.rel (h : AschbacherSixThreeCore) {G : Type} [Group G] [Finite G]
    {N X : Subgroup G} (hK : CFSG.IsKGroup ↥N) (hN : IsCharacteristicP 2 ↥N)
    (hX : InClassXGIn N X) :
    ∃ L : Subgroup G, X ≤ L ∧ L ≤ N ∧ (L.subgroupOf N).IsSubnormal ∧ InClassX ↥L ∧
      Arrow X L := by
  obtain ⟨L', hXL', hsub, hcl, harrow⟩ := h ↥N hK hN (X.subgroupOf N) hX.2
  have hXN : X ≤ N := hX.1
  have hXmap : (X.subgroupOf N).map N.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXN
  have hL'sub : (L'.map N.subtype).subgroupOf N = L' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective L'
  refine ⟨L'.map N.subtype, ?_, Subgroup.map_subtype_le L', ?_, ?_, ?_⟩
  · rw [← hXmap]
    exact Subgroup.map_mono hXL'
  · rw [hL'sub]
    exact hsub
  · exact InClassX.of_mulEquiv (L'.equivMapOfInjective N.subtype N.subtype_injective) hcl
  · rw [← hXmap]
    exact arrow_map_subtype harrow

end CFSG.CGT.PushingUpLit.CGT6
