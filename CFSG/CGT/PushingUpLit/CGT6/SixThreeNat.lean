module

public import CFSG.CGT.PushingUpLit.CGT6.SixThreeCore
public import CFSG.CGT.PushingUpLit.T2KR.P53NatArrow
public import CFSG.CGT.PushingUpLit.SixThreeBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Assembly
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.SixThree CFSG.Quasithin
open CFSG.CGT.PushingUpLit.EightOneRel
open scoped commutatorElement Pointwise

@[expose] def AschbacherSixThreeCoreNat : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.IsKGroup G → IsCharacteristicP 2 G →
    ∀ Y : Subgroup G, InClassXG Y →
      ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ ArrowNat Y X

theorem aschbacherSixThreeCore_of_coreNat (h : AschbacherSixThreeCoreNat) :
    AschbacherSixThreeCore := by
  intro G _ _ hG hchar Y hY
  obtain ⟨X, hYX, hsub, hcl, harrow⟩ := h G hG hchar Y hY
  exact ⟨X, hYX, hsub, hcl, harrow.arrow⟩

theorem AschbacherSixThreeCoreNat.rel (h : AschbacherSixThreeCoreNat) {G : Type} [Group G]
    [Finite G] {N X : Subgroup G} (hK : CFSG.IsKGroup ↥N) (hN : IsCharacteristicP 2 ↥N)
    (hX : InClassXGIn N X) :
    ∃ L : Subgroup G, X ≤ L ∧ L ≤ N ∧ (L.subgroupOf N).IsSubnormal ∧ InClassX ↥L ∧
      ArrowNat X L := by
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
    exact T2KR.P53.arrowNat_map_subtype harrow

end CFSG.CGT.PushingUpLit.CGT6
