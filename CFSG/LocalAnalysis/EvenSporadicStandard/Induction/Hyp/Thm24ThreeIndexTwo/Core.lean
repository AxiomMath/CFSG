module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo.CoreIn
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo.CoreOut

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.ComponentClassification.CatFC

theorem false_of_index_two (inp : Thm24ThreeSimpleInputs) (I : ArmInputs)
    {s' : TauCeti.SporadicName} (hs' : s' ∈ Sol78Rows) {H : Type} [Group H] [Finite H]
    {N : Subgroup H} (hN : FStarSimple N) (h2 : N.index = 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {A : Subgroup H} (hA : SolStd A)
    (hcov : OddCover s' A) (hrk : 2 ≤ CFSG.pRank 2 ↥(centralizer (A : Set H))) : False := by
  have hAN : A ≤ N := perfect_subgroups_le_of_index_le_two hN.normal h2.le A
    (Subgroup.isPerfect_iff.1 hcov.1.1)
  obtain ⟨x, hx, y, hy, hx2, hy2, hxy, hcomm⟩ :=
    CFSG.GH74.GLS.C3.Layer1.U1a.exists_commuting_involutions hrk
  rcases involution_split_of_index_two h2 hx hy hx2 hy2 hxy hcomm with
    ⟨hxN, hyN⟩ | ⟨a, ha, b, hb, ha2, hb2, haN, hbN⟩
  · exact false_of_commuting_involutions_in inp hs' hN hkp hA hcov hAN hxN hyN hx hy hx2 hy2 hxy
      hcomm
  · exact false_of_inner_and_outer_involutions inp I hs' hN h2 hkp hA hcov hAN ha hb ha2 hb2 haN
      hbN

end CFSG.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.ComponentClassification.CatFC

theorem thm24ThreeUse_of_inputs (inp : Thm24ThreeSimpleInputs) (I : ArmInputs)
    {s' : TauCeti.SporadicName} (hs' : s' ∈ Sol78Rows) : Thm24ThreeUse s' := by
  intro H _ _ N hN hidx hkp A hA hcov hrk
  rcases Balance.index_eq_one_or_two hidx with h1 | h2
  · obtain rfl : N = ⊤ := Subgroup.index_eq_one.1 h1
    haveI := hN.isSimpleGroup
    haveI : IsSimpleGroup H := MulEquiv.isSimpleGroup (Subgroup.topEquiv (G := H)).symm
    obtain ⟨a, b, hab⟩ := hN.nonabelian
    exact thm24Three_simple_of_inputs inp hs' H ⟨a.1, b.1, fun h => hab (Subtype.ext h)⟩ hkp A hA
      hcov hrk
  · exact Thm24ThreeIndexTwo.false_of_index_two inp I hs' hN h2 hkp hA hcov hrk

end CFSG.EvenSporadicStandard.Induction.Hyp
