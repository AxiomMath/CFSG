module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
public import CFSG.Sporadic.ONOddCore.LocalComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

section ON


theorem on_inner_not_twoSmall {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.ON)
    {s : S} (hs : orderOf s = 2) {D : Subgroup (fixedSubgroup (MulAut.conj s))}
    (hD : IsComponent D) : ¬ FixedCentralizerTwoSmall (MulAut.conj s) D := by
  set f : S ≃* Pv := e.trans onEquivPv
  have hft : orderOf (f s) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hs
  obtain ⟨g⟩ := centralizer_P_equiv_M hft
  let h : fixedSubgroup (MulAut.conj s) ≃* onM :=
    (MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf s)).trans
      ((Sporadic.ONOddCore.centralizerCongr f s).trans g)
  exact not_fixedCentralizerTwoSmall_of_mulEquiv_ker hD h piR
    (by rw [ker_piR]; exact card_onQ_subgroupOf_M)

end ON

end CFSG.SeitzReduction.SporadicRefine
