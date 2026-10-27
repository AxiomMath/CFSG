module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Main
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Two
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Link

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer

theorem prop_4_3Ep (h42 : Prop4_2) (hL : Lemma31Narrow) : Prop4_3Ep :=
  prop_4_3Ep_of_hyp l34DiagClosure_of_cert
    (fun G _ _ z k _ hctx => (E4Facts.of_leaves h42 hL hctx).toHyp)

theorem prop4_7cS_of_hyp (h41b : Prop4_1b) (h43 : Prop4_3Ep)
    (hF : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → E4Facts G z k)
    (hR : Prop47R) (hSL2 : P47BranchSL2) (hC : P47BranchC) : Prop4_7cS := by
  intro G _ _ z k S ctx H X T p sig hTHS hT hTX
  rcases hT with hT1 | hT2
  · obtain ⟨h1, hTS⟩ := hT1
    have hSH : S ≤ H := by
      rw [← hTS]
      exact hTHS.trans inf_le_left
    exact prop4_7cS_typeOne h41b h43 hF hC ctx sig hSH
  · exact prop4_7cS_fourC2 h41b h43 hF hR hSL2 hC ctx hT2.1 sig hTHS (Or.inr hT2) hTX

theorem prop4_7S_of (h42 : Prop4_2) (hL : Lemma31Narrow)
    (hR : Prop47R) (hSL2 : P47BranchSL2) (hC : P47BranchC) : Prop4_7S :=
  prop4_7S_of_cS
    (prop4_7cS_of_hyp (prop_4_1b_of L199.ig_19_9) (prop_4_3Ep h42 hL)
      (fun G _ _ z k _ hctx => E4Facts.of_leaves h42 hL hctx) hR hSL2 hC)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
