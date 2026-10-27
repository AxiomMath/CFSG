module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ConwayInput
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.NoEighthRoot
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ConjCField
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneFourth

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem twoCo1_not_standard
    (hD : OctadIsolation) (hco0 : Co0ConwayFacts)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L)
    (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Co1) : False :=
  twoCo1_not_standard_of_inputs h h2 hQ HypOne.hypothesisOne_native
    (Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
        Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner)
    (fun _ hz2 hZ => no_eighth_root_of_isSporadic (fun y => HypOne.no_twoB_fourth_power y) hQ
      hz2 hZ)
    (fun _ hz2 hZ _ _ hy hy' =>
      conj_typeC_of_isSporadic (Group.isPerfect_def.2 h.standard.1.1) hQ hz2 hZ hy hy')
    hD (co0LocalFacts_of_conway hco0)

end CFSG.EvenSporadicStandard.TwoCo1
