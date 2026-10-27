module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Props
public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Kernel
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Final
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsFinal
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsSuz
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L315c
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L33Full

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

theorem solomonThm13Simple_of_two_residues
    (hres : Lemma313ResidueInputFor simpleAmbient) (hb : Lemma315bInputFor simpleAmbient) :
    SolomonThm13Simple := by
  have hq : QuasisimpleTwoPartInput :=
    quasisimpleTwoPartInput_of_centralFour Hq4.quasisimpleCentralFourInput_holds
  have h𝒜 : ∀ (G : Type) [Group G] [Finite G], simpleAmbient G → KStarKProper G :=
    fun _ _ _ hG => kStarKProper_of_simpleAmbient hG
  have hR1 : Lemma32ConditionTwoInputFor simpleAmbient :=
    lemma32ConditionTwoInputFor_of_rankTwo
      (lemma32ConditionTwoRankTwoInputFor_of_kernel hq h𝒜
        (lemma32RankTwoKernelInput_of_central
          (R12.quasisimpleRankTwoCentralInput_of_symplectic
            (R12.Pcls.quasisimpleRankTwoSymplecticInput_of_suz R12.Pcls.sporadicCoverRankInput_Suz))))
  have h32 : Lemma32InputFor simpleAmbient := lemma32InputFor_simple_of_twoPart hq hR1
  have h315a := lemma315aInputFor_simple_of_315b hq hR1 hb
  have h315c := lemma315cInputFor_simple_of_315b hq hR1 hb
  have hbal : Lemma316BalancedInputFor simpleAmbient :=
    lemma316BalancedInputFor_of_noncentral h32 h315a h315c hq h𝒜
  have hprod := lemma316ProductInputFor_of_steps h32 h315a h315c hbal
  have h33 := lemma33CentralInputFor_of_steps h32 h315a h315c hbal hprod hq h𝒜
  exact solomonThm13Simple_of_noChoice fun _ _ _ hG _ hN =>
    false_of_isSolomonChoice (lemma313InputFor_of_inputs h33 hres h32 h315a h315c hbal hprod)
      (lemma316InputFor_of_inputs h32 h315a h315c hbal hprod) hG hN

end CFSG.ComponentClassification.Sol76T13
