module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma313
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

theorem solomonThm13Input_of_props
    (h33 : Lemma33Input) (hres : Lemma313ResidueInput) (h32 : Lemma32Input)
    (h315a : Lemma315aInput) (h315c : Lemma315cInput) (hbal : Lemma316BalancedInput)
    (hprod : Lemma316ProductInput) : SolomonThm13Input :=
  solomonThm13Input_of_inputs (lemma313Input_of_inputs h33 hres h32 h315a h315c hbal hprod)
    (lemma316Input_of_inputs h32 h315a h315c hbal hprod)

theorem false_of_isSolomonChoice_of_props
    {𝒜 : Thm13Ambient} (h33 : Lemma33InputFor 𝒜) (hres : Lemma313ResidueInputFor 𝒜)
    (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜)
    (hbal : Lemma316BalancedInputFor 𝒜) (hprod : Lemma316ProductInputFor 𝒜) {G : Type}
    [Group G] [Finite G] (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N) : False :=
  false_of_isSolomonChoice
    (lemma313InputFor_of_inputs (lemma33CentralInputFor_of_lemma33InputFor h33) hres h32 h315a
      h315c hbal hprod)
    (lemma316InputFor_of_inputs h32 h315a h315c hbal hprod) hG hN

end CFSG.ComponentClassification.Sol76
