module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Product
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Props

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

theorem lemma316ProductInput_of_steps (h32 : Lemma32Input) (h315a : Lemma315aInput)
    (h315c : Lemma315cInput) (hbal : Lemma316BalancedInput) : Lemma316ProductInput :=
  lemma316ProductInputFor_of_steps h32 h315a h315c hbal

theorem false_of_isSolomonChoice_of_steps
    {𝒜 : Thm13Ambient} (h33 : Lemma33InputFor 𝒜) (hres : Lemma313ResidueInputFor 𝒜)
    (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜)
    (hbal : Lemma316BalancedInputFor 𝒜) {G : Type} [Group G] [Finite G] (hG : 𝒜 G)
    {N : Subgroup G} (hN : IsSolomonChoice N) : False :=
  false_of_isSolomonChoice_of_props h33 hres h32 h315a h315c hbal
    (lemma316ProductInputFor_of_steps h32 h315a h315c hbal) hG hN

theorem solomonThm13Input_of_steps
    (h33 : Lemma33Input) (hres : Lemma313ResidueInput) (h32 : Lemma32Input)
    (h315a : Lemma315aInput) (h315c : Lemma315cInput) (hbal : Lemma316BalancedInput) :
    SolomonThm13Input :=
  solomonThm13Input_of_props h33 hres h32 h315a h315c hbal
    (lemma316ProductInputFor_of_steps h32 h315a h315c hbal)

theorem solomonThm13Simple_of_steps
    (h33 : Lemma33InputFor simpleAmbient) (hres : Lemma313ResidueInputFor simpleAmbient)
    (h32 : Lemma32InputFor simpleAmbient) (h315a : Lemma315aInputFor simpleAmbient)
    (h315c : Lemma315cInputFor simpleAmbient) (hbal : Lemma316BalancedInputFor simpleAmbient) :
    SolomonThm13Simple :=
  solomonThm13Simple_of_props h33 hres h32 h315a h315c hbal
    (lemma316ProductInputFor_of_steps h32 h315a h315c hbal)

end CFSG.ComponentClassification.Sol76T13
