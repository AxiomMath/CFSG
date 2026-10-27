module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Balanced
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13ProductProps

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

theorem kStarKProper_of_simpleAmbient {G : Type} [Group G] [Finite G] (hG : SimpleAmbient G) :
    KStarKProper G :=
  have := hG.1
  kStarKProper_of_simple hG.2.1 hG.2.2

theorem false_of_isSolomonChoice_of_noncentral
    {𝒜 : Thm13Ambient} (h33 : Lemma33InputFor 𝒜) (hres : Lemma313ResidueInputFor 𝒜)
    (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜)
    (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G) {G : Type} [Group G]
    [Finite G] (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N) : False :=
  false_of_isSolomonChoice_of_steps h33 hres h32 h315a h315c
    (lemma316BalancedInputFor_of_noncentral h32 h315a h315c hq h𝒜) hG hN

theorem solomonThm13Simple_of_noncentral
    (h33 : Lemma33InputFor simpleAmbient) (hres : Lemma313ResidueInputFor simpleAmbient)
    (h32 : Lemma32InputFor simpleAmbient) (h315a : Lemma315aInputFor simpleAmbient)
    (h315c : Lemma315cInputFor simpleAmbient) (hq : QuasisimpleTwoPartInput) :
    SolomonThm13Simple :=
  solomonThm13Simple_of_steps h33 hres h32 h315a h315c
    (lemma316BalancedInputFor_of_noncentral h32 h315a h315c hq fun _ _ _ hG =>
      kStarKProper_of_simpleAmbient hG)

end CFSG.ComponentClassification.Sol76T13
