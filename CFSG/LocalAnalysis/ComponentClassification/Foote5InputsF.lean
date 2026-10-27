module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ABGLocalTools

@[expose] def Foote5Lemma24iiV : Prop :=
  ∀ (𝕊 : Type) [Group 𝕊] [Finite 𝕊], FooteSimpleType 𝕊 →
    ∀ V : Subgroup (MulAut 𝕊), IsKleinFour V → V ≤ innAut5 𝕊 →
    ∀ P : Subgroup (MulAut 𝕊), IsSylowOf 2 P (centralizer (V : Set (MulAut 𝕊))) →
      ∃ f : MulAut 𝕊, P = zpowers f ⊔ V

end CFSG.ComponentClassification.Foote5
