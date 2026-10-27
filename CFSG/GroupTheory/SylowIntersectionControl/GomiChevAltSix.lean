module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomGenerationTwoPar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSmallA6U33
import CFSG.LieType.ChevTwo.BorelTitsTwo
import CFSG.GroupTheory.PermSylowTwo.Alt
import CFSG.Quasithin.Background.C22PfE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.GroupTheory

theorem holds_two_of_mulEquiv_alternatingGroup_six {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 6)) : CFSG.LieType.BorelTits.Holds K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.Quasithin.C22Pf.holds_of_holdsTits
    (CFSG.LieType.BorelTits.HoldsTits.of_mulEquiv e.symm
      CFSG.LieType.ChevTwo.holdsTits_alternating_six) fun S => ?_
  simpa using CFSG.GroupTheory.PermSylowTwo.inf_normalizer_le_of_mulEquiv_alt le_rfl
    (Subgroup.topEquiv.trans e) (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S)

theorem gomiAtomGenerationTop_of_mulEquiv_alternatingGroup_six
    {K : Type} [Group K] [Finite K] (e : K ≃* alternatingGroup (Fin 6)) :
    GomiAtomGenerationTop K := by
  obtain ⟨_, P₁, P₂, h⟩ := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.twoPar_alt_six
  obtain ⟨P₁', P₂', h'⟩ := h.exists_of_equiv e.symm
    (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow (default : Sylow 2 K))
  exact gomiAtomGenerationTop_of_twoPar h'

end CFSG.GroupTheory
