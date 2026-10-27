module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomGenerationTwoPar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSmallA6U33
public import CFSG.LieType.ChevTwo.BorelTitsTwo
import CFSG.Quasithin.EmptyFaithful.SBc17Ent3
import CFSG.Quasithin.Background.C22PfG
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin in
theorem holds_two_of_psu_three_three
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.StatedClassicalModel K .PSU 3 3 1) :
    CFSG.LieType.BorelTits.Holds K 2 := by
  have hTX : CFSG.LieType.BorelTits.HoldsTits K 2 :=
    CFSG.LieType.ChevTwo.holdsTits_of_psu_three_three hK
  obtain ⟨eX⟩ := SBc17.nonempty_mulEquiv_PSU3_of_isPSU hK
  obtain ⟨eU⟩ := u33Pres_mulEquiv_PSU3
  have : Finite U33G := u33Pres_finite_card_le.1
  have hNU : Subgroup.normalizer ((u33SylowT : Subgroup U33G) : Set U33G) ≤ u33SylowT := by
    rw [coe_u33SylowT, u33Extra.normalizer_T]
  exact C22Pf.holds_of_holdsTits hTX
    (C22Pf.normalizer_le_of_mulEquiv (eX.trans eU.symm) u33SylowT hNU)

theorem gomiAtomGenerationTop_of_psu_three_three
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.StatedClassicalModel K .PSU 3 3 1) :
    GomiAtomGenerationTop K := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hK⟩)
  obtain ⟨_, P₁, P₂, h⟩ := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.twoPar_u33
  obtain ⟨P₁', P₂', h'⟩ := h.exists_of_equiv e.symm
    (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow (default : Sylow 2 K))
  exact gomiAtomGenerationTop_of_twoPar h'

end CFSG.GroupTheory
