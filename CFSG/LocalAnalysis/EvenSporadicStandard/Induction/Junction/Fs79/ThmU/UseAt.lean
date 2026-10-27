module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Use
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.LayerBalanceAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.UseAux
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.StdBareStandard

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.ComponentClassification.AschbacherToolkit
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem ThmU.layerBalanceAt_of_layerBalanceKAt {H : Type} [Group H] [Finite H]
    (hLB : Junction.LayerBalanceKAt H) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (hO : CFSG.oddCore H = ⊥) : ThmU.LayerBalanceAt H := by
  intro S t hS ht2 htS hcomm K hK
  have h := hLB hkp hO S t hS ht2 htS hcomm K hK
  rwa [centralizer_zpowers_eq] at h

theorem fs79Thm13UseAt_of_lemma15At
    {H : Type} [Group H] [Finite H] (h15 : FS79Lemma15At H) : FS79Thm13UseAt H := by
  intro hkp N hN hperf K hK hrk
  obtain ⟨t, ht2, hcomp⟩ := hK.1
  have hO : CFSG.oddCore H = ⊥ := hN.oddCore_eq_bot
  have hLB := ThmU.layerBalanceAt_of_layerBalanceKAt
    (Junction.layerBalanceKAt_of_lemma15At h15) hkp hO
  have hstar := starHyp_of_fStarSimple hN hperf
  have hrank := ThmU.two_le_pRank_of_ne_one hK.1 hrk
  have hu : ThmU.UniversalF K :=
    ThmU.maximalF_universal hLB ThmU.glaubermanSimplePerfect_proved hstar hK hrank
  have hq : CFSG.Assembly.IsQuasisimple K := assembly_isQuasisimple_of_inLF hK.1
  have hCeven := even_card_centralizer_of_inLF hK.1
  have hU := isUniversalComponent_of_universalF hu
  have heven : Even (Nat.card K) :=
    CFSG.LocalAnalysis.ComponentInitial.even_card_of_two_le_pRank hrank
  have hKN : K ≤ N := hperf K (ThmU.IsCompIn.perfect hcomp)
  have hH := ThmU.normalizer_blockGroup_ne_top_of_fStarSimple hN hq hU heven hKN hCeven
  have hstd := ThmU.universal_rank_two_component_isStandardSubgroup_of_ne_top
    hq hrank hCeven hU hH
  exact ((standardComponentIsStandard_iff_stdBare).1 hstd).2.2

end CFSG.EvenSporadicStandard.Induction
