module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListThree
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeResidual
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeSporGenInputs
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenMGmat
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineONTripleCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLiftsSpor
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListAct
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListCat
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarListJ3
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFive
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3J2
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3Mathieu
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3He
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3Ru
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3J4

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81I.Section3 (Catalogue24_12)

theorem twelveSixKbarList_of_members (hcat : Catalogue24_12)
    (hB : CFSG.Assembly.CatalogAgreeOn CFSG.Assembly.InCatalog CFSG.Blueprint.Catalog)
    (h3 : KFactKbarListThree) (h5 : KFactKbarListFive) (hJS : CFSG.AGLEmbedding.KFactJ3Sylow)
    (hJO : CFSG.AGLEmbedding.KFactJ3OuterInvolution) (hJR : CFSG.AGLEmbedding.KFactJ3OuterRank)
    (hbr : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group)) :
    TwelveSixKbarList := by
  intro G _ _ M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ hyp hK
  obtain ⟨hcatK, hrK, ⟨eK⟩⟩ := hyp.kStar_catalogue hcat hB hK
  obtain ⟨Y, V, W₁, W₂, W₃, t₁, t₂, t₃, hInn, hY3, hcfg, hVY, ht₁, ht₂, ht₃⟩ :=
    hyp.exists_kbarCfg hK
  have hp : p.Prime := hyp.1.ctx.p_prime
  have hp2 : p ≠ 2 := hyp.1.ctx.p_odd
  have hp35 : p = 3 ∨ 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h | h
    · left
      have h2 := hp.two_le
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · norm_num at hp
    · exact Or.inr h
  rcases hp35 with rfl | hp5
  · rcases h3 _ hcatK hrK _ ⟨eK⟩ Y V W₁ W₂ W₃ t₁ t₂ t₃ hInn hY3 hcfg hVY ht₁ ht₂ ht₃ with
      h | h | h | h | h | h | hJ
    · exact Or.inl ⟨rfl, Or.inl h⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
    · exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
    · obtain ⟨a⟩ := hJ
      obtain ⟨b⟩ := hbr
      exact (hyp.false_of_j3 hJS hJO hJR hK ⟨a.trans b⟩).elim
  · obtain ⟨rfl, hA⟩ :=
      h5 p hp hp5 _ hcatK hrK _ ⟨eK⟩ Y V W₁ W₂ W₃ t₁ t₂ t₃ hInn hY3 hcfg hVY ht₁ ht₂ ht₃
    exact Or.inr ⟨rfl, hA⟩

theorem twelveSixKbarList_of_kFactKbarListFive
    (h5 : KFactKbarListFive) : TwelveSixKbarList :=
  twelveSixKbarList_of_members
    (CFSG.LocalAnalysis.AGL81I.Section3.catalogue24_12_of_five_three
      (CFSG.LocalAnalysis.AGL81I.Section3.catalogue24_12Five_of_sporadicGen
        CFSG.LocalAnalysis.AGL81I.Section3.SporGen.MThirteen.sporadicGen24_12Five_holds)
      (CFSG.LocalAnalysis.AGL81I.Section3.catalogue24_12Three_of_sporadicGen
        (CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree.sporadicGen24_12Three_of_inputs
          CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCentGen_J2_three
          CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCentGen_M24_three
          CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCentGen_He_three
          CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCentGen_Ru_three
          CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCentGen_J4_three
          CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCoverGen_M22
          CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree.onTripleCoverFacts_holds
          CFSG.LocalAnalysis.RankThreeTheoremC.hasLiftableTriple_J3)))
    CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree kFactKbarListThree_holds h5
    CFSG.AGLEmbedding.kFactJ3Sylow CFSG.AGLEmbedding.kFactJ3OuterInvolution
    (CFSG.AGLEmbedding.kFactJ3OuterRank_closed CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv)
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv

theorem twelveSixKbarList_holds
    : TwelveSixKbarList :=
  twelveSixKbarList_of_kFactKbarListFive kFactKbarListFive_holds

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
