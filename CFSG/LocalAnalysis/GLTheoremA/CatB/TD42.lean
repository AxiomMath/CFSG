module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD42Main
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD4
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Model
public import CFSG.Assembly.InCatalogConverse

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.CatB

theorem e9Solv_td4two
    (S : Type) [Group S] (h : catalogIs S S9.isTD4two) : E9Solv S := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isTD4two h
  obtain ⟨h1, h2⟩ :=
    primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num) (hq2.trans (by norm_num))
  obtain ⟨hfin, hsimp⟩ := CFSG.Assembly.lie_finite_simple ⟨.trialityD4 q, hv⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := hfin
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := hsimp
  haveI : Finite S := Finite.of_equiv _ e.symm.toEquiv
  haveI : IsSimpleGroup S := e.isSimpleGroup
  obtain ⟨⟨eT⟩, hZ, hA⟩ := CFSG.RankThree.PartTwo.Sec19.lineGroup_facts_of_isoLie q h1 h2 ⟨hv, ⟨e⟩⟩
  have hcardS : Nat.card S = 211341312 := by
    have hc := CFSG.AGLEmbedding.card_catGroup_trialityD4_even
      (d := ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) h1 rfl
    rw [Nat.card_congr e.toEquiv, hc, h2]
    norm_num [CFSG.Open.ordTrialityD4]
  have hT : Nat.card CFSG.RankThree.PartTwo.Sec4.Item434D42.lineGroup = 211341312 := by
    rw [← Nat.card_congr eT.toEquiv]
    exact hcardS
  exact (TD42.e9Solv_lineGroup hT hZ hA).of_mulEquiv eT

end CFSG.LocalAnalysis.GLTheoremA

end
