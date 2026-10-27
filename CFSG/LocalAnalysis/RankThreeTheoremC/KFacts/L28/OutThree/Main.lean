module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsL28
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Linear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Small
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankOneFinal
import CFSG.Models.Blueprint
import CFSG.RankThree.PartTwo.KFacts.KS14Sz

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28

open CFSG.Open TauCeti
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)

namespace OutThree

theorem statedClassicalModel_psu_of_twistedA {S : Type} [Group S] (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) :
    StatedClassicalModel S .PSU 3 q.p q.exponent := by
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA 2 q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA 2 q
  have h := CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by norm_num)
    (CFSG.Models.lieModel_twistedA 2 q hv e)
  rwa [hc, hf] at h

theorem statedClassicalModel_psl_of_typeA {S : Type} [Group S] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) (e : S ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    StatedClassicalModel S .PSL (r + 1) q.p q.exponent :=
  CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega) (CFSG.Models.lieModel_A r q hv e)

end OutThree

section Certified


namespace OutThree

theorem autThreePowInner_of_catalog
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : IsCatalogGroup S)
    (h3 : (Nat.card S).factorization 3 = 1) : AutThreePowInner S := by
  obtain ⟨i, he⟩ := hcat
  rcases CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple S hS hnab i
      he (pRank_three_top_eq_one h3) with ⟨⟨d1, hv⟩, hfam, ⟨e⟩⟩ | he | he
  · rcases hfam with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ <;> simp only at hd <;> subst hd
    · exact autThreePowInner_of_psl_two (statedClassicalModel_psl_of_typeA 1 q hv e) hq h3
    · exact autThreePowInner_of_psl_three (statedClassicalModel_psl_of_typeA 2 q hv e)
        (by rwa [← TauCeti.PrimePower.card_def]) h3
    · exact autThreePowInner_of_psu_three (statedClassicalModel_psu_of_twistedA q hv e)
        (by rwa [← TauCeti.PrimePower.card_def]) h3
  · obtain ⟨e⟩ := he
    exact autThreePowInner_of_j1 e
  · obtain ⟨e⟩ := he
    exact autThreePowInner_of_alt_five e

theorem outCommInner_of_catalog
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : IsCatalogGroup S)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1) : OutCommInner S := by
  by_cases h3 : 3 ∣ Nat.card S
  · obtain ⟨i, he⟩ := hcat
    rcases CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple S hS
        hnab i he (le_antisymm hr (one_le_pRank_three_top h3)) with
      ⟨⟨d1, hv⟩, hfam, ⟨e⟩⟩ | he | he
    · rcases hfam with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ <;> simp only at hd <;> subst hd
      · exact outCommInner_of_psl_two (statedClassicalModel_psl_of_typeA 1 q hv e)
      · exact outCommInner_of_psl_three (statedClassicalModel_psl_of_typeA 2 q hv e)
          (by rwa [← TauCeti.PrimePower.card_def])
      · exact outCommInner_of_psu_three (statedClassicalModel_psu_of_twistedA q hv e)
          (by rwa [← TauCeti.PrimePower.card_def])
    · obtain ⟨e⟩ := he
      exact outCommInner_of_j1 e
    · obtain ⟨e⟩ := he
      exact outCommInner_of_alt_five e
  · have : IsSimpleGroup S := hS
    obtain ⟨f, hf⟩ :=
      CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd S hnab hcat h3
    exact outCommInner_of_suzukiModel hf

end OutThree

open OutThree

theorem kFactOutThreeCoprime_holds
    : KFactOutThreeCoprime := by
  intro Y _ _ K hK hnab hcat h3 d hd ⟨n, hn⟩
  exact mem_sup_centralizer_of_autThreePowInner (autThreePowInner_of_catalog hK hnab hcat h3) hd hn

theorem kFactOutThreeNilpotent_holds
    : KFactOutThreeNilpotent := by
  intro Y _ _ K hK hnab hcat hr
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hr
  exact exists_threeComplement_of_outCommInner (outCommInner_of_catalog hK hnab hcat hr)

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.L28
