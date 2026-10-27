module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactSeitzOutsideLocal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactSeitzOutsideAltEight
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact131Holds
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.Models.Blueprint
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenScope)
open CFSG.LieType.SeitzGeneration (Cat)
open CFSG.AGLEmbeddingD2 (IsD2SeitzException)

namespace KSeitz

theorem not_bender_A1_eight {K : Type} [Group K] (hB : ¬ fusionIsBenderGroup K)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq2 : q.p = 2)
    (hq3 : q.exponent = 3) (e : K ≃* Cat ⟨.A 1 q, hv⟩) : False := by
  have hcl := CFSG.Models.LieModel.statedClassicalModel (CFSG.Models.lieModel_A 1 q hv e)
    (by simp [CFSG.Blueprint.classicalTags])
  rw [hq2, hq3] at hcl
  exact hB (CFSG.QuasithinUnique.K1.fusionIsBenderGroup_of_stated_psl_two (by norm_num) hcl)

theorem not_bender_suzuki_two {K : Type} [Group K] (hB : ¬ fusionIsBenderGroup K)
    (hv : (TauCeti.LieTypeIndex.suzuki 2).Valid) (e : K ≃* Cat ⟨.suzuki 2, hv⟩) : False :=
  hB (CFSG.QuasithinUnique.K1.fusionIsBenderGroup_of_suzukiModel
    (CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 ⟨hv, ⟨e⟩⟩))

end KSeitz

section Simple


theorem isSimpleGroup_of_isChevSimple_two {S : Type} [Group S] (h : IsChevSimple 2 S) :
    IsSimpleGroup S := by
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases h with ⟨t, n, f, hm⟩ | ⟨e⟩ | h33
  · exact (CFSG.LieType.Catalog.lieModel_finite_simple S t n 2 f hm).2.2
  · obtain ⟨e⟩ := e
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · exact (CFSG.LieType.Catalog.lieModel_finite_simple S .PSU 3 3 1
      (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], h33⟩)).2.2

end Simple

theorem kFactSeitzOutside_holds :
    KFactSeitzOutside := by
  intro A _ _ K E U f hK hB hS hf hf2 hEK hE hEc hUK hU0 hU2 hEU
  haveI hsimp : IsSimpleGroup ↥K := isSimpleGroup_of_isChevSimple_two hK
  have hEcK : Nat.card (E.subgroupOf K) = f ^ 2 := by
    rw [KSeitz.card_subgroupOf hEK]
    exact hEc
  have hU2K : IsPGroup 2 (U.subgroupOf K) := hU2.comap_subtype
  have hU0K : U.subgroupOf K ≠ ⊥ := KSeitz.subgroupOf_ne_bot hUK hU0
  have hZ : Subgroup.center ↥K = ⊥ := KSeitz.center_eq_bot_of_simple hf hf2 hEcK hU2K hU0K
  obtain ⟨SK, P, hP, hEP, hSP⟩ := KSeitz.exists_overgroup_of_holds
    (holds_two_of_isChevSimple_two hK) hU2K hU0K (KSeitz.subgroupOf_le_normalizer hUK hEU)
  have hdvd : ∀ n : ℕ, Nat.card ↥K = n → f ^ 2 ∣ n := fun n hn =>
    hn ▸ hEcK ▸ Subgroup.card_subgroup_dvd_card (E.subgroupOf K)
  rcases hK with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | d | s
    · exact hi.elim
    · exact hi.elim
    ·
      have hchar : d.1.characteristic = 2 := hi
      have hpd : f ≠ d.1.characteristic := by
        rw [hchar]
        exact hf2
      by_cases hsc : EvenScope d.1
      · exact absurd ⟨e⟩ (hS d hsc)
      by_cases hex : IsD2SeitzException f d.1
      · obtain ⟨d0, hv⟩ := d
        change IsD2SeitzException f d0 at hex
        unfold IsD2SeitzException at hex
        rcases hex with ⟨rfl, hcases⟩ | ⟨rfl, hcases⟩
        · rcases hcases with ⟨q, hq2, hq3, rfl⟩ | ⟨q, hq2, hq4, rfl⟩ | ⟨q, hq2, hq1, rfl⟩ |
            ⟨q, hq2, hq1, hB34⟩ | rfl
          · exact (KSeitz.not_bender_A1_eight hB hv hq2 hq3 e).elim
          · exact (hsc (show q.p = 2 ∧ 2 ≤ 2 from ⟨hq2, le_rfl⟩)).elim
          · exact (hsc (show q.p = 2 ∧ 3 ≤ 3 from ⟨hq2, le_rfl⟩)).elim
          · rcases hB34 with rfl | rfl
            · exact (hsc (show q.p = 2 from hq2)).elim
            · exact (hsc (show q.p = 2 from hq2)).elim
          · exact (KSeitz.false_of_tits e hf hf2 hEcK SK hP hEP hSP).elim
        · rcases hcases with rfl | rfl
          · exact (KSeitz.false_of_tits e hf hf2 hEcK SK hP hEP hSP).elim
          · exact (KSeitz.not_bender_suzuki_two hB hv e).elim
      · exact KSeitz.hyperGen_of_seitz CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds d e hZ
          hf hf2 hpd hex hEK hE hEc
    · exact hi.elim
  · rcases CFSG.StandardType.ChevTwo.ambiguousChev_two_cases hi with ⟨h5, rfl⟩ | ⟨h6, rfl⟩ |
      ⟨h8, rfl⟩ | ⟨q, hv, hq, rfl⟩ | ⟨q, hv, hq, rfl⟩
    ·
      have hK60 : Nat.card ↥K = 60 := by
        rw [Nat.card_congr e.toEquiv]
        change Nat.card (alternatingGroup (Fin 5)) = 60
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      exact (KSeitz.not_sq_dvd_sixty hf hf2 (hdvd 60 hK60)).elim
    ·
      have hK360 : Nat.card ↥K = 360 := by
        rw [Nat.card_congr e.toEquiv]
        change Nat.card (alternatingGroup (Fin 6)) = 360
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      have hf3 : f = 3 := KSeitz.eq_three_of_sq_dvd_360 hf hf2 (hdvd 360 hK360)
      subst hf3
      exact (KSeitz.false_of_card_three_sixty hK360 SK (by rw [hEcK]; norm_num) hP hEP hSP).elim
    ·
      have e' : ↥K ≃* alternatingGroup (Fin 8) := e
      have hK20160 : Nat.card ↥K = 20160 := by
        rw [Nat.card_congr e'.toEquiv, KSeitz.card_alt_eight]
      have hf3 : f = 3 := KSeitz.eq_three_of_sq_dvd_20160 hf hf2 (hdvd 20160 hK20160)
      subst hf3
      have hE9 : Nat.card ((E.subgroupOf K).map e'.toMonoidHom) = 9 := by
        rw [Subgroup.card_map_of_injective e'.injective, hEcK]
        norm_num
      exact KSeitz.hyperGen_of_closure_hset hEK
        ((KSeitz.closure_hset_map_eq_top_iff e' 3 (E.subgroupOf K)).mp
          (KSeitz.closure_hset_alt_eight hE9))
    ·
      have hbp : CFSG.Blueprint.LieModel ↥K .PSL (1 + 1) q.p q.exponent :=
        CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
          (CFSG.Models.lieModel_A 1 q hv e)
      have hK168 : Nat.card ↥K = 168 := by
        rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hbp]
        have h7 : q.p ^ q.exponent = 7 := by
          rw [← TauCeti.PrimePower.card_def]
          exact hq
        rw [h7]
        decide
      exact (KSeitz.not_sq_dvd_168 hf hf2 (hdvd 168 hK168)).elim
    ·
      exact (KSeitz.false_of_u33
        (CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two q hv hq e)
        hf hf2 hEcK SK hP hEP hSP).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
