module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Setup
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Inputs

import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.GH74.GLS.LU.Local.Core
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76Basic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ} {k : ℕ}

namespace NineCore

theorem le_iff_starImg_le (h : NineCore G M p Q H E k) {A : Subgroup G} (hAH : A ≤ H) :
    A ≤ M ↔ starImg p H A ≤ starImg p H M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  constructor
  · intro hAM
    exact Subgroup.map_mono (Subgroup.comap_mono hAM)
  · intro hAM
    have h1 : A.subgroupOf H ≤ M.subgroupOf H ⊔ CFSG.pPrimeCore p ↥H := by
      have h2 : (A.subgroupOf H).map
            (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ≤
          (M.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) := hAM
      have h3 := Subgroup.map_le_iff_le_comap.mp h2
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h3
    calc A = (A.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hAH).symm
      _ ≤ (M.subgroupOf H ⊔ CFSG.pPrimeCore p ↥H).map H.subtype := Subgroup.map_mono h1
      _ = (M.subgroupOf H).map H.subtype ⊔ (CFSG.pPrimeCore p ↥H).map H.subtype := by
            rw [Subgroup.map_sup]
      _ ≤ M := by
            refine sup_le ?_ ?_
            · rw [Subgroup.subgroupOf_map_subtype]
              exact inf_le_left
            · change (primeComplementCore (G := ↥H) p).map H.subtype ≤ M
              rw [← CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
                h.prime H]
              exact h.relPPrimeCore_le

end NineCore

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M Q H F : Subgroup G} {q : ℕ}

theorem Setting1417.isSylowOf_starImg (s : Setting1417 G M Q H F q)
    (hQ : CFSG.ABGLocalTools.IsSylowOf q Q H) :
    CFSG.ABGLocalTools.IsSylowOf q (starImg q H Q) ⊤ := by
  simpa only [starImg_self] using
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.isSylowOf_starImg s.qPrime (le_rfl : H ≤ H) hQ

private theorem pCore_le_starImg_of_isSylowOf (s : Setting1417 G M Q H F q)
    (hQ : CFSG.ABGLocalTools.IsSylowOf q Q H) :
    CFSG.pCore q (StarGroup q H) ≤ starImg q H Q := by
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  refine CFSG.ABGLocalTools.pCore_le_of_not_dvd_index (p := q) ?_
  have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp (s.isSylowOf_starImg hQ)).2.2
  simpa [Subgroup.relIndex_top_right] using h

private theorem not_le_of_dvd_card (s : Setting1417 G M Q H F q) {J : Subgroup G}
    (hJH : J ≤ H) (hJM : J ≤ M) (hJsub_norm : (J.subgroupOf H).Normal)
    (hqJ : q ∣ Nat.card J) : False := by
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf q J
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hpos : 0 < (Nat.card J).factorization q :=
      s.qPrime.factorization_pos_of_dvd (Nat.card_pos.ne') hqJ
    have hgt : 1 < Nat.card R := by
      rw [hR.card_eq]
      exact Nat.one_lt_pow (Nat.ne_of_gt hpos) s.qPrime.one_lt
    rw [hbot, Subgroup.card_bot] at hgt
    exact Nat.lt_irrefl 1 hgt
  have hJHnorm : H ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mp hJsub_norm
  have hfr : H ≤ J ⊔ Subgroup.normalizer (R : Set G) :=
    CFSG.RankThree.PartTwo.Sec18.le_sup_normalizer_of_isSylowOf hR hJHnorm
  have hRnorm : Subgroup.normalizer (R : Set G) ≤ M :=
    s.normalizer_le_of_isPGroup hRne hR.isPGroup (hR.le.trans hJM)
  exact s.not_le (hfr.trans (sup_le hJM hRnorm))

private theorem not_le_of_not_dvd_card (s : Setting1417 G M Q H F q) {J : Subgroup G}
    (hJH : J ≤ H)
    (hJsub : J.subgroupOf H =
      (CFSG.pCore q (StarGroup q H) ⊔ CFSG.layer (StarGroup q H)).comap
        (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
          (G := ↥H) q)))
    (hstarJ : starImg q H J =
      CFSG.pCore q (StarGroup q H) ⊔ CFSG.layer (StarGroup q H))
    (hJsub_norm : (J.subgroupOf H).Normal) (hqJ : ¬ q ∣ Nat.card J) : False := by
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  haveI hOn : O.Normal := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).Normal
    infer_instance
  have hcop : Nat.Coprime q (Nat.card J) := (s.qPrime.coprime_iff_not_dvd).mpr hqJ
  have hcop' : Nat.Coprime q (Nat.card (J.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJH).toEquiv]
  have hJsubO : J.subgroupOf H ≤ O :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_coprime_le_primeComplementCore q
      (J.subgroupOf H) hJsub_norm hcop'
  have hJstar_bot : (CFSG.pCore q (StarGroup q H) ⊔ CFSG.layer (StarGroup q H)) = ⊥ := by
    rw [← hstarJ, starImg, hJsub, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk',
      ← hJsub]
    exact hJsubO
  have hset : ((CFSG.pCore q (StarGroup q H) ⊔ CFSG.layer (StarGroup q H) :
      Subgroup (StarGroup q H)) : Set (StarGroup q H)) =
      ((⊥ : Subgroup (StarGroup q H)) : Set (StarGroup q H)) := by
    rw [hJstar_bot]
  have htopcore : (⊤ : Subgroup (StarGroup q H)) ≤ CFSG.pCore q (StarGroup q H) := by
    have hcent : (⊤ : Subgroup (StarGroup q H)) ≤
        Subgroup.centralizer ((⊥ : Subgroup (StarGroup q H)) : Set (StarGroup q H)) := by
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      subst y
      simp
    have hcore := CFSG.LocalAnalysis.RankThreeUC.AGL81C.centralizer_pCore_sup_layer_le
      s.qPrime H
    rw [hset] at hcore
    exact hcent.trans hcore
  have hbot_top : (⊥ : Subgroup (StarGroup q H)) = ⊤ := by
    have hpCore : CFSG.pCore q (StarGroup q H) = ⊤ := le_antisymm le_top htopcore
    have hsup : (CFSG.pCore q (StarGroup q H) ⊔ CFSG.layer (StarGroup q H)) = ⊤ := by
      rw [hpCore, top_sup_eq]
    rw [← hJstar_bot, hsup]
  have hOtop : O = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← QuotientGroup.eq_one_iff (N := O)]
    have hx : QuotientGroup.mk' O x ∈ (⊥ : Subgroup (StarGroup q H)) := by
      rw [hbot_top]
      exact Subgroup.mem_top _
    simpa using hx
  have hOtop' : CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
      (G := ↥H) q = ⊤ := hOtop
  have htop : CFSG.Open.relPPrimeCore q H = H := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
      s.qPrime H, hOtop', Subgroup.map_top, Subgroup.range_subtype]
  exact s.not_le (by rw [← htop]; exact s.nine.relPPrimeCore_le)

theorem Setting1417.not_pLayerIn_le (s : Setting1417 G M Q H F q) :
    ¬ AGL81C.pLayerIn q H ≤ M := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  intro hL
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  haveI hOn : O.Normal := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).Normal
    infer_instance
  let Jstar : Subgroup (StarGroup q H) :=
    CFSG.pCore q (StarGroup q H) ⊔ CFSG.layer (StarGroup q H)
  have hJstar_normal : Jstar.Normal := by
    haveI : (CFSG.pCore q (StarGroup q H)).Normal := inferInstance
    haveI hchar : (CFSG.layer (StarGroup q H)).Characteristic :=
      CFSG.LocalCores.layer_characteristic
    haveI : (CFSG.layer (StarGroup q H)).Normal := inferInstance
    dsimp only [Jstar]
    infer_instance
  let J : Subgroup G := (Jstar.comap (QuotientGroup.mk' O)).map H.subtype
  have hJH : J ≤ H := Subgroup.map_subtype_le _
  have hJsub : J.subgroupOf H = Jstar.comap (QuotientGroup.mk' O) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hstarJ : starImg q H J = Jstar := by
    rw [starImg, hJsub,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)]
  have hQbar_le : starImg q H Q ≤ starImg q H M :=
    Subgroup.map_mono (Subgroup.comap_mono s.Q_le_M)
  have hlayer_le : CFSG.layer (StarGroup q H) ≤ starImg q H M := by
    rw [← starImg_pLayerIn s.qPrime]
    exact Subgroup.map_mono (Subgroup.comap_mono hL)
  have hJstar_le : Jstar ≤ starImg q H M := by
    dsimp only [Jstar]
    exact sup_le ((pCore_le_starImg_of_isSylowOf s s.sylowH).trans hQbar_le) hlayer_le
  have hJM : J ≤ M :=
    (s.nine.toCore.le_iff_starImg_le hJH).mpr (by rw [hstarJ]; exact hJstar_le)
  have hJsub_norm : (J.subgroupOf H).Normal := by
    rw [hJsub]
    exact hJstar_normal.comap (QuotientGroup.mk' O)
  by_cases hqJ : q ∣ Nat.card J
  · exact not_le_of_dvd_card s hJH hJM hJsub_norm hqJ
  · exact not_le_of_not_dvd_card s hJH (by simpa only [O, Jstar] using hJsub)
      (by simpa only [O, Jstar] using hstarJ) hJsub_norm hqJ

theorem Setting1417.kStructure (s : Setting1417 G M Q H F q) (h1 : NineFourTwoSigmaGen) :
    ((AGL81C.kSub q M H).subgroupOf H).Normal ∧ AGL81C.xSub q M H ≤ M ∧
      Nat.Coprime q (Nat.card (AGL81C.xSub q M H)) ∧
      CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q ↥(AGL81C.kStar q M H) := by
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  refine h1 G M Q H F q s.nine s.hq s.not_pLayerIn_le ?_
  intro P hP
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.rankThreeGamma_self_le s.strongQ
    (hP.le.trans inf_le_right) hP.isPGroup

private theorem starImg_eq_kStar_of_isPComponent (s : Setting1417 G M Q H F q)
    (hKsimple : IsSimpleGroup ↥(AGL81C.kStar q M H)) {L : Subgroup G}
    (hL : AGL81C.IsPComponentIn q L H) (hLM : ¬ L ≤ M) :
    AGL81C.starImg q H L = AGL81C.kStar q M H := by
  have hLk : L ≤ AGL81C.kSub q M H := by
    unfold AGL81C.kSub
    rw [if_neg s.not_pLayerIn_le]
    exact le_sSup ⟨hL, hLM⟩
  have hLle : AGL81C.starImg q H L ≤ AGL81C.kStar q M H := by
    rw [AGL81C.kStar_eq_starImg]
    exact Subgroup.map_mono (Subgroup.comap_mono hLk)
  have hLsub : (AGL81C.starImg q H L).IsSubnormal :=
    (AGL81C.isComponent_starImg hL).2
  have hsub : ((AGL81C.starImg q H L).subgroupOf (AGL81C.kStar q M H)).IsSubnormal :=
    hLsub.subgroupOf
  have hne : AGL81C.starImg q H L ≠ ⊥ := by
    intro hbot
    exact (Subgroup.nontrivial_iff_ne_bot _).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial (AGL81C.isComponent_starImg hL).1) hbot
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hKsimple hsub with hbot | htop
  · exfalso
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hLle, hbot, Subgroup.map_bot]
  · exact le_antisymm hLle (Subgroup.subgroupOf_eq_top.mp htop)

theorem Setting1417.exists_eq_kSub (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) :
    ∃ L : Subgroup G, AGL81C.IsPComponentIn q L H ∧ ¬ L ≤ M ∧ AGL81C.kSub q M H = L := by
  classical
  have hKlist := (s.kStructure h1).2.2.2
  have hKsimple : IsSimpleGroup ↥(AGL81C.kStar q M H) := hKlist.1
  have hpLayer_eq : AGL81C.pLayerIn q H =
      sSup {L : Subgroup G | AGL81C.IsPComponentIn q L H} := by
    refine le_antisymm ?_ (sSup_le fun L hL => AGL81C.le_pLayerIn hL)
    rw [AGL81C.pLayerIn, Subgroup.map_le_iff_le_comap, CFSG.pLayer]
    refine sSup_le fun L hL => ?_
    exact Subgroup.map_le_iff_le_comap.mp
      (le_sSup (AGL81C.isPComponentIn_map_subtype hL))
  have hex : ∃ L : Subgroup G, AGL81C.IsPComponentIn q L H ∧ ¬ L ≤ M := by
    by_contra h
    exact s.not_pLayerIn_le (by
      rw [hpLayer_eq]
      refine sSup_le fun L hL => ?_
      by_contra hLM
      exact h ⟨L, hL, hLM⟩)
  obtain ⟨L, hL, hLM⟩ := hex
  have hkdef : AGL81C.kSub q M H =
      sSup {Y : Subgroup G | AGL81C.IsPComponentIn q Y H ∧ ¬ Y ≤ M} := by
    unfold AGL81C.kSub
    rw [if_neg s.not_pLayerIn_le]
  have hk : AGL81C.kSub q M H = L := by
    rw [hkdef]
    refine le_antisymm ?_ (le_sSup ⟨hL, hLM⟩)
    refine sSup_le ?_
    rintro Y ⟨hY, hYM⟩
    have hYeq : Y = L :=
      AGL81C.eq_of_starImg_eq s.qPrime hY hL (by
        rw [starImg_eq_kStar_of_isPComponent s hKsimple hY hYM,
          starImg_eq_kStar_of_isPComponent s hKsimple hL hLM])
    rw [hYeq]
  exact ⟨L, hL, hLM, hk⟩

theorem Setting1417.isPerfect_kSub (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) : Group.IsPerfect ↥(AGL81C.kSub q M H) := by
  obtain ⟨L, hL, -, hk⟩ := s.exists_eq_kSub h1
  rw [hk]
  exact AGL81C.IsPComponentIn.isPerfect s.qPrime hL

theorem Setting1417.kSub_not_le (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) : ¬ AGL81C.kSub q M H ≤ M := by
  obtain ⟨L, -, hLM, hk⟩ := s.exists_eq_kSub h1
  rwa [hk]

theorem Setting1417.le_centralizer_kSub (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) {A : Subgroup G} [IsCyclic A]
    (hHA : H ≤ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.centralizer (AGL81C.kSub q M H : Set G) := by
  have hcomm : ⁅AGL81C.kSub q M H, AGL81C.kSub q M H⁆ = AGL81C.kSub q M H :=
    (Subgroup.isPerfect_iff (H := AGL81C.kSub q M H)).mp (s.isPerfect_kSub h1)
  have hKN : AGL81C.kSub q M H ≤ Subgroup.normalizer (A : Set G) :=
    (AGL81C.kSub_le q M H).trans hHA
  exact (Subgroup.le_centralizer_iff).mpr
    (CFSG.GH74.GLS.LU.Local.perfect_le_centralizer_of_cyclic hcomm hKN)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217
