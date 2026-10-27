module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Star
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneSigmaStrongDefs

import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructAux
import CFSG.Adapters.WholeGroupLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76Basic
import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Gen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem IsTwoPrimeComponentIn.isQuasisimple {G : Type} [Group G] [Finite G] {L H : Subgroup G}
    (hTwo : IsTwoPrimeComponentIn L H) (hcore : CFSG.Open.pCoreOf 2 H = ⊥) :
    CFSG.IsQuasisimple ↥L := by
  have hLH : L ≤ H := hTwo.1
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hTwo.2.2.1
  have hcoreH : CFSG.pCore 2 ↥H = ⊥ := by
    have hmap : (CFSG.pCore 2 ↥H).map H.subtype = ⊥ := by
      simpa only [CFSG.Open.pCoreOf] using hcore
    exact Subgroup.map_injective H.subtype_injective
      (by rw [hmap, Subgroup.map_bot])
  have hT : CFSG.Open.IsSubnormal (L.subgroupOf H) ⊤ :=
    CFSG.Open.IsSubnormal.top_iff.mpr hTwo.2.1
  have hcoreSub : CFSG.pCore 2 ↥(L.subgroupOf H) = ⊥ :=
    CFSG.AGLEmbedding.CZeroLift.pCore_eq_bot_of_isSubnormal hT hcoreH
  have hcoreL : CFSG.pCore 2 ↥L = ⊥ := by
    have hmap := CFSG.pCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hLH :
      ↥(L.subgroupOf H) ≃* ↥L)
    rw [hcoreSub, Subgroup.map_bot] at hmap
    exact hmap.symm
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hcoreL).trans QuotientGroup.quotientBot
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {G : Type} [Group G] [Finite G] {M Q H F : Subgroup G} {q : ℕ}

theorem Setting1417.exists_of_two_le_pRank (hC : CStarGen G)
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hstrong : ∀ r ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded r M)
    (hq : q ∈ sigmaSet G M) {H : Subgroup G} (hH : H ≠ ⊤) (hHM : ¬ H ≤ M)
    (hrank : 2 ≤ CFSG.Open.pRank q (M ⊓ H)) :
    ∃ Q F : Subgroup G, Setting1417 G M Q H F q := by
  classical
  have hqM : q ∈ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa only [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hq
  haveI : Fact q.Prime := ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime q hq.1⟩
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf q (H ⊓ M)
  have hQrank : 2 ≤ CFSG.Open.pRank q Q := by
    rw [CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow
      (CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime q hq.1) hQ]
    simpa only [inf_comm] using hrank
  obtain ⟨F, hFQ, hFea, hFcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := q) (k := 2) hQrank
  have hFM : F ≤ M := hFQ.trans (hQ.le.trans inf_le_right)
  have hΓ : CFSG.Open.rankThreeGamma 1 q F ≤ M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.rankThreeGamma_self_le
      (hstrong q hq) hFM hFea.isPGroup
  have hsigma : (CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M).Nonempty := ⟨q, hqM⟩
  have hnine : AGL81C.NineSettingGen G M q Q H F 2 :=
    { setting := ⟨hC, hM, hsigma⟩
      mem_Q := AGL81C.mem_QSet_iff.mpr ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime q hq.1,
        CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd q hq.1,
        hQ.le.trans inf_le_right, hQ.isPGroup, Or.inr ⟨F, hFQ, hFea, hFcard, hΓ⟩⟩
      mem_H := AGL81C.mem_HFam_iff.mpr ⟨hH, hQ.le.trans inf_le_left, hHM⟩
      stdE := ⟨Or.inl rfl, hFQ, hFea, hFcard, hΓ⟩ }
  have hSylowH : CFSG.ABGLocalTools.IsSylowOf q Q H :=
    (hnine.isSylowOf_of_isSylowOf_inf hqM hQ).1
  exact ⟨Q, F, ⟨hC, hM, hstrong, hq, hnine, hSylowH, hQ⟩⟩

theorem Setting1417.isQuasisimple_kSub_of_ne_three (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong) (hq3 : q ≠ 3) :
    CFSG.IsQuasisimple ↥(AGL81C.kSub q M H) := by
  obtain ⟨L, hL, hLM, hk⟩ := s.exists_eq_kSub h1
  have hTwo := h2 G M Q H F q s hq3 L hL hLM
  rw [← hk] at hTwo
  exact IsTwoPrimeComponentIn.isQuasisimple hTwo s.pCoreOf_two_eq_bot

theorem Setting1417.centralizer_kStar_eq_bot (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) :
    Subgroup.centralizer (AGL81C.kStar q M H : Set (AGL81C.StarGroup q H)) = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  haveI : (AGL81C.kStar q M H).Normal := s.kStar_normal h1
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  haveI hOn : O.Normal := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).Normal
    infer_instance
  let π : ↥H →* AGL81C.StarGroup q H := QuotientGroup.mk' O
  let C : Subgroup (AGL81C.StarGroup q H) :=
    Subgroup.centralizer (AGL81C.kStar q M H : Set (AGL81C.StarGroup q H))
  have hxsub : (AGL81C.xSub q M H).subgroupOf H = C.comap π := by
    dsimp only [AGL81C.xSub, CFSG.AGLEmbedding.d1PlusCore, C, π, O]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hxH : AGL81C.xSub q M H ≤ H := Subgroup.map_subtype_le _
  have hxNormal : ((AGL81C.xSub q M H).subgroupOf H).Normal := by
    rw [hxsub]
    exact Subgroup.normal_centralizer.comap π
  have hxO : (AGL81C.xSub q M H).subgroupOf H ≤ O := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_coprime_le_primeComplementCore
      q _ hxNormal ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxH).toEquiv]
    exact (s.kStructure h1).2.2.1
  have hCeq : C = Subgroup.map π ((AGL81C.xSub q M H).subgroupOf H) := by
    rw [hxsub, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)]
  change C = ⊥
  rw [hCeq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact hxO

private theorem isPerfect_kStar (s : Setting1417 G M Q H F q) (h1 : NineFourTwoSigmaGen) :
    Group.IsPerfect ↥(AGL81C.kStar q M H) := by
  classical
  let K : Subgroup G := AGL81C.kSub q M H
  let π : ↥H →* AGL81C.StarGroup q H :=
    QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q)
  let g : ↥K →* AGL81C.StarGroup q H := π.comp (Subgroup.inclusion (AGL81C.kSub_le q M H))
  have hmem : ∀ x : ↥K, g x ∈ AGL81C.kStar q M H := by
    intro x
    rw [AGL81C.kStar_eq_starImg]
    exact Subgroup.mem_map.mpr ⟨⟨(x : G), AGL81C.kSub_le q M H x.2⟩,
      Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  let f : ↥K →* ↥(AGL81C.kStar q M H) := g.codRestrict (AGL81C.kStar q M H) hmem
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : AGL81C.StarGroup q H) ∈ AGL81C.starImg q H K := by
      rw [← AGL81C.kStar_eq_starImg]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩, ?_⟩
    apply Subtype.ext
    simp only [f, g, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
    change π (⟨(z : G), AGL81C.kSub_le q M H
      (Subgroup.mem_subgroupOf.mp hz)⟩ : ↥H) = (y : AGL81C.StarGroup q H)
    rw [show (⟨(z : G), AGL81C.kSub_le q M H
      (Subgroup.mem_subgroupOf.mp hz)⟩ : ↥H) = z from Subtype.ext rfl]
    exact hzy
  haveI : Group.IsPerfect ↥K := s.isPerfect_kSub h1
  exact Group.IsPerfect.ofSurjective hsurj

theorem Setting1417.generalizedFitting_eq_kStar (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) :
    CFSG.generalizedFitting (AGL81C.StarGroup q H) = AGL81C.kStar q M H := by
  haveI : (AGL81C.kStar q M H).Normal := s.kStar_normal h1
  haveI : IsSimpleGroup ↥(AGL81C.kStar q M H) := (s.kStructure h1).2.2.2.1
  haveI : Group.IsPerfect ↥(AGL81C.kStar q M H) := isPerfect_kStar s h1
  have hnc : ∃ x y : ↥(AGL81C.kStar q M H), x * y ≠ y * x := by
    by_contra h
    have hcomm : IsMulCommutative ↥(AGL81C.kStar q M H) :=
      ⟨⟨fun x y => by
        by_contra hxy
        exact h ⟨x, y, hxy⟩⟩⟩
    exact Group.IsPerfect.not_isMulCommutative ↥(AGL81C.kStar q M H) hcomm
  exact CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot
    (AGL81C.kStar q M H) hnc (s.centralizer_kStar_eq_bot h1)

private theorem kStar_ne_bot (s : Setting1417 G M Q H F q) (h1 : NineFourTwoSigmaGen) :
    AGL81C.kStar q M H ≠ ⊥ := by
  haveI : IsSimpleGroup ↥(AGL81C.kStar q M H) := (s.kStructure h1).2.2.2.1
  exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance

private theorem starImg_eq_bot_of_le_relPPrimeCore (s : Setting1417 G M Q H F q)
    {K : Subgroup G} (hKH : K ≤ H) (hKO : K ≤ CFSG.Open.relPPrimeCore q H) :
    AGL81C.starImg q H K = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  have hOeq : CFSG.Open.relPPrimeCore q H = O.map H.subtype := by
    dsimp only [O]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
      s.qPrime H
  have hker : K.subgroupOf H ≤ O := by
    intro x hx
    have hxO : (x : G) ∈ O.map H.subtype := by
      rw [← hOeq]
      exact hKO (Subgroup.mem_subgroupOf.mp hx)
    rwa [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective O,
      Subgroup.mem_comap]
  rw [AGL81C.starImg, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact hker

private theorem commutator_kSub_subgroupOf_normal (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) :
    (⁅CFSG.Open.relPPrimeCore q H, AGL81C.kSub q M H⁆.subgroupOf
      (AGL81C.kSub q M H)).Normal := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let K : Subgroup G := AGL81C.kSub q M H
  let O : Subgroup G := CFSG.Open.relPPrimeCore q H
  have hKH : K ≤ H := AGL81C.kSub_le q M H
  have hOH : O ≤ H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
      (p := q) H
  have hKn : (K.subgroupOf H).Normal := (s.kStructure h1).1
  have hOn : (O.subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      s.qPrime H
  have hCnorm : (⁅O.subgroupOf H, K.subgroupOf H⁆).Normal :=
    Subgroup.commutator_normal (O.subgroupOf H) (K.subgroupOf H)
  have hmap : (⁅O.subgroupOf H, K.subgroupOf H⁆).map H.subtype = ⁅O, K⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hOH,
      Subgroup.map_subgroupOf_eq_of_le hKH]
  have hNsub : (⁅O, K⁆).subgroupOf H = ⁅O.subgroupOf H, K.subgroupOf H⁆ := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hNH : ⁅O, K⁆ ≤ H := by
    rw [← hmap]
    exact Subgroup.map_subtype_le _
  have hNg : H ≤ Subgroup.normalizer ((⁅O, K⁆ : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp
      (by rw [hNsub]; exact hCnorm)
  have hKnorm : K ≤ Subgroup.normalizer ((⁅O, K⁆ : Subgroup G) : Set G) := hKH.trans hNg
  have hNleK : ⁅O, K⁆ ≤ K := by
    refine (Subgroup.le_normalizer_iff_commutator_le_right
      (H := O) (K := K)).mp ?_
    exact hOH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNleK).mpr hKnorm

theorem Setting1417.relPPrimeCore_le_centralizer_kSub (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong) (hq3 : q ≠ 3) :
    CFSG.Open.relPPrimeCore q H ≤ Subgroup.centralizer (AGL81C.kSub q M H : Set G) := by
  classical
  let K : Subgroup G := AGL81C.kSub q M H
  let O : Subgroup G := CFSG.Open.relPPrimeCore q H
  have hq : CFSG.IsQuasisimple ↥K := s.isQuasisimple_kSub_of_ne_three h1 h2 hq3
  have hNn : (⁅O, K⁆.subgroupOf K).Normal := commutator_kSub_subgroupOf_normal s h1
  have hNleO : ⁅O, K⁆ ≤ O := by
    refine (Subgroup.le_normalizer_iff_commutator_le_left
      (H := K) (K := O)).mp ?_
    exact (AGL81C.kSub_le q M H).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
          (p := q) H)).mp
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
          s.qPrime H))
  have hNleK : ⁅O, K⁆ ≤ K := by
    refine (Subgroup.le_normalizer_iff_commutator_le_right
      (H := O) (K := K)).mp ?_
    exact (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
      (p := q) H).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (AGL81C.kSub_le q M H)).mp
        (s.kStructure h1).1)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with htop | hcenter
  · have hKleN : K ≤ ⁅O, K⁆ := Subgroup.subgroupOf_eq_top.mp htop
    have hKleO : K ≤ O := hKleN.trans hNleO
    have hbot : AGL81C.kStar q M H = ⊥ := by
      rw [AGL81C.kStar_eq_starImg]
      exact starImg_eq_bot_of_le_relPPrimeCore s (AGL81C.kSub_le q M H) hKleO
    exact absurd hbot (kStar_ne_bot s h1)
  · have hNcent : ⁅O, K⁆ ≤ Subgroup.centralizer (K : Set G) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hnk : (⟨n, hNleK hn⟩ : ↥K) ∈ Subgroup.center ↥K :=
        hcenter (Subgroup.mem_subgroupOf.mpr hn)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hnk ⟨k, hk⟩)
    have hcomm : ⁅K, O⁆ = ⊥ := by
      refine CFSG.GH74.GLS.Stage2.Bender.Thm2.L915.commutator_eq_bot_of_commutator_le_centralizer
        (P := K) (X := O) (s.isPerfect_kSub h1) ?_
      rwa [Subgroup.commutator_comm]
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

theorem Setting1417.pRank_kStar_le (s : Setting1417 G M Q H F q) (h1 : NineFourTwoSigmaGen)
    {R : Subgroup G} (hKR : AGL81C.kSub q M H ≤ R) :
    CFSG.Open.pRank q (⊤ : Subgroup ↥(AGL81C.kStar q M H)) ≤ CFSG.Open.pRank q (M ⊓ R) := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let K : Subgroup G := AGL81C.kSub q M H
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  haveI hOn : O.Normal := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).Normal
    infer_instance
  have hKH : K ≤ H := AGL81C.kSub_le q M H
  have hKn : (K.subgroupOf H).Normal := (s.kStructure h1).1
  have hKnormH : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKn
  have hSyl : CFSG.ABGLocalTools.IsSylowOf q (Q ⊓ K) K :=
    s.sylowH.inf_of_le_normalizer hKH hKnormH
  have hmap : CFSG.Open.pRank q (AGL81C.kStar q M H) = CFSG.Open.pRank q K := by
    rw [AGL81C.kStar_eq_starImg, AGL81C.starImg,
      CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype s.qPrime O
        (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := ↥H) q)
        (K.subgroupOf H)]
    rw [Subgroup.map_subgroupOf_eq_of_le hKH]
  calc CFSG.Open.pRank q (⊤ : Subgroup ↥(AGL81C.kStar q M H))
      = CFSG.Open.pRank q (AGL81C.kStar q M H) :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (AGL81C.kStar q M H)).symm
    _ = CFSG.Open.pRank q K := hmap
    _ = CFSG.Open.pRank q (Q ⊓ K) :=
        (CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow s.qPrime hSyl).symm
    _ ≤ CFSG.Open.pRank q (M ⊓ R) :=
        CFSG.SectionRank.pRank_mono s.qPrime.one_lt
          (le_inf (inf_le_left.trans s.Q_le_M) (inf_le_right.trans hKR))

theorem Setting1417.le_relPPrimeCore_of_not_three_dvd (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) (h3 : ¬ 3 ∣ Nat.card (MulAut ↥(AGL81C.kStar q M H)))
    {J : Subgroup G} (hJH : J ≤ H) (hJ : IsPGroup 3 J) :
    J ≤ CFSG.Open.relPPrimeCore q H := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (AGL81C.kStar q M H).Normal := s.kStar_normal h1
  have hdvd : Nat.card (AGL81C.StarGroup q H) ∣
      Nat.card (MulAut ↥(AGL81C.kStar q M H)) :=
    CFSG.OddStandard.Seitz77.card_dvd_mulAut (s.centralizer_kStar_eq_bot h1)
  have hnotdvd : ¬ 3 ∣ Nat.card (AGL81C.StarGroup q H) :=
    fun h => h3 (h.trans hdvd)
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  haveI hOn : O.Normal := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).Normal
    infer_instance
  let π : ↥H →* AGL81C.StarGroup q H := QuotientGroup.mk' O
  have hJstar3 : IsPGroup 3 (AGL81C.starImg q H J) :=
    (hJ.comap_subtype (K := H)).map π
  have hnot3img : ¬ 3 ∣ Nat.card ↥(AGL81C.starImg q H J) :=
    fun h => hnotdvd (h.trans (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨n, hn⟩ := hJstar3.exists_card_eq
  have hn0 : n = 0 := by
    cases n with
    | zero => rfl
    | succ m =>
        exact absurd ⟨3 ^ m, by rw [hn, pow_succ, mul_comm]⟩ hnot3img
  have hbot : AGL81C.starImg q H J = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
  exact s.nine.le_relPPrimeCore_of_starImg_eq_bot hJH hbot

private theorem pPrimeCore_inf_normal (s : Setting1417 G M Q H F q) :
    (((CFSG.pPrimeCore 3 ↥M).map M.subtype ⊓ H).subgroupOf (H ⊓ M)).Normal := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let Ymap : Subgroup G := Y.map M.subtype
  let X : Subgroup G := Ymap ⊓ H
  have hYM : Ymap ≤ M := Subgroup.map_subtype_le Y
  have hXM : X ≤ M := inf_le_left.trans hYM
  have hXH : X ≤ H := inf_le_right
  have hXHM : X ≤ H ⊓ M := le_inf hXH hXM
  have hYsub : Ymap.subgroupOf M = Y :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective Y
  have hYmapNormal : (Ymap.subgroupOf M).Normal := by
    rw [hYsub]
    exact CFSG.pPrimeCore_normal
  have hYnorm : M ≤ Subgroup.normalizer (Ymap : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mp hYmapNormal
  have hXnorm : H ⊓ M ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer_inf (A := H ⊓ M) (H := Ymap) (K := H)
      (inf_le_right.trans hYnorm) (inf_le_left.trans Subgroup.le_normalizer)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXHM).mpr hXnorm

private theorem exists_surjective_map_starImg_inf (s : Setting1417 G M Q H F q)
    (X : Subgroup G) (hXHM : X ≤ H ⊓ M) :
    ∃ f : ↥(H ⊓ M) →* ↥(AGL81C.starImg q H (H ⊓ M)),
      Function.Surjective f ∧
      (X.subgroupOf (H ⊓ M)).map f =
        (AGL81C.starImg q H X).subgroupOf (AGL81C.starImg q H (H ⊓ M)) := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  haveI hOn : O.Normal := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).Normal
    infer_instance
  let π : ↥H →* AGL81C.StarGroup q H := QuotientGroup.mk' O
  let N : Subgroup (AGL81C.StarGroup q H) := AGL81C.starImg q H (H ⊓ M)
  let ρ : ↥(H ⊓ M) →* AGL81C.StarGroup q H :=
    π.comp (Subgroup.inclusion (inf_le_left : H ⊓ M ≤ H))
  have hρmem : ∀ x : ↥(H ⊓ M), ρ x ∈ N := by
    intro x
    dsimp only [N]
    rw [AGL81C.starImg]
    exact Subgroup.mem_map.mpr ⟨⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩,
      Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  let f : ↥(H ⊓ M) →* ↥N := ρ.codRestrict N hρmem
  have hfsurj : Function.Surjective f := by
    intro y
    have hy : (y : AGL81C.StarGroup q H) ∈ N := y.2
    dsimp only [N] at hy
    change (y : AGL81C.StarGroup q H) ∈ Subgroup.map π ((H ⊓ M).subgroupOf H) at hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩, Subtype.ext ?_⟩
    simp only [f, ρ, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
    change π (⟨(z : G), (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).1⟩ : ↥H) =
      (y : AGL81C.StarGroup q H)
    rw [show (⟨(z : G), (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).1⟩ : ↥H) = z
      from Subtype.ext rfl]
    exact hzy
  refine ⟨f, hfsurj, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf, AGL81C.starImg]
    exact Subgroup.mem_map.mpr ⟨⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), rfl⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf, AGL81C.starImg] at hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    have hzX : (z : G) ∈ X := Subgroup.mem_subgroupOf.mp hz
    refine ⟨⟨(z : G), hXHM hzX⟩, Subgroup.mem_subgroupOf.mpr hzX, Subtype.ext ?_⟩
    simp only [f, ρ, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
    change π (⟨(z : G), (Subgroup.mem_inf.mp (hXHM hzX)).1⟩ : ↥H) =
      (y : AGL81C.StarGroup q H)
    rw [show (⟨(z : G), (Subgroup.mem_inf.mp (hXHM hzX)).1⟩ : ↥H) = z from Subtype.ext rfl]
    exact hzy

private theorem starImg_inf_pPrimeCore_subgroupOf_normal (s : Setting1417 G M Q H F q) :
    ((AGL81C.starImg q H ((CFSG.pPrimeCore 3 ↥M).map M.subtype ⊓ H)).subgroupOf
      (AGL81C.starImg q H (H ⊓ M))).Normal := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X : Subgroup G := (CFSG.pPrimeCore 3 ↥M).map M.subtype ⊓ H
  have hXHM : X ≤ H ⊓ M :=
    le_inf inf_le_right
      (inf_le_left.trans (Subgroup.map_subtype_le (CFSG.pPrimeCore 3 ↥M)))
  obtain ⟨f, hfsurj, himg_eq⟩ := exists_surjective_map_starImg_inf s X hXHM
  have hXnorm : (X.subgroupOf (H ⊓ M)).Normal := pPrimeCore_inf_normal s
  have himg_normal : ((X.subgroupOf (H ⊓ M)).map f).Normal :=
    Subgroup.Normal.map hXnorm f hfsurj
  have hXstar_normal :
      ((AGL81C.starImg q H X).subgroupOf (AGL81C.starImg q H (H ⊓ M))).Normal := by
    rw [← himg_eq]
    exact himg_normal
  simpa only [X] using hXstar_normal

theorem Setting1417.not_dvd_card_of_pPrimeCore_starImg_eq_bot (s : Setting1417 G M Q H F q)
    (hO : CFSG.pPrimeCore 3 ↥(AGL81C.starImg q H (H ⊓ M)) = ⊥) :
    ¬ q ∣ Nat.card ↥((CFSG.pPrimeCore 3 ↥M).map M.subtype ⊓ H) := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let Ymap : Subgroup G := Y.map M.subtype
  let X : Subgroup G := Ymap ⊓ H
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  haveI hOn : O.Normal := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).Normal
    infer_instance
  let π : ↥H →* AGL81C.StarGroup q H := QuotientGroup.mk' O
  let N : Subgroup (AGL81C.StarGroup q H) := AGL81C.starImg q H (H ⊓ M)
  have hXH : X ≤ H := inf_le_right
  have hXHM : X ≤ H ⊓ M := le_inf hXH (inf_le_left.trans (Subgroup.map_subtype_le Y))
  have hXN : AGL81C.starImg q H X ≤ N := by
    dsimp only [N]
    rw [AGL81C.starImg, AGL81C.starImg]
    exact Subgroup.map_mono (Subgroup.comap_mono hXHM)
  have hXstar_normal : ((AGL81C.starImg q H X).subgroupOf N).Normal := by
    simpa only [X, N] using starImg_inf_pPrimeCore_subgroupOf_normal s
  have hYcop : Nat.Coprime 3 (Nat.card ↥Ymap) := by
    rw [show Nat.card ↥Ymap = Nat.card ↥Y from
      Subgroup.card_map_of_injective M.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hXcop : Nat.Coprime 3 (Nat.card ↥X) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hYcop
  have hXsubCop : Nat.Coprime 3 (Nat.card ↥(X.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]
    exact hXcop
  have hXstarCop : Nat.Coprime 3 (Nat.card ↥(AGL81C.starImg q H X)) := by
    have h := Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (X.subgroupOf H) π) hXsubCop
    simpa only [AGL81C.starImg] using h
  have hXstarSubCop : Nat.Coprime 3 (Nat.card ↥((AGL81C.starImg q H X).subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv]
    exact hXstarCop
  have hYle : (AGL81C.starImg q H X).subgroupOf N ≤ CFSG.pPrimeCore 3 ↥N :=
    le_sSup ⟨hXstar_normal, hXstarSubCop⟩
  have hYbot : (AGL81C.starImg q H X).subgroupOf N = ⊥ := by
    rw [hO] at hYle
    exact le_bot_iff.mp hYle
  have hXbot : AGL81C.starImg q H X = ⊥ :=
    (Subgroup.subgroupOf_eq_bot.mp hYbot).eq_bot_of_le hXN
  have hXO : X ≤ CFSG.Open.relPPrimeCore q H :=
    s.nine.le_relPPrimeCore_of_starImg_eq_bot hXH hXbot
  change ¬ q ∣ Nat.card ↥X
  intro hdiv
  have hnot : ¬ q ∣ Nat.card (CFSG.Open.relPPrimeCore q H) :=
    (Nat.Prime.coprime_iff_not_dvd s.qPrime).mp
      (coprime_card_relPPrimeCore s.qPrime H)
  exact hnot (hdiv.trans (Subgroup.card_dvd_of_le hXO))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217
