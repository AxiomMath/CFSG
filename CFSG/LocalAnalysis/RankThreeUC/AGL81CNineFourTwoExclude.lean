module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFourTwoStruct
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFourTwoAlt
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFourTwoFi22
import CFSG.GroupTheory.LocalLift.NormalizerQuotient
import CFSG.RankThree.GroupTheory.AlternatingSectionLocalThreeRank
import CFSG.RankThree.PartOne.KP.Fi22SectionLocalThreeRank
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}

private theorem two_le_pRank_three_of_e9_le_starImg (s : NineSettingGen G M p Q H E 2)
    (hO : primeComplementCore (G := ↥H) p ≤ M.subgroupOf H)
    {R' : Subgroup (StarGroup p H)} (hR'N : R' ≤ starImg p H M)
    (hR'e : IsElemAbelian 3 R') (hR'c : Nat.card R' = 9) :
    2 ≤ CFSG.Open.pRank 3 M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hR'p : IsPGroup 3 R' := elementary_isPGroup 3 R' hR'e
  obtain ⟨R, hRp, hRM, hRmap⟩ := CFSG.LocalLift.exists_isPGroup_map_eq (r := 3)
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hO) hR'p hR'N
  have h2' : 2 ≤ CFSG.Open.pRank 3 R' := by
    have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := R') (E := R')
      le_rfl hR'e (k := 2) (by rw [hR'c]; norm_num)
    simpa using h
  have h2R : 2 ≤ CFSG.Open.pRank 3 R := by
    refine CFSG.LocalLift.two_le_pRank_of_map (r := 3) (by norm_num)
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) hRp ?_
    rwa [hRmap]
  have h2map : 2 ≤ CFSG.Open.pRank 3 (R.map H.subtype) :=
    h2R.trans (CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) H.subtype
      H.subtype_injective R)
  refine h2map.trans (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) ?_)
  calc R.map H.subtype ≤ (M.subgroupOf H).map H.subtype := Subgroup.map_mono hRM
    _ = M ⊓ H := Subgroup.subgroupOf_map_subtype M H
    _ ≤ M := inf_le_left

private theorem normalizer_le_subgroupOf_of_two_le_pRank (s : NineSettingGen G M p Q H E 2)
    (h3 : 3 ∈ sigmaM G M) {R : Subgroup ↥H} (hRM : R ≤ M.subgroupOf H)
    (hR : 2 ≤ CFSG.Open.pRank 3 R) :
    Subgroup.normalizer (R : Set ↥H) ≤ M.subgroupOf H := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hRM' : R.map H.subtype ≤ M := by
    calc R.map H.subtype ≤ (M.subgroupOf H).map H.subtype := Subgroup.map_mono hRM
      _ = M ⊓ H := Subgroup.subgroupOf_map_subtype M H
      _ ≤ M := inf_le_left
  have h2map : 2 ≤ CFSG.Open.pRank 3 (R.map H.subtype) :=
    hR.trans (CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) H.subtype
      H.subtype_injective R)
  have hN : Subgroup.normalizer (R.map H.subtype : Set G) ≤ M :=
    s.setting.normalizer_le_of_two_le_pRank h3 hRM' h2map
  have hEq : (Subgroup.normalizer (R.map H.subtype : Set G)).subgroupOf H =
      Subgroup.normalizer (R : Set ↥H) := by
    rw [Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le R)]
    rw [show (Subgroup.map H.subtype R).subgroupOf H = R from
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective R]
  rw [← hEq]
  exact Subgroup.subgroupOf_mono H hN

private theorem normalizer_le_starImg_of_two_le_pRank (s : NineSettingGen G M p Q H E 2)
    (hO : primeComplementCore (G := ↥H) p ≤ M.subgroupOf H) (h3 : 3 ∈ sigmaM G M)
    {R' : Subgroup (StarGroup p H)} (hR'p : IsPGroup 3 R') (hR'N : R' ≤ starImg p H M)
    (hR' : 2 ≤ CFSG.Open.pRank 3 R') :
    Subgroup.normalizer (R' : Set (StarGroup p H)) ≤ starImg p H M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine CFSG.LocalLift.normalizer_le_map_of_forall (r := 3)
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hO) hR'p hR'N ?_
  intro R hRp hRM hRmap
  refine normalizer_le_subgroupOf_of_two_le_pRank s h3 hRM ?_
  refine CFSG.LocalLift.two_le_pRank_of_map (r := 3) (by norm_num)
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) hRp ?_
  rwa [hRmap]

private theorem three_mem_sigmaM_of_four_le (h4 : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G)
    (h2 : 2 ≤ CFSG.Open.pRank 3 M) : 3 ∈ sigmaM G M :=
  ⟨CFSG.LocalAnalysis.AGL81TheoremCD.mem_sigmaA_of_four_le_localRank
    Nat.prime_three (by norm_num) (by simpa [CFSG.Open.rankThreeLocalRank] using h4), h2⟩

private noncomputable def kSubToKStar (p : ℕ) (M H : Subgroup G) :
    ↥(kSub p M H) →* ↥(kStar p M H) where
  toFun k := ⟨QuotientGroup.mk' (primeComplementCore (G := ↥H) p) ⟨k.1, kSub_le p M H k.2⟩,
    Subgroup.mem_map.mpr ⟨⟨k.1, kSub_le p M H k.2⟩, k.2, rfl⟩⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' x y := by apply Subtype.ext; rfl

private theorem kSubToKStar_surjective (p : ℕ) (M H : Subgroup G) :
    Function.Surjective (kSubToKStar (G := G) p M H) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩

theorem not_isAltTwoP_kStar {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}
    (s : NineSettingGen G M p Q H E 2) (hp : p ∈ sigmaM G M) (hL : ¬ pLayerIn p H ≤ M)
    (hΓ : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) → rankThreeGamma 1 p P ≤ M)
    (hp7 : 7 ≤ p) : ¬ CFSG.AGLEmbedding.IsAltTwoP p ↥(kStar p M H) := by
  haveI : Fact p.Prime := ⟨s.prime⟩
  intro hAlt
  obtain ⟨hY, hF, hnot, -, hO⟩ := nineFourTwo_star s hp hL hΓ
  haveI : (kStar p M H).Normal := by rw [← hF]; exact inferInstance
  obtain ⟨e⟩ := hAlt
  obtain ⟨R, hR, hRe, hRc⟩ := exists_e9_le_inf_of_altTwoP (p := p) hp7 hY e
  have h2M : 2 ≤ CFSG.Open.pRank 3 M :=
    two_le_pRank_three_of_e9_le_starImg s hO (hR.trans inf_le_left) hRe hRc
  have hπ : Function.Surjective (e.toMonoidHom.comp (kSubToKStar (G := G) p M H)) :=
    e.surjective.comp (kSubToKStar_surjective p M H)
  have h4 : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G :=
    CFSG.RankThree.GroupTheory.four_le_twoLocalPrimeRank_three_of_section_alternating
      (n := 2 * p) (by omega) (kSub p M H) _ hπ
  have h3M : 3 ∈ sigmaM G M := three_mem_sigmaM_of_four_le h4 h2M
  refine hnot (le_of_altTwoP (p := p) hp7 hY e ?_)
  intro R' hR' hR'e hR'c
  have hR'2 : 2 ≤ CFSG.Open.pRank 3 R' := by
    have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := R') (E := R')
      le_rfl hR'e (k := 2) (by rw [hR'c]; norm_num)
    simpa using h
  exact normalizer_le_starImg_of_two_le_pRank s hO h3M (elementary_isPGroup 3 R' hR'e)
    (hR'.trans inf_le_left) hR'2

section Fi22Certificates


theorem not_isFi22_kStar {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}
    (s : NineSettingGen G M p Q H E 2) (hp : p ∈ sigmaM G M) (hL : ¬ pLayerIn p H ≤ M)
    (hΓ : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M) → rankThreeGamma 1 p P ≤ M)
    (hp5 : p = 5) : ¬ CFSG.AGLEmbedding.IsFi22 ↥(kStar p M H) := by
  subst p
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro hFi
  obtain ⟨hY, hF, hnot, -, hO⟩ := nineFourTwo_star s hp hL hΓ
  haveI : (kStar 5 M H).Normal := by rw [← hF]; exact inferInstance
  obtain ⟨eK⟩ := id hFi
  obtain ⟨b⟩ : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic .Fi22).Group) := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have hf : Function.Surjective (kSubToKStar (G := G) 5 M H) := kSubToKStar_surjective 5 M H
  let K₀ : Subgroup ↥(kSub 5 M H) := (kSubToKStar (G := G) 5 M H).ker
  haveI : K₀.Normal := MonoidHom.normal_ker _
  have h4 : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G :=
    CFSG.RankThree.PartOne.four_le_twoLocalPrimeRank_three_of_section_fi22
      (kSub 5 M H) K₀
      ((QuotientGroup.quotientKerEquivOfSurjective _ hf).trans (eK.trans b.symm))
  obtain ⟨⟨R, hR, hRe, hRc⟩, -⟩ := exists_e9_le_inf_of_fi22 hY hFi hnot
  have h2M : 2 ≤ CFSG.Open.pRank 3 M :=
    two_le_pRank_three_of_e9_le_starImg s hO (hR.trans inf_le_left) hRe hRc
  have h3M : 3 ∈ sigmaM G M := three_mem_sigmaM_of_four_le h4 h2M
  have hR2 : 2 ≤ CFSG.Open.pRank 3 R := by
    have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := R) (E := R)
      le_rfl hRe (k := 2) (by rw [hRc]; norm_num)
    simpa using h
  obtain ⟨R₀, hR₀p, hR₀M, hR₀map⟩ := CFSG.LocalLift.exists_isPGroup_map_eq (r := 3)
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) 5))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hO)
    (elementary_isPGroup 3 R hRe) (hR.trans inf_le_left)
  have hR₀2 : 2 ≤ CFSG.Open.pRank 3 R₀ := by
    refine CFSG.LocalLift.two_le_pRank_of_map (r := 3) (by norm_num)
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) 5)) hR₀p ?_
    rwa [hR₀map]
  obtain ⟨S, hR₀S⟩ := (hR₀p.comap_subtype (K := M.subgroupOf H)).exists_le_sylow
  let T : Subgroup ↥H := (S : Subgroup ↥(M.subgroupOf H)).map (M.subgroupOf H).subtype
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T (M.subgroupOf H) := ⟨S, rfl⟩
  have hTle : T ≤ M.subgroupOf H := Subgroup.map_subtype_le _
  have hR₀T : R₀ ≤ T := by
    have h : (R₀.subgroupOf (M.subgroupOf H)).map (M.subgroupOf H).subtype ≤ T :=
      Subgroup.map_mono hR₀S
    rwa [Subgroup.map_subgroupOf_eq_of_le hR₀M] at h
  have hT2 : 2 ≤ CFSG.Open.pRank 3 T :=
    hR₀2.trans (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hR₀T)
  have hNT : Subgroup.normalizer (T : Set ↥H) ≤ M.subgroupOf H :=
    normalizer_le_subgroupOf_of_two_le_pRank s h3M hTle hT2
  have hTsylTop : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤ :=
    isSylowOf_top_of_normalizer_le hTsyl hNT
  have hT' := CFSG.ABGLocalTools.isSylowOf_iff.mp hTsylTop
  set ST : Sylow 3 ↥H := hT'.2.1.toSylow
    (by simpa [Subgroup.relIndex_top_right] using hT'.2.2) with hSTdef
  have hSTcoe : (ST : Subgroup ↥H) = T := by
    rw [hSTdef, IsPGroup.toSylow_coe]
  set SX : Sylow 3 (StarGroup 5 H) :=
    ST.mapSurjective (QuotientGroup.mk'_surjective _) with hSXdef
  have hSXcoe : (SX : Subgroup (StarGroup 5 H)) =
      T.map (QuotientGroup.mk' (primeComplementCore (G := ↥H) 5)) := by
    rw [hSXdef, Sylow.coe_mapSurjective, hSTcoe]
  have hSXN : (SX : Subgroup (StarGroup 5 H)) ≤ starImg 5 H M := by
    rw [hSXcoe]
    exact Subgroup.map_mono hTle
  exact not_sylow_three_le_of_fi22 hY hFi hnot SX hSXN

end Fi22Certificates

end CFSG.LocalAnalysis.RankThreeUC.AGL81C