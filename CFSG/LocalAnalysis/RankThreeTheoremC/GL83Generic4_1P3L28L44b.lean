module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34L44b
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

theorem l28l44_le_normalizer_of_not_le {X : Type} [Group X] [Finite X] (hK1 : KFactL28Three)
    {K T W : Subgroup X} (hKn : K.Normal) (hU : IsRankThreeL28 ↥K) (hT : IsSylowOf 3 T K)
    (hTW : T ≤ W) (hNW : normalizer (T : Set X) ≤ W) (hKW : ¬ K ≤ W) :
    W ≤ normalizer (T : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hmapQ⟩ := hT
  have hTK : T ≤ K := hmapQ ▸ Subgroup.map_subtype_le _
  obtain ⟨-, hmax⟩ := hK1 _ hU Q
  have hNQ : normalizer ((Q : Subgroup K) : Set K) ≤ W.subgroupOf K := by
    intro k hk
    have h1 := Subgroup.le_normalizer_map K.subtype ⟨k, hk, rfl⟩
    rw [hmapQ] at h1
    exact Subgroup.mem_subgroupOf.mpr (hNW h1)
  have hWK : W.subgroupOf K = normalizer ((Q : Subgroup K) : Set K) := by
    rcases hmax _ hNQ with h | h
    · exact h
    · refine absurd (fun k hk => ?_) hKW
      have hk' : (⟨k, hk⟩ : K) ∈ W.subgroupOf K := h ▸ mem_top _
      exact Subgroup.mem_subgroupOf.mp hk'
  have hT3 : ∀ t ∈ T, ∃ m : ℕ, t ^ 3 ^ m = 1 := by
    intro t ht
    rw [← hmapQ] at ht
    obtain ⟨q, hq, rfl⟩ := ht
    obtain ⟨m, hm⟩ := Q.isPGroup' ⟨q, hq⟩
    refine ⟨m, ?_⟩
    have h1 := congrArg (fun z : ↥(Q : Subgroup K) => ((z : K) : X)) hm
    simpa using h1
  have hconj : ∀ w ∈ W, ∀ t ∈ T, w * t * w⁻¹ ∈ T := by
    intro w hw t ht
    set k : K := ⟨w * t * w⁻¹, hKn.conj_mem t (hTK ht) w⟩
    have hkW : k ∈ W.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr (W.mul_mem (W.mul_mem hw (hTW ht)) (W.inv_mem hw))
    rw [hWK] at hkW
    obtain ⟨m, hm⟩ := hT3 t ht
    have hk3 : k ^ 3 ^ m = 1 := Subtype.ext (by
      change (w * t * w⁻¹) ^ 3 ^ m = 1
      rw [conj_pow, hm, mul_one, mul_inv_cancel])
    have hkp : IsPGroup 3 ↥(zpowers k) := IsPGroup.of_card_dvd_pow (n := m) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk3)
    have h1 : k ∈ zpowers k ⊓ normalizer ((Q : Subgroup K) : Set K) := ⟨mem_zpowers k, hkW⟩
    have h2 : k ∈ (Q : Subgroup K) := ((hkp.inf_normalizer_sylow Q).le h1).2
    rw [← hmapQ]
    exact ⟨k, h2, rfl⟩
  intro w hw
  rw [mem_normalizer_iff]
  intro t
  refine ⟨hconj w hw t, fun h => ?_⟩
  have h1 := hconj w⁻¹ (W.inv_mem hw) _ h
  rwa [inv_inv, show w⁻¹ * (w * t * w⁻¹) * w = t by group] at h1

variable {G : Type} [Group G] [Finite G]

theorem l28l44_img_eq_map (x : G) (J A : Subgroup G) :
    l34Img x J A = ((A.subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3))).map
      (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore) := by
  unfold l34Img l34Hom
  rw [Subgroup.map_map]

theorem l28l44_mem_of_img_mem (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    {c : centralizer ({x} : Set G)} (hc : l34Hom x J c ∈ l34Img x J M) : (c : G) ∈ M := by
  obtain ⟨Sbar, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have hDn := l28_reducedCentralizer_normal hJ
  have hDp := l28_reducedCentralizer_isPGroup hS hU0 hp hM hgen hJ
  have hker : (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).ker =
      reducedCentralizerOfJ x J := by
    rw [QuotientGroup.ker_mk', Subgroup.normalCore_eq_self]
  have hDΓ : reducedCentralizerOfJ x J ≤
      ((centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)) :=
    (hDp.le_sylow_of_normal Sbar).trans (le_normalizer.trans
      (hsh.normalizer_le _ le_rfl (by rw [hsh.rank_eq]; norm_num)))
  rw [l28l44_img_eq_map, ← Subgroup.inf_subgroupOf_left M (centralizer ({x} : Set G))] at hc
  have h2 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c ∈
      ((((centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3))).map
        (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore)).comap
        (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore) := hc
  rw [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hDΓ] at h2
  exact l28s_mem_of_mk_mem hS hp hM hgen h2

theorem l28l44_gamma_le (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) :
    rankThreeGamma 1 3 (l34Img x J ((P : Subgroup G) ⊓ J)) ≤ l34Img x J M := by
  obtain ⟨Sbar, hSbar, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have hDn := l28_reducedCentralizer_normal hJ
  have hDp := l28_reducedCentralizer_isPGroup hS hU0 hp hM hgen hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  set D : Subgroup (C ⧸ O) := reducedCentralizerOfJ x J with hD
  set q : C ⧸ O →* L34Quot x J := QuotientGroup.mk' D.normalCore with hq
  have hker : q.ker = D := by rw [hq, QuotientGroup.ker_mk', Subgroup.normalCore_eq_self]
  have hxD : QuotientGroup.mk' O ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ q.ker := by
    rw [hker]
    exact (l28_xbar_facts hS hU0 hp hM hgen J).1
  have hkS : q.ker ≤ (Sbar : Subgroup (C ⧸ O)) := hker ▸ hDp.le_sylow_of_normal Sbar
  have hLk : r1sBar x J ⊓ q.ker = ⊥ := by
    rw [hker]
    exact l28_bar_inf_reducedCentralizer_eq_bot hJ
  rw [l28l44_img_eq_map x J M, ← Subgroup.inf_subgroupOf_left M C]
  refine l34l44_rankThreeGamma_le_map hsh q (QuotientGroup.mk'_surjective _) hkS hxD hLk ?_
  rw [l28l44_img_eq_map, hSbar]
  refine Subgroup.map_mono (le_inf (Subgroup.map_mono fun c hc => ?_)
    (Subgroup.map_mono fun c hc => ?_))
  · exact Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_subgroupOf.mp hc).1, c.2⟩
  · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hc).2

theorem l28l44_one_le_pRank {K : Type} [Group K] [Finite K] (Q : Sylow 3 K)
    (hc : Nat.card (Q : Subgroup K) = 3 ^ 2) : 1 ≤ CFSG.Open.pRank 3 (Q : Subgroup K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3
    (show 3 ∣ Nat.card (Q : Subgroup K) by rw [hc]; norm_num)
  have hao : orderOf (a : K) = 3 := by rw [Subgroup.orderOf_coe]; exact ha
  have hx3 : (a : K) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (a : K)
    rwa [hao] at h
  exact le_pRank_of_elemAbelian_card (zpowers_le.mpr a.2)
    (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) (by rw [Nat.card_zpowers, hao, pow_one])

theorem l28l44_normalizer_le (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL28Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) :
    normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
      Set (L34Quot x J)) ≤ rankThreeGamma 1 3 (l34Img x J ((P : Subgroup G) ⊓ J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hU⟩ := l28_quot_data hS hU0 hp hM hgen hJ
  obtain ⟨⟨Q, hQ⟩, -, -⟩ := l28_T_data hS hU0 hK1 hp hM hgen hJ
  obtain ⟨hQc, -⟩ := hK1 _ hU Q
  have h2 := l28l44_one_le_pRank Q hQc
  have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three
    (l34Img x J J).subtype (l34Img x J J).subtype_injective (Q : Subgroup (l34Img x J J))
  rw [hQ] at hmap
  exact le_sSup ⟨_, le_rfl, by omega, rfl⟩

theorem l28l44_le_normalizer (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL28Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) :
    l34Img x J M ≤ normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
      Set (L34Quot x J)) := by
  obtain ⟨hKn, -, hU⟩ := l28_quot_data hS hU0 hp hM hgen hJ
  obtain ⟨hT, -, -⟩ := l28_T_data hS hU0 hK1 hp hM hgen hJ
  have hPM := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  refine l28l44_le_normalizer_of_not_le hK1 hKn hU hT
    (Subgroup.map_mono (Subgroup.comap_mono (inf_le_left.trans hPM)))
    ((l28l44_normalizer_le hS hU0 hK1 hp hM hgen hJ).trans
      (l28l44_gamma_le hS hU0 hp hM hgen hJ)) fun hle => hJ.not_le fun j hj => ?_
  have hjC : j ∈ centralizer ({x} : Set G) := hJ.le_centralizer hj
  exact l28l44_mem_of_img_mem hS hU0 hp hM hgen hJ (c := ⟨j, hjC⟩)
    (hle ⟨⟨j, hjC⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
