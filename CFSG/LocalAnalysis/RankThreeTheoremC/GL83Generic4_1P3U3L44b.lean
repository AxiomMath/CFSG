module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34L44b
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

theorem u3l44_le_normalizer_of_not_le {X : Type} [Group X] [Finite X] (hK1 : U3SylowData)
    {K T W : Subgroup X} (hKn : K.Normal) (hU : IsRankThreeU3 ↥K) (hT : IsSylowOf 3 T K)
    (hTW : T ≤ W) (hNW : normalizer (T : Set X) ≤ W) (hKW : ¬ K ≤ W) :
    W ≤ normalizer (T : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hmapQ⟩ := hT
  have hTK : T ≤ K := hmapQ ▸ Subgroup.map_subtype_le _
  obtain ⟨-, hexp, -, -, -, hmax⟩ := hK1 _ hU Q
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
  have hT3 : ∀ t ∈ T, t ^ 3 = 1 := by
    intro t ht
    rw [← hmapQ] at ht
    obtain ⟨q, hq, rfl⟩ := ht
    have h1 := congrArg K.subtype (hexp q hq)
    rwa [map_pow, map_one] at h1
  have hconj : ∀ w ∈ W, ∀ t ∈ T, w * t * w⁻¹ ∈ T := by
    intro w hw t ht
    set k : K := ⟨w * t * w⁻¹, hKn.conj_mem t (hTK ht) w⟩
    have hkW : k ∈ W.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr (W.mul_mem (W.mul_mem hw (hTW ht)) (W.inv_mem hw))
    rw [hWK] at hkW
    have hk3 : k ^ 3 = 1 := Subtype.ext (by
      change (w * t * w⁻¹) ^ 3 = 1
      rw [conj_pow, hT3 t ht, mul_one, mul_inv_cancel])
    have hkp : IsPGroup 3 ↥(zpowers k) := IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
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

theorem u3l44_img_eq_map (x : G) (J A : Subgroup G) :
    l34Img x J A = ((A.subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3))).map
      (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore) := by
  unfold l34Img l34Hom
  rw [Subgroup.map_map]

theorem u3l44_mem_of_mk_mem (hS : Setting G) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G}
    {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x)
    {c : centralizer ({x} : Set G)}
    (hc : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c ∈
      ((centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3))) :
    (c : G) ∈ M := by
  have hOM : primeComplementCore (G := centralizer ({x} : Set G)) 3 ≤
      (centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G)) := by
    have h1 : GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M :=
      (glbPrimeCore_le_pPrimeCoreIn 3 _).trans (pPrimeCoreIn_centralizer_le hS hp hM hgen.2.2.2.ge)
    rw [← glbPrimeCore_subgroupOf 3 (centralizer ({x} : Set G))]
    exact glbPrimeCore_subgroupOf_le_inf h1
  have h2 := Subgroup.mem_comap.mpr hc
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hOM] at h2
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h2)).2

theorem u3l44_mem_of_img_mem (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : U3SylowData)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J)
    {c : centralizer ({x} : Set G)} (hc : l34Hom x J c ∈ l34Img x J M) : (c : G) ∈ M := by
  obtain ⟨Sbar, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have hDn := u3_reducedCentralizer_normal hJ
  have hDp := u3_reducedCentralizer_isPGroup hS hU0 hK1 hp hM hgen hJ
  have hker : (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).ker =
      reducedCentralizerOfJ x J := by
    rw [QuotientGroup.ker_mk', Subgroup.normalCore_eq_self]
  have hDΓ : reducedCentralizerOfJ x J ≤
      ((centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)) :=
    (hDp.le_sylow_of_normal Sbar).trans (le_normalizer.trans
      (hsh.normalizer_le _ le_rfl (by rw [hsh.rank_eq]; norm_num)))
  rw [u3l44_img_eq_map, ← Subgroup.inf_subgroupOf_left M (centralizer ({x} : Set G))] at hc
  have h2 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c ∈
      ((((centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3))).map
        (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore)).comap
        (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore) := hc
  rw [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hDΓ] at h2
  exact u3l44_mem_of_mk_mem hS hp hM hgen h2

theorem u3l44_gamma_le (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : U3SylowData)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J) :
    rankThreeGamma 1 3 (l34Img x J ((P : Subgroup G) ⊓ J)) ≤ l34Img x J M := by
  obtain ⟨Sbar, hSbar, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have hDn := u3_reducedCentralizer_normal hJ
  have hDp := u3_reducedCentralizer_isPGroup hS hU0 hK1 hp hM hgen hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  set D : Subgroup (C ⧸ O) := reducedCentralizerOfJ x J with hD
  set q : C ⧸ O →* L34Quot x J := QuotientGroup.mk' D.normalCore with hq
  have hker : q.ker = D := by rw [hq, QuotientGroup.ker_mk', Subgroup.normalCore_eq_self]
  have hxD : QuotientGroup.mk' O ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ q.ker := by
    rw [hker]
    exact (u3_xbar_facts hS hU0 hp hM hgen J).1
  have hkS : q.ker ≤ (Sbar : Subgroup (C ⧸ O)) := hker ▸ hDp.le_sylow_of_normal Sbar
  have hLk : r1sBar x J ⊓ q.ker = ⊥ := by
    rw [hker]
    exact u3_bar_inf_reducedCentralizer_eq_bot hJ
  rw [u3l44_img_eq_map x J M, ← Subgroup.inf_subgroupOf_left M C]
  refine l34l44_rankThreeGamma_le_map hsh q (QuotientGroup.mk'_surjective _) hkS hxD hLk ?_
  rw [u3l44_img_eq_map, hSbar]
  refine Subgroup.map_mono (le_inf (Subgroup.map_mono fun c hc => ?_)
    (Subgroup.map_mono fun c hc => ?_))
  · exact Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_subgroupOf.mp hc).1, c.2⟩
  · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hc).2

theorem u3l44_normalizer_le (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : U3SylowData)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J) :
    normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
      Set (L34Quot x J)) ≤ rankThreeGamma 1 3 (l34Img x J ((P : Subgroup G) ⊓ J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hU⟩ := u3_quot_data hS hU0 hp hM hgen hJ
  obtain ⟨⟨Q, hQ⟩, -, -⟩ := u3_T_data hS hU0 hK1 hp hM hgen hJ
  obtain ⟨E, hEQ, hE, hEc⟩ := (hK1 _ hU Q).2.2.2.1
  have h2 := le_pRank_of_elemAbelian_card hEQ hE hEc
  have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three
    (l34Img x J J).subtype (l34Img x J J).subtype_injective (Q : Subgroup (l34Img x J J))
  rw [hQ] at hmap
  exact le_sSup ⟨_, le_rfl, by omega, rfl⟩

theorem u3l44_le_normalizer (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : U3SylowData)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J) :
    l34Img x J M ≤ normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
      Set (L34Quot x J)) := by
  obtain ⟨hKn, -, hU⟩ := u3_quot_data hS hU0 hp hM hgen hJ
  obtain ⟨hT, -, -⟩ := u3_T_data hS hU0 hK1 hp hM hgen hJ
  have hPM := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  refine u3l44_le_normalizer_of_not_le hK1 hKn hU hT
    (Subgroup.map_mono (Subgroup.comap_mono (inf_le_left.trans hPM)))
    ((u3l44_normalizer_le hS hU0 hK1 hp hM hgen hJ).trans
      (u3l44_gamma_le hS hU0 hK1 hp hM hgen hJ)) fun hle => hJ.not_le fun j hj => ?_
  have hjC : j ∈ centralizer ({x} : Set G) := hJ.le_centralizer hj
  exact u3l44_mem_of_img_mem hS hU0 hK1 hp hM hgen hJ (c := ⟨j, hjC⟩)
    (hle ⟨⟨j, hjC⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
