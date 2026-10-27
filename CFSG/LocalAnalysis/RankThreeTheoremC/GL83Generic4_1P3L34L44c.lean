module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34L44b
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34l44_img_eq_map (x : G) (J A : Subgroup G) :
    l34Img x J A = ((A.subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3))).map
      (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore) := by
  unfold l34Img l34Hom
  rw [Subgroup.map_map]

theorem l34l44_mem_of_mk_mem (hS : Setting G) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G}
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

theorem l34l44_mem_of_img_mem (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J)
    {c : centralizer ({x} : Set G)} (hc : l34Hom x J c ∈ l34Img x J M) : (c : G) ∈ M := by
  obtain ⟨Sbar, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have hDn := l34_reducedCentralizer_normal hJ
  have hDp := l34_reducedCentralizer_isPGroup hS hU0 hK1 hK2 hp hM hgen hJ
  have hker : (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).ker =
      reducedCentralizerOfJ x J := by
    rw [QuotientGroup.ker_mk', Subgroup.normalCore_eq_self]
  have hDΓ : reducedCentralizerOfJ x J ≤
      ((centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)) :=
    (hDp.le_sylow_of_normal Sbar).trans (le_normalizer.trans
      (hsh.normalizer_le _ le_rfl (by rw [hsh.rank_eq]; norm_num)))
  rw [l34l44_img_eq_map, ← Subgroup.inf_subgroupOf_left M (centralizer ({x} : Set G))] at hc
  have h2 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c ∈
      ((((centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3))).map
        (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore)).comap
        (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore) := hc
  rw [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hDΓ] at h2
  exact l34l44_mem_of_mk_mem hS hp hM hgen h2

theorem l34l44_gamma_le (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    rankThreeGamma 1 3 (l34Img x J ((P : Subgroup G) ⊓ J)) ≤ l34Img x J M := by
  obtain ⟨Sbar, hSbar, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have hDn := l34_reducedCentralizer_normal hJ
  have hDp := l34_reducedCentralizer_isPGroup hS hU0 hK1 hK2 hp hM hgen hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  set D : Subgroup (C ⧸ O) := reducedCentralizerOfJ x J with hD
  set q : C ⧸ O →* L34Quot x J := QuotientGroup.mk' D.normalCore with hq
  have hker : q.ker = D := by rw [hq, QuotientGroup.ker_mk', Subgroup.normalCore_eq_self]
  have hxD : QuotientGroup.mk' O ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ q.ker := by
    rw [hker, hD, r1s_reducedCentralizerOfJ_eq]
    exact mem_centralizer_iff.mpr fun h _ => mem_center_iff.mp hsh.mem_center h
  have hkS : q.ker ≤ (Sbar : Subgroup (C ⧸ O)) := hker ▸ hDp.le_sylow_of_normal Sbar
  have hLk : r1sBar x J ⊓ q.ker = ⊥ := by
    rw [hker]
    exact l34_bar_inf_reducedCentralizer_eq_bot hK1 hK2 hJ
  rw [l34l44_img_eq_map x J M, ← Subgroup.inf_subgroupOf_left M C]
  refine l34l44_rankThreeGamma_le_map hsh q (QuotientGroup.mk'_surjective _) hkS hxD hLk ?_
  rw [l34l44_img_eq_map, hSbar]
  refine Subgroup.map_mono (le_inf (Subgroup.map_mono fun c hc => ?_)
    (Subgroup.map_mono fun c hc => ?_))
  · exact Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_subgroupOf.mp hc).1, c.2⟩
  · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hc).2

theorem l34l44_normalizer_le (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
      Set (L34Quot x J)) ≤ rankThreeGamma 1 3 (l34Img x J ((P : Subgroup G) ⊓ J)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hT, hTc, -⟩ := l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ
  have h2 := le_pRank_of_elemAbelian_card le_rfl hT hTc
  exact le_sSup ⟨_, le_rfl, by omega, rfl⟩

theorem l34l44_le_normalizer (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    l34Img x J M ≤ normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
      Set (L34Quot x J)) := by
  obtain ⟨hKn, -, hL⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨hT, hTc, hTK⟩ := l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ
  have hPM := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  refine l34l44_le_normalizer_of_not_le hK2 hKn hL hT hTc hTK
    (Subgroup.map_mono (Subgroup.comap_mono (inf_le_left.trans hPM)))
    ((l34l44_normalizer_le hS hU0 hK1 hK2 hp hM hgen hJ).trans
      (l34l44_gamma_le hS hU0 hK1 hK2 hp hM hgen hJ)) fun hle => hJ.not_le fun j hj => ?_
  have hjC : j ∈ centralizer ({x} : Set G) := hJ.le_centralizer hj
  exact l34l44_mem_of_img_mem hS hU0 hK1 hK2 hp hM hgen hJ (c := ⟨j, hjC⟩)
    (hle ⟨⟨j, hjC⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩)

theorem l34_Kimg_inf_M (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    l34Img x J M ⊓ l34Img x J J =
      normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
        Set (L34Quot x J)) ⊓ l34Img x J J :=
  le_antisymm (inf_le_inf_right _ (l34l44_le_normalizer hS hU0 hK1 hK2 hp hM hgen hJ))
    (inf_le_inf_right _ ((l34l44_normalizer_le hS hU0 hK1 hK2 hp hM hgen hJ).trans
      (l34l44_gamma_le hS hU0 hK1 hK2 hp hM hgen hJ)))

end CFSG.LocalAnalysis.RankThreeTheoremC
