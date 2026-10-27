module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatHelp
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.center_le_map_R [Fact p.Prime] (hβ : KFactBeta) (hKO : KFactOneLie)
    (hTor : KFactOneLieTorus) (hSch : KFactCatalogSchreier) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hout : D1CzOutside p z) (h3 : D1PhaseThree p P M H R)
    (hY : pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥)
    {P' : Sylow p G} {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hRC : D1ReducedCentralizer p P' M z Pbar KC) (hRP' : R ≤ P')
    (hP'M : (P' : Subgroup G) ≤ M) :
    ∃ (TC : Sylow p KC) (n e : ℕ),
      (TC : Subgroup KC).map KC.subtype = (Pbar : Subgroup (D1CzQuot p z)) ⊓ KC ∧
      OneLieTorusFacts p KC TC n e ∧
      centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC) ≤
        (R.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk'
            (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) := by
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set mk := QuotientGroup.mk' (primeComplementCore (G := C) p) with hmk
  have hOC := primeComplementCore_coprime (G := C) p
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hRC' : R ≤ C := hd.le_centralizer_czElt hz
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, hzC⟩ rfl
  have hzK : mk ⟨z, hzC⟩ ∉ KC := hout KC hRC.comp
  have hKn := hRC.normal
  obtain ⟨hZK, hs, hnab, hcat, hbig, hnc, T₁, hT₁, hTnc, hΓ⟩ :=
    hRC.red.exists_sylow_facts_of_not_mem hRC.four_le_pRank hRC.catalog hzZ hzp hRC.comp hKn
      hzK hβ
  have hF := hKO KC hs hnab hcat p hp hp2 T₁ hTnc hΓ hbig
  obtain ⟨n, e, hTF⟩ := hTor KC hs hnab hcat p hp2 T₁ hTnc hΓ hbig
  have hzPbar : mk ⟨z, hzC⟩ ∈ (Pbar : Subgroup (D1CzQuot p z)) := by
    rw [hRC.sylow_eq]
    exact ⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.mpr (hRP' hz.1), rfl⟩
  have hz' : ∃ w ∈ (Pbar : Subgroup (D1CzQuot p z)), w ∉ KC ∧ orderOf w = p ∧
      w ∈ Subgroup.centralizer (KC : Set (D1CzQuot p z)) :=
    ⟨_, hzPbar, hzK, hzp, Subgroup.mem_centralizer_iff.mpr fun k _ =>
      Subgroup.mem_center_iff.mp hzZ k⟩
  have hY₀T := hRC.red.le_normalizer_of_borel_coatom hRC.comp hnc hz' T₁ hT₁ hTF.borel_coatom
  set W : Subgroup (D1CzQuot p z) := ((pCorePreimage p M ⊓ C).subgroupOf C).map mk with hW
  have hWY₀ : W ≤ ((C ⊓ M).subgroupOf C).map mk :=
    Subgroup.map_mono fun c hc => Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.mem_subgroupOf.mp hc).2, pCorePreimage_le p M (Subgroup.mem_subgroupOf.mp hc).1⟩
  have hAJ : C ⊓ M ≤ Subgroup.normalizer ((pCorePreimage p M ⊓ C : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCorePreimage p M hg.2, Subgroup.le_normalizer hg.1⟩
  have hY₀W : ((C ⊓ M).subgroupOf C).map mk ≤ Subgroup.normalizer (W : Set (D1CzQuot p z)) :=
    map_le_normalizer_map mk inf_le_right hAJ
  rcases hRC.red.dichotomy_of_torus hRC.comp hnc hz' hZK T₁ hT₁ hF hTF hY₀T W hWY₀ hY₀W with
    hle | hle
  swap
  ·
    exfalso
    obtain ⟨⟨x, hxY, hxX⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hY
    have hxC : x ∈ C := hRC' (d1LiftX_le p H R K hxX)
    have hxW : mk ⟨x, hxC⟩ ∈ W := ⟨⟨x, hxC⟩, Subgroup.mem_subgroupOf.mpr ⟨hxY, hxC⟩, rfl⟩
    have hxK := hd.mk_mem_comp_of_mem_d1LiftX hz hRC hSch hxX hxC
    have hcen : (⟨mk ⟨x, hxC⟩, hxK⟩ : KC) ∈ Subgroup.center KC :=
      Subgroup.mem_center_iff.mpr fun k =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle hxW) k k.2)
    rw [hZK, Subgroup.mem_bot] at hcen
    have h1 : mk ⟨x, hxC⟩ = mk 1 := by rw [map_one]; exact congrArg Subtype.val hcen
    have hRCp : IsPGroup p (R.subgroupOf C) := hd.cfg.ext.isPGroup.comap_subtype
    have h2 := eq_of_mk_eq_of_isPGroup hp _ hOC hRCp
      (show (⟨x, hxC⟩ : C) ∈ R.subgroupOf C from d1LiftX_le p H R K hxX)
      (R.subgroupOf C).one_mem h1
    exact hx1 (Subtype.ext (by simpa using congrArg Subtype.val h2))
  refine ⟨T₁, n, e, hT₁, hTF, fun ζ hζ => ?_⟩
  have hζW := hle hζ
  have hζP : ζ ∈ (Pbar : Subgroup (D1CzQuot p z)) := hζ.1.1
  rw [hRC.sylow_eq] at hζP
  obtain ⟨t, htP, rfl⟩ := hζP
  obtain ⟨w, hwY, hwt⟩ := hζW
  have htP' : (t : G) ∈ (P' : Subgroup G) := Subgroup.mem_subgroupOf.mp htP
  have htY : (t : G) ∈ pCorePreimage p M := by
    set L := C ⊓ M with hL
    set N : Subgroup L := (pCorePreimage p M ⊓ C).subgroupOf L with hN
    have hNL : pCorePreimage p M ⊓ C ≤ L :=
      fun y hy => ⟨hy.2, pCorePreimage_le p M hy.1⟩
    have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hAJ
    have htL : (t : G) ∈ L := ⟨t.2, hP'M htP'⟩
    have hwL : (w : G) ∈ L := ⟨w.2, pCorePreimage_le p M (Subgroup.mem_subgroupOf.mp hwY).1⟩
    set t' : L := ⟨t, htL⟩ with ht'
    set w' : L := ⟨w, hwL⟩ with hw'
    have hw'N : w' ∈ N := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hwY)
    have ho : p.Coprime (orderOf (w'⁻¹ * t')) := by
      have h1 : w⁻¹ * t ∈ primeComplementCore (G := C) p := QuotientGroup.eq.mp hwt
      have h2 := Subgroup.orderOf_dvd_natCard _ h1
      have e1 : orderOf (w'⁻¹ * t') = orderOf ((w : G)⁻¹ * t) := by
        rw [← Subgroup.orderOf_coe]; simp [ht', hw']
      have e2 : orderOf (w⁻¹ * t) = orderOf ((w : G)⁻¹ * t) := by
        rw [← Subgroup.orderOf_coe]; simp
      rw [e1, ← e2]
      exact hOC.coprime_dvd_right h2
    obtain ⟨k, hk⟩ := P'.isPGroup' ⟨t, htP'⟩
    have hk' : t' ^ p ^ k = 1 := Subtype.ext (by simpa [ht'] using congrArg Subtype.val hk)
    have hmem := mem_of_mul_inv_mem_of_coprime hp hk' ho
      (by rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]; exact hw'N)
    exact (Subgroup.mem_subgroupOf.mp hmem).1
  have htH : (t : G) ∈ H := (h3.pCorePreimage_le_inf h84 hD2 htY).1
  have htR : (t : G) ∈ R := hd.mem_of_mem_inf P'.isPGroup' hRP' htP' htH
  exact ⟨t, Subgroup.mem_subgroupOf.mpr htR, rfl⟩

end Config

end CFSG.AGLEmbedding
