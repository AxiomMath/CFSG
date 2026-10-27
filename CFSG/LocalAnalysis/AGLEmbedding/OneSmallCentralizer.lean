module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem eq_of_isPGroup_of_le_of_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P Q : Subgroup G} (hQ : IsPGroup p Q) (hPQ : P ≤ Q)
    (hN : ∀ g ∈ Q, g ∈ Subgroup.normalizer (P : Set G) → g ∈ P) : Q = P := by
  by_contra hne
  have : Group.IsNilpotent Q := hQ.isNilpotent
  set P' := P.subgroupOf Q
  have hlt : P' < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    refine le_antisymm (fun x hx => ?_) hPQ
    have : (⟨x, hx⟩ : Q) ∈ P' := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨q, hqN, hqP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent P' hlt)
  apply hqP
  have hqNG : (q : G) ∈ Subgroup.normalizer (P : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hxQ : (⟨x, hPQ hx⟩ : Q) ∈ P' := hx
    have := (Subgroup.mem_normalizer_iff.mp hqN _).mp hxQ
    exact this
  exact hN _ q.2 hqNG

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfigU.exists_sylow_centralizer (hcfg : D1ComponentConfigU p P M H R Rbar)
    {z : G} (hRC : R ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ m ∈ M, ∃ T : Sylow p (Subgroup.centralizer ({z} : Set G)),
      R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ∧
      (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
        (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
  have hp := hcfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({z} : Set G)
  have hRM : R ≤ M := hcfg.ext.le_M
  have hRp : IsPGroup p R := hcfg.ext.isPGroup
  obtain ⟨S, hS⟩ := (hRp.comap_subtype (K := C ⊓ M)).exists_le_sylow
  set Q₀ : Subgroup G := (S : Subgroup (C ⊓ M : Subgroup G)).map (C ⊓ M).subtype
  have hQ₀CM : Q₀ ≤ C ⊓ M := Subgroup.map_subtype_le _
  have hQ₀p : IsPGroup p Q₀ := S.isPGroup'.map _
  have hRQ₀ : R ≤ Q₀ := fun r hr =>
    ⟨⟨r, hRC hr, hRM hr⟩, hS (show (⟨r, hRC hr, hRM hr⟩ : (C ⊓ M : Subgroup G)) ∈
      R.comap (C ⊓ M).subtype from hr), rfl⟩
  have hmax : ∀ Y : Subgroup G, IsPGroup p Y → Q₀ ≤ Y → Y ≤ C ⊓ M → Y ≤ Q₀ := by
    intro Y hY hQY hYCM y hy
    have hSY : (S : Subgroup (C ⊓ M : Subgroup G)) ≤ Y.subgroupOf (C ⊓ M) :=
      fun s hs => hQY ⟨s, hs, rfl⟩
    have heq := S.is_maximal' hY.comap_subtype hSY
    have hy' : (⟨y, hYCM hy⟩ : (C ⊓ M : Subgroup G)) ∈ Y.comap (C ⊓ M).subtype := hy
    rw [heq] at hy'
    exact ⟨_, hy', rfl⟩
  obtain ⟨c, hc⟩ := exists_conjugate_le_sylow_of_le p P hcfg.ext.sylow_le
    (hQ₀CM.trans inf_le_right) hQ₀p
  have hm : (c : G)⁻¹ ∈ M := M.inv_mem c.2
  have hQ₀P : Q₀ ≤ (P : Subgroup G).map (MulAut.conj (c : G)⁻¹).toMonoidHom := by
    intro q hq
    refine ⟨(c : G) * q * (c : G)⁻¹, hc ⟨q, hq, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have h3 : 3 ≤ Open.pRank p Q₀ := hcfg.ext.three_le_pRank.trans (pRank_mono p hp hRQ₀)
  have hNQ₀ : Subgroup.normalizer (Q₀ : Set G) ≤ M :=
    (normalizer_le_weakCore p hQ₀P (by omega) (h3.trans (pRank_mono p hp le_sup_left))).trans
      (weakCore_conj_le hp hcfg.ext.weakCore_le hm)
  obtain ⟨T, hT⟩ := (hQ₀p.comap_subtype (K := C)).exists_le_sylow
  have hQ₀T : Q₀ ≤ (T : Subgroup C).map C.subtype := fun q hq =>
    ⟨⟨q, (hQ₀CM hq).1⟩, hT (show (⟨q, (hQ₀CM hq).1⟩ : C) ∈ Q₀.comap C.subtype from hq), rfl⟩
  have hTeq : (T : Subgroup C).map C.subtype = Q₀ := by
    refine eq_of_isPGroup_of_le_of_normalizer (T.isPGroup'.map _) hQ₀T fun g hgT hgN => ?_
    have hgC : g ∈ C := Subgroup.map_subtype_le _ hgT
    have hY : Q₀ ⊔ Subgroup.zpowers g ≤ (T : Subgroup C).map C.subtype :=
      sup_le hQ₀T (Subgroup.zpowers_le.mpr hgT)
    exact hmax _ ((T.isPGroup'.map _).to_le hY) le_sup_left
      (sup_le hQ₀CM (Subgroup.zpowers_le.mpr ⟨hgC, hNQ₀ hgN⟩))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))
  refine ⟨(c : G)⁻¹, hm, T, ?_, ?_⟩
  · rw [hTeq]
    exact hRQ₀
  · rw [hTeq]
    exact hQ₀P

theorem D1ComponentConfig.exists_sylow_centralizer (hcfg : D1ComponentConfig p P M H R Rbar)
    {z : G} (hRC : R ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ m ∈ M, ∃ T : Sylow p (Subgroup.centralizer ({z} : Set G)),
      R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ∧
      (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
        (P : Subgroup G).map (MulAut.conj m).toMonoidHom :=
  hcfg.toU.exists_sylow_centralizer hRC

theorem D1OneSmallData.exists_sylow_centralizer (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) :
    ∃ m ∈ M, ∃ T : Sylow p (Subgroup.centralizer ({z} : Set G)),
      R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ∧
      (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
        (P : Subgroup G).map (MulAut.conj m).toMonoidHom :=
  hd.cfg.exists_sylow_centralizer (hd.le_centralizer_czElt hz)

theorem D1ComponentConfig.exists_reducedCentralizer (hcfg : D1ComponentConfig p P M H R Rbar)
    {z : G} (hzp : orderOf z = p) (hRC : R ≤ Subgroup.centralizer ({z} : Set G))
    (hCM : ¬ Subgroup.centralizer ({z} : Set G) ≤ M) (hSP : D1CzSP p z) :
    ∃ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1Local p P' M ∧ (P' : Subgroup G) ≤ M ∧ R ≤ P' ∧
        D1ReducedCentralizer p P' M z Pbar KC := by
  have hp := hcfg.red.prime
  have hp2 := hcfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({z} : Set G)
  obtain ⟨m, hm, T, hRT, hTP⟩ := hcfg.exists_sylow_centralizer hRC
  set P' : Sylow p G := m • P with hP'def
  have hP'eq : (P' : Subgroup G) = (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
    rw [hP'def, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hP'M : (P' : Subgroup G) ≤ M := by
    rw [hP'eq]
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hcfg.ext.sylow_le hx)) (M.inv_mem hm)
  have hW' : GLBWeakCore p (P' : Subgroup G) ≤ M := by
    rw [hP'eq]
    exact weakCore_conj_le hp hcfg.ext.weakCore_le hm
  have hTP' : (T : Subgroup C).map C.subtype ≤ P' := by
    rw [hP'eq]
    exact hTP
  have hcore : GLBPrimeCore p C ≤ M :=
    intersecting_local_primeCore_le p hp P hcfg.ext.sylow_le hcfg.ext.weakCore_le
      (hcfg.ext.three_le_pRank.trans (pRank_mono p hp (le_inf hRC hcfg.ext.le_M)))
  have hT4 : 4 ≤ Open.pRank p ((T : Subgroup C).map C.subtype) := by
    rw [pRank_map_of_injective p hp C.subtype C.subtype_injective,
      (SectionRank.pRank_sylow T).1, ← SectionRank.pRank_eq_pRank_top_subgroup]
    exact hSP
  obtain ⟨Pbar, hPbar, hred⟩ := reducedNongeneration_of_not_le hp hp2 P' hP'M hW' hCM T hTP'
    (by omega) hcore
  have hlayer := layer_ne_bot_of_four_le_pRank hp hp2 P' hP'M hW' hCM T hTP' hT4 hcore
  obtain ⟨KC, hKC⟩ := exists_isComponentOf_of_layer_ne_bot hlayer
  have hcen : ∀ zC : C, (zC : G) = z →
      QuotientGroup.mk' (primeComplementCore (G := C) p) zC ∈
        Subgroup.center (C ⧸ primeComplementCore (G := C) p) ∧
      orderOf (QuotientGroup.mk' (primeComplementCore (G := C) p) zC) = p :=
    fun zC hzC => ⟨mk_mem_center_centralizer _ hzC, orderOf_mk_of_coprime hp _
      (primeComplementCore_coprime p) (by rw [← Subgroup.orderOf_coe, hzC, hzp])⟩
  obtain ⟨hzZ, hzbarp⟩ := hcen ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ rfl
  have hz1 : z ≠ 1 := fun hz1 => hp.one_lt.ne (by rw [← hzp, hz1, orderOf_one])
  have hTeq : (T : Subgroup C) = (P' : Subgroup G).subgroupOf C :=
    (T.is_maximal' P'.isPGroup'.comap_subtype fun t ht => hTP' ⟨t, ht, rfl⟩).symm
  refine ⟨P', Pbar, KC, ⟨hcfg.loc.beta, hcfg.loc.maxLocal, hW'⟩, hP'M, hRT.trans hTP',
    ⟨by rw [hPbar, hTeq], hred, ?_, ?_, hcen, hKC,
      hred.normal_of_isComponentOf_of_center hzZ hzbarp hKC,
      fun L hL => hred.eq_of_isComponentOf_of_center hzZ hzbarp hL hKC⟩⟩
  · rw [hPbar, pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p)]
    exact hT4
  · exact (catalogSimpleSections_of_isKProper hcfg.glob.kProper _
      (centralizer_singleton_ne_top hcfg.glob.simple hcfg.glob.nonab hz1)).quotient _

theorem D1OneSmallData.exists_reducedCentralizer (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hSP : D1CzSP p z) :
    ∃ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1Local p P' M ∧ (P' : Subgroup G) ≤ M ∧ R ≤ P' ∧
        D1ReducedCentralizer p P' M z Pbar KC :=
  hd.cfg.exists_reducedCentralizer hz.2.1 (hd.le_centralizer_czElt hz) (hd.centralizer_not_le hz)
    hSP

end Config

end CFSG.AGLEmbedding
