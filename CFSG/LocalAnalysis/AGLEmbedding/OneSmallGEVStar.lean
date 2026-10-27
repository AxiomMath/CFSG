module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Star

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.extremal_of_normalizer_le (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) {Hs : Subgroup G} (hHs : GLBIsMaxTwoLocal Hs)
    (hLHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs) :
    Subgroup.centralizer ({z} : Set G) ≤ Hs ∧
      Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ Hs ∧ D1Extremal p P M Hs R := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hNC : Subgroup.normalizer (C : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p C) : Set G) :=
    normalizer_le_normalizer_pCoreOf_glbPrimeCore p C
  have hCHs : C ≤ Hs := (Subgroup.le_normalizer.trans hNC).trans hLHs
  have hNz : Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    have h : C = Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      rw [hC, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [h]
    exact RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer _
  have hRHs : R ≤ Hs := (hd.le_centralizer_czElt hz).trans hCHs
  have hHsM : ¬ Hs ≤ M := fun h => hd.centralizer_not_le hz (hCHs.trans h)
  have hrank : 3 ≤ Open.pRank p (Hs ⊓ M) :=
    hd.cfg.ext.three_le_pRank.trans (pRank_mono p hp (le_inf hRHs hd.cfg.ext.le_M))
  obtain ⟨T, hTM, -, -⟩ := intersecting_local_has_contained_sylow p hp P hd.cfg.ext.sylow_le
    hd.cfg.ext.weakCore_le hrank
  have hTR : Nat.card ((T : Subgroup Hs).map Hs.subtype) ≤ Nat.card R :=
    hd.cfg.ext.extremal Hs hHs.1 hHsM hrank _ (le_inf (Subgroup.map_subtype_le _) hTM)
      (T.isPGroup'.map _)
  obtain ⟨TR, hTRle⟩ := (hd.cfg.ext.isPGroup.comap_subtype (K := Hs)).exists_le_sylow
  have hRTR : R ≤ (TR : Subgroup Hs).map Hs.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRHs]
    exact Subgroup.map_mono hTRle
  have hTReq : (TR : Subgroup Hs).map Hs.subtype = R := by
    refine (Subgroup.eq_of_le_of_card_ge hRTR ?_).symm
    rw [Subgroup.card_map_of_injective Hs.subtype_injective, TR.card_eq_multiplicity,
      ← T.card_eq_multiplicity, ← Subgroup.card_map_of_injective Hs.subtype_injective]
    exact hTR
  exact ⟨hCHs, (hNz.trans hNC).trans hLHs,
    { hd.cfg.ext with
      maxTwoLocal_H := hHs
      le_H := hRHs
      isSylow := ⟨TR, hTReq⟩
      not_le := hHsM }⟩

theorem D1OneSmallData.exists_maxTwoLocal_normalizer_le (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z)
    (hV : pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) ≠ ⊥) :
    ∃ Hs : Subgroup G, GLBIsMaxTwoLocal Hs ∧
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs ∧
      Subgroup.centralizer ({z} : Set G) ≤ Hs ∧
      Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ Hs ∧ D1Extremal p P M Hs R := by
  have hloc : IsTwoLocal (Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G)) :=
    ⟨_, hV, RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _, rfl⟩
  obtain ⟨Hs, hLHs, hHs⟩ := exists_maximal_twoLocal hloc
  obtain ⟨hCHs, hNzHs, hext⟩ := hd.extremal_of_normalizer_le hz hHs hLHs
  exact ⟨Hs, hHs, hLHs, hCHs, hNzHs, hext⟩

end Star

section StarMap

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def d1StarMap (p : ℕ) {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs) :
    Subgroup.centralizer ({z} : Set G) →* Hs ⧸ primeComplementCore (G := Hs) p :=
  (QuotientGroup.mk' (primeComplementCore (G := Hs) p)).comp (Subgroup.inclusion hCHs)

omit [Finite G] in
theorem mem_of_centralizer_le {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs) : z ∈ Hs :=
  hCHs (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

@[expose] noncomputable def d1StarElt (p : ℕ) {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs) : Hs ⧸ primeComplementCore (G := Hs) p :=
  QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, mem_of_centralizer_le hCHs⟩

theorem d1StarMap_range {p : ℕ} (hp : p.Prime) {Hs : Subgroup G} {z : G} (hzp : orderOf z = p)
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs) :
    (d1StarMap p hCHs).range = Subgroup.centralizer ({d1StarElt p hCHs} : Set _) := by
  have : Fact p.Prime := ⟨hp⟩
  set zs : Hs := ⟨z, mem_of_centralizer_le hCHs⟩ with hzs
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (c : G) * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
    have hc' : (Subgroup.inclusion hCHs c) * zs = zs * (Subgroup.inclusion hCHs c) :=
      Subtype.ext hc
    show QuotientGroup.mk' _ (Subgroup.inclusion hCHs c) * QuotientGroup.mk' _ zs =
      QuotientGroup.mk' _ zs * QuotientGroup.mk' _ (Subgroup.inclusion hCHs c)
    rw [← map_mul, ← map_mul, hc']
  · intro hx
    have hzs' : orderOf zs = p := (Subgroup.orderOf_coe _).symm.trans hzp
    obtain ⟨g, hg, hgx⟩ := exists_mem_centralizer_mk_eq hp _ (primeComplementCore_coprime p)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzs', pow_one])) hx
    have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
    exact ⟨⟨g, hgC⟩, hgx⟩

theorem glbPrimeCore_normal_of_normal {X : Type*} [Group X] [Finite X] (p : ℕ)
    {A : Subgroup X} (hA : A.Normal) : (GLBPrimeCore p A).Normal := by
  have : (primeComplementCore (G := A) p).Characteristic := primeComplementCore_characteristic p
  rw [glbPrimeCore_eq_primeComplementCoreOf]
  exact ConjAct.normal_of_characteristic_of_normal

theorem d1StarMap_ker_le (p : ℕ) {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs) :
    (d1StarMap p hCHs).ker ≤
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p := by
  have hker : (d1StarMap p hCHs).ker =
      (primeComplementCore (G := Hs) p).comap (Subgroup.inclusion hCHs) := by
    rw [d1StarMap, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  refine normal_coprime_le_primeComplementCore p _ (MonoidHom.normal_ker _) ?_
  rw [hker]
  exact (primeComplementCore_coprime (G := Hs) p).coprime_dvd_right
    (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hCHs))

theorem le_d1StarMap_ker {p : ℕ} (hp : p.Prime) {Hs : Subgroup G} {z : G} (hzp : orderOf z = p)
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    (hcore : primeComplementCore (G := Hs ⧸ primeComplementCore (G := Hs) p) p = ⊥)
    (hA : (Subgroup.zpowers (d1StarElt p hCHs)).Normal) :
    primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p ≤
      (d1StarMap p hCHs).ker := by
  set φ := d1StarMap p hCHs with hφ
  set O := primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p with hO
  have hAn : φ.range.Normal := by
    rw [d1StarMap_range hp hzp hCHs, ← Subgroup.centralizer_closure,
      ← Subgroup.zpowers_eq_closure]
    exact Subgroup.normal_centralizer
  have hnorm : φ.range ≤ Subgroup.normalizer ((O.map φ : Subgroup _) : Set _) := by
    rw [MonoidHom.range_eq_map, ← Subgroup.normalizer_eq_top_iff.mpr (inferInstance : O.Normal)]
    exact Subgroup.le_normalizer_map φ
  have h1 : O.map φ ≤ GLBPrimeCore p φ.range :=
    le_glbPrimeCore (Subgroup.map_le_range φ O) hnorm
      ((primeComplementCore_coprime p).coprime_dvd_right (Subgroup.card_map_dvd O φ))
  have h2 : GLBPrimeCore p φ.range ≤
      primeComplementCore (G := Hs ⧸ primeComplementCore (G := Hs) p) p :=
    normal_coprime_le_primeComplementCore p _ (glbPrimeCore_normal_of_normal p hAn)
      (glbPrimeCore_coprime p φ.range)
  have h3 : O.map φ = ⊥ := by
    rw [eq_bot_iff, ← hcore]
    exact h1.trans h2
  exact (Subgroup.map_eq_bot_iff O).mp h3

noncomputable def d1CzQuotEquivRange (p : ℕ) {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    (hker : (d1StarMap p hCHs).ker =
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) :
    D1CzQuot p z ≃* (d1StarMap p hCHs).range :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange _)

theorem isComponentOf_le_centralizer_of_normal_zpowers {X : Type*} [Group X] [Finite X]
    {x : X} (hN : (Subgroup.zpowers x).Normal) {L : Subgroup X} (hL : IsComponentOf L ⊤) :
    L ≤ Subgroup.centralizer ({x} : Set X) := by
  rcases ComponentClassification.LocalComponents.normal_contains_or_commutes L
    (Subgroup.zpowers x) hL with h | h
  · exact h.trans (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  · have h' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h'

theorem d1StarMap_component {p : ℕ} (hp : p.Prime) {Hs : Subgroup G} {z : G}
    (hzp : orderOf z = p) (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    (hker : (d1StarMap p hCHs).ker =
      primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
    (hA : (Subgroup.zpowers (d1StarElt p hCHs)).Normal) {KC : Subgroup (D1CzQuot p z)}
    (huniq : ∀ L : Subgroup (D1CzQuot p z), IsComponentOf L ⊤ → L = KC)
    {L : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)} (hL : IsComponentOf L ⊤) :
    L ≤ (d1StarMap p hCHs).range ∧
      (L.subgroupOf (d1StarMap p hCHs).range).map
        ((d1CzQuotEquivRange p hCHs hker).symm :
          (d1StarMap p hCHs).range →* D1CzQuot p z) = KC := by
  have hLA : L ≤ (d1StarMap p hCHs).range := by
    rw [d1StarMap_range hp hzp hCHs]
    exact isComponentOf_le_centralizer_of_normal_zpowers hA hL
  refine ⟨hLA, huniq _ ?_⟩
  exact (ComponentClassification.LocalComponents.equiv_iff _ _).mpr
    (ComponentClassification.LocalComponents.of_overgroup hL hLA)

end StarMap

end CFSG.AGLEmbedding
