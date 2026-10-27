module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCentral
import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Star

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.extremal_of_normalizer_le (hd : D1CaseTwoDataAt p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) {Hs : Subgroup G} (hHs : GLBIsMaxTwoLocal Hs)
    (hLHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ Hs) :
    Subgroup.centralizer ({(z : G)} : Set G) ≤ Hs ∧
      Subgroup.normalizer (Subgroup.zpowers (z : G) : Set G) ≤ Hs ∧
      D1Extremal p P M Hs R := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  set C := Subgroup.centralizer ({(z : G)} : Set G) with hC
  have hNC : Subgroup.normalizer (C : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p C) : Set G) :=
    normalizer_le_normalizer_pCoreOf_glbPrimeCore p C
  have hCHs : C ≤ Hs := (Subgroup.le_normalizer.trans hNC).trans hLHs
  have hNz : Subgroup.normalizer (Subgroup.zpowers (z : G) : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    have h : C = Subgroup.centralizer (Subgroup.zpowers (z : G) : Set G) := by
      rw [hC, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [h]
    exact RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer _
  have hRHs : R ≤ Hs := hRz.trans hCHs
  have hHsM : ¬ Hs ≤ M := fun h => hd.cfg.centralizer_not_le hLX z.2 hzp hzL (hCHs.trans h)
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

theorem D1CaseTwoData.extremal_of_normalizer_le (hd : D1CaseTwoData p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) {Hs : Subgroup G} (hHs : GLBIsMaxTwoLocal Hs)
    (hLHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ Hs) :
    Subgroup.centralizer ({(z : G)} : Set G) ≤ Hs ∧
      Subgroup.normalizer (Subgroup.zpowers (z : G) : Set G) ≤ Hs ∧
      D1Extremal p P M Hs R :=
  D1CaseTwoDataAt.extremal_of_normalizer_le (hd := hd.toAt) (hz := hz) (hHs := hHs) (hLHs := hLHs)

theorem D1CaseTwoData.exists_componentConfig_star (hβ : KFactBeta) (hα : KFactAlphaW)
    (hd : D1CaseTwoData p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) {Hs : Subgroup G} (hHs : GLBIsMaxTwoLocal Hs)
    (hLHs : Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ Hs) :
    ∃ Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p),
      D1ComponentConfig p P M Hs R Rbars := by
  obtain ⟨-, -, hext⟩ := D1CaseTwoData.extremal_of_normalizer_le hd hz hHs hLHs
  have hcon : ¬ HasPrimeConstraint (G := Hs) p := fun hcon =>
    d1ConstrainedCase_of_kFactsW hβ hα G hd.cfg.glob p P M hd.cfg.loc Hs R hext hcon
  exact hext.exists_componentConfig hd.cfg.glob hd.cfg.loc hcon hd.cfg.ind

end Star

section Psi

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def d1StarPsi (p : ℕ) {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs) :
    (d1StarMap p hCHs).range →* D1CzQuot p z :=
  (QuotientGroup.map (d1StarMap p hCHs).ker
    (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) (MonoidHom.id _)
    (d1StarMap_ker_le p hCHs)).comp
    (QuotientGroup.quotientKerEquivRange (d1StarMap p hCHs)).symm.toMonoidHom

theorem d1StarPsi_apply (p : ℕ) {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs) (c : Subgroup.centralizer ({z} : Set G)) :
    d1StarPsi p hCHs ⟨d1StarMap p hCHs c, c, rfl⟩ =
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) c := by
  have h1 : (QuotientGroup.quotientKerEquivRange (d1StarMap p hCHs)).symm
      ⟨d1StarMap p hCHs c, c, rfl⟩ = (QuotientGroup.mk c : _ ⧸ (d1StarMap p hCHs).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [d1StarPsi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
  rfl

theorem d1StarPsi_surjective (p : ℕ) {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs) :
    Function.Surjective (d1StarPsi p hCHs) := by
  intro y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective
    (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) y
  exact ⟨_, d1StarPsi_apply p hCHs c⟩

theorem coprime_orderOf_of_d1StarPsi_eq_one (p : ℕ) {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs) (a : (d1StarMap p hCHs).range)
    (ha : d1StarPsi p hCHs a = 1) : p.Coprime (orderOf a) := by
  obtain ⟨_, c, rfl⟩ := a
  rw [d1StarPsi_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
  have h1 : orderOf (⟨d1StarMap p hCHs c, c, rfl⟩ : (d1StarMap p hCHs).range) ∣ orderOf c :=
    orderOf_map_dvd (d1StarMap p hCHs).rangeRestrict c
  exact ((primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G))
    p).coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ ha)).coprime_dvd_right h1

theorem exists_inner_cover (p : ℕ) {Hs : Subgroup G} {z : G}
    (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs) {KC : Subgroup (D1CzQuot p z)}
    (hKC : ⁅KC, KC⁆ = KC) :
    ∃ W : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p),
      ∃ hWA : W ≤ (d1StarMap p hCHs).range, ⁅W, W⁆ = W ∧ ∃ θ : W →* KC,
        Function.Surjective θ ∧
        ∀ w : W, (θ w : D1CzQuot p z) = d1StarPsi p hCHs ⟨w, hWA w.2⟩ := by
  set A := (d1StarMap p hCHs).range with hA
  set ψ := d1StarPsi p hCHs with hψ
  set W₀ : Subgroup A := KC.comap ψ with hW₀
  set Wp : Subgroup A := perfectCore W₀ with hWp
  have hWpW₀ : Wp ≤ W₀ := perfectCore_le W₀
  refine ⟨Wp.map A.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, perfectCore_perfect]
  set e := Subgroup.equivMapOfInjective Wp A.subtype A.subtype_injective with he
  set θ₀ : Wp →* KC := (ψ.comp Wp.subtype).codRestrict KC fun a => hWpW₀ a.2 with hθ₀
  refine ⟨θ₀.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro k
    have hmap : Wp.map ψ = KC := by
      rw [hWp, map_perfectCore, Subgroup.map_comap_eq_self_of_surjective
        (d1StarPsi_surjective p hCHs), perfectCore_eq_self_of_perfect hKC]
    have hk : (k : D1CzQuot p z) ∈ Wp.map ψ := by
      rw [hmap]
      exact k.2
    obtain ⟨a, ha, hak⟩ := hk
    refine ⟨e ⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact hak
  · intro w
    obtain ⟨a, rfl⟩ := e.surjective w
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl

theorem d1StarPsi_mem_of_mem_X0 {p : ℕ} (hp : p.Prime) {M Hs : Subgroup G} {z : G}
    (hzp : orderOf z = p) (hzM : z ∈ M) (hCHs : Subgroup.centralizer ({z} : Set G) ≤ Hs)
    (y : (d1StarMap p hCHs).range)
    (hy : (y : Hs ⧸ primeComplementCore (G := Hs) p) ∈
      ((Hs ⊓ M).subgroupOf Hs).map (QuotientGroup.mk' (primeComplementCore (G := Hs) p))) :
    d1StarPsi p hCHs y ∈ ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p)) := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set O := primeComplementCore (G := Hs) p with hO
  obtain ⟨m, hm, hmy⟩ := hy
  set ι : ↥(Hs ⊓ M) →* Hs := Subgroup.inclusion inf_le_left with hι
  set OY : Subgroup ↥(Hs ⊓ M) := O.comap ι with hOY
  have : OY.Normal := Subgroup.Normal.comap inferInstance ι
  have hOYc : p.Coprime (Nat.card OY) :=
    (primeComplementCore_coprime (G := Hs) p).coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective _))
  have hzHs : z ∈ Hs := mem_of_centralizer_le hCHs
  set zY : ↥(Hs ⊓ M) := ⟨z, hzHs, hzM⟩ with hzY
  have hmM : (m : G) ∈ Hs ⊓ M := hm
  set mY : ↥(Hs ⊓ M) := ⟨m, hmM⟩ with hmY
  have hzYp : orderOf zY = p := by
    rw [← Subgroup.orderOf_coe]
    exact hzp
  have hyC : (y : Hs ⧸ O) ∈ Subgroup.centralizer ({d1StarElt p hCHs} : Set _) := by
    rw [← d1StarMap_range hp hzp hCHs]
    exact y.2
  have hcomm : QuotientGroup.mk' O m * QuotientGroup.mk' O ⟨z, hzHs⟩ =
      QuotientGroup.mk' O ⟨z, hzHs⟩ * QuotientGroup.mk' O m := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hyC
    rw [← hmy] at this
    exact this
  have hmC : QuotientGroup.mk' OY mY ∈
      Subgroup.centralizer ({QuotientGroup.mk' OY zY} : Set (↥(Hs ⊓ M) ⧸ OY)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
    show ι ((mY * zY)⁻¹ * (zY * mY)) ∈ O
    have h1 : (QuotientGroup.mk' O (ι ((mY * zY)⁻¹ * (zY * mY)))) = 1 := by
      simp only [map_mul, map_inv]
      have e1 : QuotientGroup.mk' O (ι mY) = QuotientGroup.mk' O m := rfl
      have e2 : QuotientGroup.mk' O (ι zY) = QuotientGroup.mk' O ⟨z, hzHs⟩ := rfl
      rw [e1, e2, ← hcomm, inv_mul_cancel]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨g, hg, hgm⟩ := exists_mem_centralizer_mk_eq hp OY hOYc
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzYp, pow_one])) hmC
  have hgC : (g : G) ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
    exact this
  have hyg : (y : Hs ⧸ O) = d1StarMap p hCHs ⟨g, hgC⟩ := by
    rw [← hmy]
    have h1 := (QuotientGroup.eq (s := OY)).mp hgm
    show QuotientGroup.mk' O m = QuotientGroup.mk' O (ι g)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h2 : ι (g⁻¹ * mY) ∈ O := h1
    rw [map_mul, map_inv] at h2
    have h3 : ((ι g)⁻¹ * m)⁻¹ ∈ O := O.inv_mem h2
    simpa using h3
  have hyeq : y = ⟨d1StarMap p hCHs ⟨g, hgC⟩, ⟨g, hgC⟩, rfl⟩ := Subtype.ext hyg
  rw [hyeq, d1StarPsi_apply]
  exact ⟨⟨g, hgC⟩, ⟨hgC, (g.2 : (g : G) ∈ Hs ⊓ M).2⟩, rfl⟩

end Psi

end CFSG.AGLEmbedding
