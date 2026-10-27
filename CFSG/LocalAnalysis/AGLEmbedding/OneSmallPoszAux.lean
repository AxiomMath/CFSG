module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem le_map_conj_of_le_range {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hZ : Subgroup.center K = ⊥) (T : Sylow p K) {Y : Subgroup (MulAut K)} (hY : IsPGroup p Y)
    (hYI : Y ≤ (MulAut.conj : K →* MulAut K).range)
    (hYN : Y ≤ Subgroup.normalizer (((T : Subgroup K).map (MulAut.conj : K →* MulAut K) :
      Subgroup (MulAut K)) : Set (MulAut K))) :
    Y ≤ (T : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    intro a b hab
    have hc : b⁻¹ * a ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 : a * x * a⁻¹ = b * x * b⁻¹ := by
        simpa [MulAut.conj_apply] using congrArg (fun f : MulAut K => f x) hab
      calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
        _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [h1]
        _ = b⁻¹ * a * x := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  set Y₀ := Y.comap (MulAut.conj : K →* MulAut K)
  have hYeq : Y₀.map (MulAut.conj : K →* MulAut K) = Y := Subgroup.map_comap_eq_self hYI
  have hY₀ : IsPGroup p Y₀ := by
    rw [← hYeq] at hY
    exact hY.of_equiv (Subgroup.equivMapOfInjective Y₀ _ hinj).symm
  have hY₀N : Y₀ ≤ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have hN := Subgroup.mem_normalizer_iff.mp (hYN hy) (MulAut.conj t)
    have key : MulAut.conj y * MulAut.conj t * (MulAut.conj y)⁻¹ =
        MulAut.conj (y * t * y⁻¹) := by
      simp [map_mul, map_inv]
    rw [key] at hN
    constructor
    · intro ht
      obtain ⟨s, hs, hst⟩ := hN.mp ⟨t, ht, rfl⟩
      rwa [← hinj hst]
    · intro ht
      obtain ⟨s, hs, hst⟩ := hN.mpr ⟨_, ht, rfl⟩
      rwa [← hinj hst]
  have hle : Y₀ ≤ T := by
    intro y hy
    have h := hY₀.inf_normalizer_sylow T
    have hy' : y ∈ Y₀ ⊓ Subgroup.normalizer (T : Set K) := ⟨hy, hY₀N hy⟩
    rw [h] at hy'
    exact hy'.2
  rw [← hYeq]
  exact Subgroup.map_mono hle

section Inner

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y}

theorem le_inf_sup_inf_centralizer [Fact p.Prime] {K : Subgroup Y} [K.Normal]
    (hZ : Subgroup.center K = ⊥) (T₁ : Sylow p K)
    (hT₁ : (T₁ : Subgroup K).map K.subtype = (Rb : Subgroup Y) ⊓ K) {W : Subgroup Y}
    (hW : IsPGroup p W) (hWR : W ≤ Rb) (hWK : W ≤ K ⊔ Subgroup.centralizer (K : Set Y)) :
    W ≤ ((Rb : Subgroup Y) ⊓ K) ⊔ ((Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y)) := by
  have key : ∀ (f : MulAut K) (t : K), f * MulAut.conj t * f⁻¹ = MulAut.conj (f t) := by
    intro f t
    ext k
    simp [MulAut.mul_apply, MulAut.inv_def]
  have hmem : W.map (MulAut.conjNormal (H := K)) ≤
      (T₁ : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
    refine le_map_conj_of_le_range hZ T₁ (hW.map _) ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      have hw' : w ∈ ((K ⊔ Subgroup.centralizer (K : Set Y) : Subgroup Y) : Set Y) := hWK hw
      rw [Subgroup.mul_normal] at hw'
      obtain ⟨k, hk, c, hc, rfl⟩ := hw'
      refine ⟨⟨k, hk⟩, ?_⟩
      ext x
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      have hcx : c * (x : Y) = (x : Y) * c :=
        (Subgroup.mem_centralizer_iff.mp hc (x : Y) x.2).symm
      calc (k : Y) * x * (k : Y)⁻¹ = k * (c * x * c⁻¹) * (k : Y)⁻¹ := by
            rw [hcx, mul_inv_cancel_right]
        _ = k * c * x * (k * c)⁻¹ := by group
    · refine le_normalizer_of_forall_mul_mul_inv_mem ?_
      rintro _ ⟨w, hw, rfl⟩ _ ⟨t, ht, rfl⟩
      rw [key]
      have htY : (t : Y) ∈ (Rb : Subgroup Y) ⊓ K := hT₁ ▸ ⟨t, ht, rfl⟩
      have hwt : w * t * w⁻¹ ∈ (T₁ : Subgroup K).map K.subtype := by
        rw [hT₁]
        exact ⟨Rb.mul_mem (Rb.mul_mem (hWR hw) htY.1) (Rb.inv_mem (hWR hw)),
          ‹K.Normal›.conj_mem _ htY.2 w⟩
      obtain ⟨s, hs, hsw⟩ := hwt
      refine ⟨s, hs, congrArg MulAut.conj (Subtype.ext ?_)⟩
      rw [MulAut.conjNormal_apply]
      exact hsw
  intro w hw
  obtain ⟨t, ht, hwt⟩ := hmem ⟨w, hw, rfl⟩
  have htR : (t : Y) ∈ (Rb : Subgroup Y) ⊓ K := hT₁ ▸ ⟨t, ht, rfl⟩
  have e : w = (t : Y) * ((t : Y)⁻¹ * w) := by group
  rw [e]
  exact Subgroup.mul_mem_sup htR ⟨Rb.mul_mem (Rb.inv_mem htR.1) (hWR hw),
    inv_mul_mem_centralizer_of_conjNormal_eq hwt.symm⟩

end Inner

section General

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem weakCore_conj_le {P M : Subgroup G} (hp : p.Prime) (hWM : GLBWeakCore p P ≤ M) {m : G}
    (hm : m ∈ M) : GLBWeakCore p (P.map (MulAut.conj m).toMonoidHom) ≤ M := by
  have h1 := map_glbWeakCore_le hp (MulAut.conj m⁻¹).toMonoidHom (MulAut.conj m⁻¹).injective
    (P.map (MulAut.conj m).toMonoidHom)
  have h2 : (P.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom = P := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id P
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [h2] at h1
  intro x hx
  have hx' : (MulAut.conj m⁻¹).toMonoidHom x ∈ M := hWM (h1 ⟨x, hx, rfl⟩)
  have e : x = m * (m⁻¹ * x * m⁻¹⁻¹) * m⁻¹ := by group
  rw [e]
  exact M.mul_mem (M.mul_mem hm hx') (M.inv_mem hm)

end General

section Posz

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfig.centralizer_not_le (hcfg : D1ComponentConfig p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hLX : ¬ L ≤ d1X0 p M H) {z : G}
    (hzH : z ∈ H) (hzp : orderOf z = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p))) :
    ¬ Subgroup.centralizer ({z} : Set G) ≤ M :=
  hcfg.toU.centralizer_not_le hLX hzH hzp hzL

theorem D1OneSmallData.centralizer_not_le (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) : ¬ Subgroup.centralizer ({z} : Set G) ≤ M := by
  obtain ⟨zb, hzbR, hzbK, hzbp, hzbc⟩ := hd.z
  obtain ⟨-, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzbR hzbK hzbp hzbc
  obtain ⟨-, hzp, hzH, hzC⟩ := hz
  exact hd.cfg.centralizer_not_le hKX₀ hzH hzp hzC

theorem D1OneSmallData.le_centralizer_czElt (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) : R ≤ Subgroup.centralizer ({z} : Set G) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hO := primeComplementCore_coprime (G := H) p
  obtain ⟨zb, hzbR, hzbK, hzbp, hzbc⟩ := hd.z
  obtain ⟨-, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzbR hzbK hzbp hzbc
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  have hRC : IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) : Subgroup _) :=
    hd.cfg.red.isCyclic_of_le_centralizer hd.comp hKX₀ (Rbar.isPGroup'.to_le inf_le_left)
      inf_le_right
  obtain ⟨hzR, hzp, hzH, hzC⟩ := hz
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  have hRp : IsPGroup p R := hd.cfg.ext.isPGroup
  intro r hr
  have hrH : r ∈ H := hd.cfg.ext.le_H hr
  have hmemR : ∀ x : H, (x : G) ∈ R → π x ∈ (Rbar : Subgroup (H ⧸ primeComplementCore p)) :=
    fun x hx => by rw [hd.cfg.rbar]; exact Subgroup.mem_map_of_mem _ hx
  obtain ⟨y, hy⟩ : ∃ y : H, y = ⟨r, hrH⟩ * ⟨z, hzH⟩ * ⟨r, hrH⟩⁻¹ := ⟨_, rfl⟩
  have hyR : (y : G) ∈ R := by
    rw [hy]
    exact R.mul_mem (R.mul_mem hr hzR) (R.inv_mem hr)
  have hπy : π y = π ⟨r, hrH⟩ * π ⟨z, hzH⟩ * (π ⟨r, hrH⟩)⁻¹ := by
    rw [hy, map_mul, map_mul, map_inv]
  have hyC : π y ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) := by
    have hCn : (Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))).Normal :=
      Subgroup.normal_centralizer
    rw [hπy]
    exact hCn.conj_mem _ hzC (π ⟨r, hrH⟩)
  have hymp : orderOf (π y) = orderOf (π ⟨z, hzH⟩) := by
    rw [hπy, ← MulAut.conj_apply]
    exact orderOf_injective (MulAut.conj (π ⟨r, hrH⟩)).toMonoidHom
      (MulAut.conj (π ⟨r, hrH⟩)).injective _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_orderOf_eq_of_isCyclic
    (Z := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    ⟨hmemR y hyR, hyC⟩ ⟨hmemR _ hzR, hzC⟩ hymp)
  have hyk : (⟨z, hzH⟩ : H) ^ k = y := by
    have h1 : ((⟨z, hzH⟩ : H) ^ k)⁻¹ * y ∈ primeComplementCore (G := H) p := by
      rw [← QuotientGroup.ker_mk' (primeComplementCore (G := H) p), MonoidHom.mem_ker,
        map_mul, map_inv, map_zpow, ← hk, inv_mul_cancel]
    have h2 : ((⟨z, hzH⟩ : H) ^ k)⁻¹ * y ∈ R.subgroupOf H :=
      (R.subgroupOf H).mul_mem ((R.subgroupOf H).inv_mem ((R.subgroupOf H).zpow_mem
        (show (⟨z, hzH⟩ : H) ∈ R.subgroupOf H from hzR) k)) hyR
    have hdisj : Disjoint (R.subgroupOf H) (primeComplementCore (G := H) p) := by
      have hRH : IsPGroup p (R.subgroupOf H) := hRp.comap_subtype
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hRH
      exact Subgroup.disjoint_of_coprime_natCard (by rw [hn]; exact hO.pow_left n)
    have h3 := Subgroup.disjoint_def.mp hdisj h2 h1
    rw [inv_mul_eq_one] at h3
    exact h3
  have hconj : r * z * r⁻¹ = z ^ k := by
    have := congrArg Subtype.val hyk
    rw [hy] at this
    simpa using this.symm
  have hrN : r ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    mem_normalizer_zpowers_of_mem_zpowers (hconj ▸ Subgroup.zpow_mem_zpowers z k)
  obtain ⟨n, hn⟩ := hRp ⟨r, hr⟩
  have hrn : r ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_mem_normalizer_zpowers_of_pow_prime_pow hp hzp hrN hrn).eq

end Posz

end CFSG.AGLEmbedding
