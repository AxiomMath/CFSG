module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEVLine
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPIdent
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPTransvect
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEVAx
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEVPCentral

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.exists_axis_inv (hAut : KFactCycAut) (hSc : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hd : D1CaseTwoDataAt p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) (hnSP : ¬ D1CzSP p (z : G)) (hout : D1CzOutside p (z : G))
    (hB0 : D1CzB0 p R (z : G)) :
    ∃ w ∈ R, orderOf w = p ∧ w ∉ Subgroup.zpowers (z : G) ∧ (∀ g ∈ R, Commute w g) ∧
      (∀ g ∈ (P : Subgroup G), Commute w g) ∧
      (∀ g ∈ (P : Subgroup G), (∀ h ∈ (P : Subgroup G), Commute g h) → g ^ p = 1 →
        g ∈ Subgroup.zpowers w) ∧
      (∀ g ∈ R, (∀ h ∈ R, Commute g h) → g ^ p = 1 →
        g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G)) ∧
      ∃ s ∈ Subgroup.normalizer (R : Set G), s * (z : G) * s⁻¹ = z ∧
        s * w * s⁻¹ ∈ Subgroup.zpowers w ∧ s * w * s⁻¹ ≠ w := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({(z : G)} : Set G) with hCdef
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  have hcand : D1CaseTwoCand p M H R z := ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩
  obtain ⟨S₀, hT⟩ := hB0
  obtain ⟨A₀, φ, hφ⟩ := D1CaseTwoDataAt.exists_surjective_czQuot hd hL hzp hzL
  have hiso : IsCaseTwoGroup p L :=
    hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
        hd.cfg.catalog) hSc hd.cyclic hd.rank hL hLX
  have hLp : Group.IsPerfect L := ⟨hL.2.2.1⟩
  have hP1 : (P : Subgroup G).map (MulAut.conj (1 : G)).toMonoidHom = P := by
    ext x
    simp
  obtain ⟨Pbar, K, hc⟩ := D1CaseTwoDataAt.exists_czReduced hd hAut hSc hSyl hcand M.one_mem hT.ge
    (by rw [hT, hP1]; exact hd.cfg.ext.le_P)
  have hzK : d1CzElt p (z : G) ∉ K := hout K hc.comp
  obtain ⟨hcyc, hK⟩ := hc.isCyclic_and_isCaseTwoGroup_at hAut hSc hSch hInv hnSP hzK hiso hLp φ hφ
  obtain ⟨τ, hτT, hτK, hτc, hτp, hτz, hΩT, s, hsN, hsτ, hsτ1⟩ :=
    D1CzReduced.exists_kline_inv hc hL2 hzK hcyc hK hzp
  have hτR : (τ : G) ∈ R := hT ▸ ⟨τ, hτT, rfl⟩
  have hτcR : ∀ g ∈ R, Commute (τ : G) g := by
    intro g hg
    rw [← hT] at hg
    obtain ⟨σ, hσ, rfl⟩ := hg
    exact congrArg Subtype.val (hτc σ hσ)
  have hτpG : orderOf (τ : G) = p := by rw [Subgroup.orderOf_coe, hτp]
  have hΩR : ∀ g ∈ R, (∀ h ∈ R, Commute g h) → g ^ p = 1 →
      g ∈ Subgroup.zpowers (τ : G) ⊔ Subgroup.zpowers (z : G) := by
    intro g hg hgc hgp
    rw [← hT] at hg
    obtain ⟨σ, hσ, rfl⟩ := hg
    have hσc : ∀ h ∈ (S₀ : Subgroup C), Commute σ h := fun h hh =>
      Subtype.ext (hgc _ (hT ▸ ⟨h, hh, rfl⟩))
    have hσp : σ ^ p = 1 := Subtype.ext (by simpa using hgp)
    have h1 := hΩT σ hσ hσc hσp
    have h2 := Subgroup.mem_map_of_mem C.subtype h1
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hsGN : (s : G) ∈ Subgroup.normalizer (R : Set G) := by
    rw [← hT]
    exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hsN)
  have hsz : (s : G) * z * (s : G)⁻¹ = z := by
    have h1 : (s : G) * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp s.2
    rw [h1, mul_inv_cancel_right]
  have hsτG : (s : G) * τ * (s : G)⁻¹ ∈ Subgroup.zpowers (τ : G) := by
    have h1 := Subgroup.mem_map_of_mem C.subtype hsτ
    rw [MonoidHom.map_zpowers] at h1
    simpa using h1
  have hsτG1 : (s : G) * τ * (s : G)⁻¹ ≠ τ := fun h => hsτ1 (Subtype.ext (by simpa using h))
  have hQC := hd.inf_centralizer_le ⟨S₀, hT⟩
  have hne := hd.neSylow z hcand hnSP
  have hzc : ∀ g ∈ R, Commute (z : G) g := fun g hg =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hRz hg)).symm
  obtain ⟨w, hwR, hwp, hwz, hwc, hwP, hΩP, -, hnorm⟩ := exists_pcentral_axis
    hd.cfg.glob.charTwo hd.cfg.loc.maxLocal.1 hd.cfg.red.ne_two P.isPGroup' hd.cfg.ext.sylow_le
    hd.cfg.ext.le_P hne hzR hτR hzc hτcR hzp hτpG hτz hΩR hQC
  have hB0' : ∀ y ∈ Subgroup.normalizer (R : Set G), y * z * y⁻¹ = z →
      IsPGroup p (Subgroup.zpowers y) → y ∈ R := by
    intro y hyN hyz hyp
    have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [hyz])
    have hRy : IsPGroup p (R ⊔ Subgroup.zpowers y : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hd.cfg.ext.isPGroup hyp (Subgroup.zpowers_le.mpr hyN)
    have hmax := S₀.is_maximal' (hRy.comap_subtype (K := C))
      (fun σ hσ => (le_sup_left : R ≤ R ⊔ Subgroup.zpowers y) (hT ▸ ⟨σ, hσ, rfl⟩))
    have hy' : (⟨y, hyC⟩ : C) ∈ (S₀ : Subgroup C) := by
      rw [← hmax]
      exact (le_sup_right : Subgroup.zpowers y ≤ R ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
    rw [← hT]
    exact ⟨_, hy', rfl⟩
  have hw : w ∈ Subgroup.zpowers (τ : G) ⊔ Subgroup.zpowers (z : G) :=
    hΩR w hwR hwc (by rw [← hwp]; exact pow_orderOf_eq_one w)
  have hτw : (τ : G) ∈ Subgroup.zpowers w :=
    mem_zpowers_of_conj (hτcR z hzR) hτpG hwp hw hsz hsτG hsτG1 (hnorm hB0' (s : G) hsGN) hwz
  have heq : Subgroup.zpowers (τ : G) = Subgroup.zpowers w :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hτw)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hτpG, hwp])
  refine ⟨w, hwR, hwp, hwz, hwc, hwP, hΩP, fun g hg hgc hgp => heq ▸ hΩR g hg hgc hgp, s,
    hsGN, hsz, hnorm hB0' (s : G) hsGN, fun hsw => hsτG1 ?_⟩
  have hτw' : (τ : G) ∈ Subgroup.zpowers w := heq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hτw'
  rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hsw]

theorem D1CaseTwoData.exists_axis_inv (hβ : KFactBeta) (hSc : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hd : D1CaseTwoData p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) (hnSP : ¬ D1CzSP p (z : G)) (hout : D1CzOutside p (z : G))
    (hB0 : D1CzB0 p R (z : G)) :
    ∃ w ∈ R, orderOf w = p ∧ w ∉ Subgroup.zpowers (z : G) ∧ (∀ g ∈ R, Commute w g) ∧
      (∀ g ∈ (P : Subgroup G), Commute w g) ∧
      (∀ g ∈ (P : Subgroup G), (∀ h ∈ (P : Subgroup G), Commute g h) → g ^ p = 1 →
        g ∈ Subgroup.zpowers w) ∧
      (∀ g ∈ R, (∀ h ∈ R, Commute g h) → g ^ p = 1 →
        g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G)) ∧
      ∃ s ∈ Subgroup.normalizer (R : Set G), s * (z : G) * s⁻¹ = z ∧
        s * w * s⁻¹ ∈ Subgroup.zpowers w ∧ s * w * s⁻¹ ≠ w :=
  D1CaseTwoDataAt.exists_axis_inv (hAut := (kFactCycAut_of_kFactBeta hβ)) (hSc := hSc) (hL2 := hL2)
    (hInv := (kFactCaseTwoInvIn_of_kFactCaseTwoInv hInv)) (hSch := hSch) (hSyl := hSyl)
    (hd := hd.toAt) (hz := hz) (hnSP := hnSP) (hout := hout) (hB0 := hB0)

theorem D1CaseTwoDataAt.exists_fus_p (hd : D1CaseTwoDataAt p P M H R Rbar) {z w : G}
    (hzR : z ∈ R) (hzo : orderOf z = p) (hRz : R ≤ Subgroup.centralizer ({z} : Set G))
    (hB0 : D1CzB0 p R z) (hne : R ≠ (P : Subgroup G)) (hwo : orderOf w = p)
    (hwz : w ∉ Subgroup.zpowers z) (hwP : ∀ g ∈ (P : Subgroup G), Commute w g)
    (hΩR : ∀ g ∈ R, (∀ h ∈ R, Commute g h) → g ^ p = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers z) :
    ∀ i : ℕ, ∃ n ∈ M, n * z * n⁻¹ = z * w ^ i := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hQC := hd.inf_centralizer_le hB0
  obtain ⟨x, hxP, hxN, hxz⟩ := exists_mem_normalizer_not_mem_zpowers P.isPGroup'
    hd.cfg.ext.le_P hne hzo hQC
  have hxM : x ∈ M := hd.cfg.ext.sylow_le hxP
  have hzc : ∀ g ∈ R, Commute z g := fun g hg =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hRz hg)).symm
  have hxzR : x * z * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxN z).mp hzR
  have hxzc : ∀ h ∈ R, Commute (x * z * x⁻¹) h := by
    intro h hh
    have hh' : x⁻¹ * h * x ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) h).mp hh
      simpa using this
    have e := (hzc _ hh').eq
    show x * z * x⁻¹ * h = h * (x * z * x⁻¹)
    calc x * z * x⁻¹ * h = x * (z * (x⁻¹ * h * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * h * x) * z) * x⁻¹ := by rw [e]
      _ = h * (x * z * x⁻¹) := by group
  have hzp : z ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hxzp : (x * z * x⁻¹) ^ p = 1 := by rw [conj_pow, hzp, mul_one, mul_inv_cancel]
  have hwzc : Commute w z := hwP z (hd.cfg.ext.le_P hzR)
  have hxw : Commute x w := (hwP x hxP).symm
  obtain ⟨u, hu, v, hv, huv⟩ := (mem_zpowers_sup_zpowers_iff hwzc).mp (hΩR _ hxzR hxzc hxzp)
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨m, hm⟩ := P.isPGroup' ⟨x, hxP⟩
  have hxm : x ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hxz' : x * z * x⁻¹ = z ^ b * w ^ a := by rw [← huv, (hwzc.zpow_zpow a b).eq]
  have hxw' : x * w * x⁻¹ = w := by rw [hxw.eq, mul_inv_cancel_right]
  have hbot : Subgroup.zpowers z ⊓ Subgroup.zpowers w = ⊥ := by
    rw [inf_comm]
    exact zpowers_inf_zpowers_eq_bot_of_not_mem hwo hwz
  have hzb : z ^ b = z := zpow_eq_self_of_conj hwzc.symm hxz' hxw' hxm hzo hbot
  rw [hzb] at hxz'
  have hwa1 : w ^ a ≠ 1 := fun h1 => hxz (by
    rw [hxz', h1, mul_one]; exact Subgroup.mem_zpowers z)
  have hxu : x * w ^ a * x⁻¹ = w ^ a := by rw [(hxw.zpow_right a).eq, mul_inv_cancel_right]
  have hwap : orderOf (w ^ a) = p := by
    refine orderOf_eq_prime ?_ hwa1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hwo, pow_orderOf_eq_one,
      one_zpow]
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_zpow_ne_one hp hwo hwa1)
  intro i
  set k : ℕ := ((c * i) % (p : ℤ)).toNat with hk
  have hkc : ((k : ℕ) : ℤ) = (c * i) % (p : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero))
  refine ⟨x ^ k, M.pow_mem hxM k, ?_⟩
  rw [conj_pow_eq_mul_pow hxz' hxu k, ← zpow_natCast (w ^ a) k, hkc, ← hwap, zpow_mod_orderOf,
    zpow_mul, hc, zpow_natCast]

end CFSG.AGLEmbedding
