module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEVAx
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEVLine
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPIdent
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEVPCentral

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseTwoKAxis (p : ℕ) (P : Sylow p G) (M R : Subgroup G) (z : G) : Prop :=
  ∃ w ∈ R, ∃ hwC : w ∈ Subgroup.centralizer ({z} : Set G),
    (∀ KC : Subgroup (D1CzQuot p z), IsComponentOf KC ⊤ →
      QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)
        ⟨w, hwC⟩ ∈ KC) ∧
    orderOf w = p ∧ w ∉ Subgroup.zpowers z ∧ (∀ g ∈ R, Commute w g) ∧
    (∀ g ∈ (P : Subgroup G), Commute w g) ∧
    (∀ g ∈ (P : Subgroup G), (∀ h ∈ (P : Subgroup G), Commute g h) → g ^ p = 1 →
      g ∈ Subgroup.zpowers w) ∧
    ¬ (pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.centralizer ({w} : Set G)) ∧
    (pCorePreimage p M ⊓ (P : Subgroup G) ≠ ⊥ → w ∈ pCorePreimage p M ∧
      ∀ o ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)),
        w * o * w⁻¹ * o⁻¹ ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G))

end Defs

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.exists_kaxis_of_cand (hAut : KFactCycAut) (hSc : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hd : D1CaseTwoDataAt p P M H R Rbar)
    (hnosp : D1CaseTwoNoSP p M H R) (hEV : D1CaseTwoAllOutEV p M H R) {z : H}
    (hz : D1CaseTwoCand p M H R z) : D1CaseTwoKAxis p P M R (z : G) := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({(z : G)} : Set G) with hCdef
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  have hcand : D1CaseTwoCand p M H R z := ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩
  have hnSP := hnosp L hL hLX z hzR hzp hRz hzL
  have hout := (hEV z hcand).1
  obtain ⟨S₀, hT⟩ := (hEV z hcand).2.1
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
  obtain ⟨w, hwR, hwp, hwz, hwc, hwP, hΩP, hA, hnorm⟩ := exists_pcentral_axis
    hd.cfg.glob.charTwo hd.cfg.loc.maxLocal.1 hd.cfg.red.ne_two P.isPGroup' hd.cfg.ext.sylow_le
    hd.cfg.ext.le_P hne hzR hτR hzc hτcR hzp hτpG hτz hΩR hQC
  have hB0 : ∀ y ∈ Subgroup.normalizer (R : Set G), y * z * y⁻¹ = z →
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
    mem_zpowers_of_conj (hτcR z hzR) hτpG hwp hw hsz hsτG hsτG1 (hnorm hB0 (s : G) hsGN) hwz
  have hwτ : w ∈ Subgroup.zpowers (τ : G) := by
    have heq : Subgroup.zpowers (τ : G) = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hτw)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hτpG, hwp])
    exact heq ▸ Subgroup.mem_zpowers w
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwτ
  have hwC : w ∈ C := hRz hwR
  have hwK : ∀ KC : Subgroup (D1CzQuot p (z : G)), IsComponentOf KC ⊤ →
      QuotientGroup.mk' (primeComplementCore (G := C) p) ⟨w, hwC⟩ ∈ KC := by
    intro KC hKC
    rw [hc.unique KC hKC]
    have h1 : (⟨w, hwC⟩ : C) = τ ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [h1, map_zpow]
    exact Subgroup.zpow_mem _ hτK k
  exact ⟨w, hwR, hwC, hwK, hwp, hwz, hwc, hwP, hΩP, hA,
    hd.mem_pCorePreimage_of_axis hRz hwR hwp hΩP⟩

end Main

end CFSG.AGLEmbedding
