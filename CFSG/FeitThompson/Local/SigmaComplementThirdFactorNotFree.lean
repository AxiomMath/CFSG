module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.TauTwoFactorContainsPlaneRegularActions
import CFSG.FeitThompson.Local.NonfreeProductFixedCentralizerSigmaCore
import CFSG.FeitThompson.Local.OutsideSigmaKappaSylowCoreNilpotent
import CFSG.FeitThompson.Local.AbelianAmbientCharacteristicChain
import CFSG.FeitThompson.Local.TwoBetaFixedCoresHallPosition
import CFSG.FeitThompson.Local.SigmaConjugateIntersectionCyclic
import CFSG.FeitThompson.Local.BetaNormalPrimeCentralizerPosition
import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

variable {G : Type*} [Group G]

theorem coe_conj_smul (c : G) (H : Subgroup G) :
    (MulAut.conj c • H : Subgroup G) = H.map (MulAut.conj c : G →* G) := (rfl)

theorem mem_conj_smul_conj (c : G) (H : Subgroup G) (y : G) :
    c * y * c⁻¹ ∈ (MulAut.conj c • H : Subgroup G) ↔ y ∈ H := by
  rw [coe_conj_smul]
  exact Subgroup.mem_map_iff_mem (f := (MulAut.conj c : G →* G)) (MulAut.conj c).injective

theorem le_normalizer_of_le_normalizer_conj_smul {E X : Subgroup G} {c : G} (hc : c ∈ E)
    (h : E ≤ normalizer ((MulAut.conj c • X : Subgroup G) : Set G)) :
    E ≤ normalizer (X : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  have hk : c * g * c⁻¹ ∈ E := mul_mem (mul_mem hc hg) (inv_mem hc)
  have hknorm := mem_normalizer_iff.1 (h hk) (c * y * c⁻¹)
  have e1 : (c * g * c⁻¹) * (c * y * c⁻¹) * (c * g * c⁻¹)⁻¹ = c * (g * y * g⁻¹) * c⁻¹ := by group
  rw [e1, mem_conj_smul_conj, mem_conj_smul_conj] at hknorm
  exact hknorm

theorem FNI_tau13_nonfree_third_factor_structure
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_tau13_noncentral_third_factor_free.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonfree_third_factor_structure.{u} := by
  intro G _ _ hG M E E₁ E₂ E₃ hfac hx
  obtain ⟨x, hxE₃, hx1, hxC⟩ := hx
  have hG04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hM : IsCoatom M := hfac.isSigmaComplement.isCoatom
  have hsd := hfac.isSigmaComplement.semidirect
  have hEM : E ≤ M := hsd.right_le
  have hsigma04 : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hM, hsd⟩
  have hsplit04 : _root_.CFSG.FeitThompson.IsTauHallSplitting M E E₁ E₂ E₃ :=
    { le_E₁ := hfac.le_E₁
      le_E₂ := hfac.le_E₂
      le_E₃ := hfac.le_E₃
      isHall_E₁ := hfac.hall_E₁
      isHall_E₂ := hfac.hall_E₂
      isHall_E₃ := hfac.hall_E₃
      outer := hfac.semidirect_E
      inner := hfac.semidirect_E₂₁ }
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hEsolv : Group.IsSolvable ↥E := @isSolvable_of_le _ _ _ _ hEM hMsolv
  have hxCsing : (sigmaCore M ⊓ centralizer ({x} : Set G) : Subgroup G) ≠ ⊥ := by
    rw [← centralizer_coe_zpowers, ← centralizerIn_eq]
    exact hxC
  have hE₃ne : E₃ ≠ ⊥ := fun h => hx1 (by rw [h] at hxE₃; simpa using hxE₃)
  have hcyc₁ := hfac.isCyclic_E₁
  have hcyc₃ := hfac.isCyclic_E₃
  have hE₂ : E₂ = ⊥ := by
    by_contra hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (fun hc => hne (Subgroup.card_eq_one.1 hc))
    have hqτ : q ∈ tauTwoPrimes M :=
      mem_of_dvd_natCard_of_isHallPiSubgroup_subgroupOf hfac.le_E₂ hfac.hall_E₂ hq hqdvd
    obtain ⟨-, hqσ, hrankM⟩ := mem_tauTwoPrimes_iff.1 hqτ
    have hqE : q ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥E :=
      ⟨hq, hqdvd.trans (Subgroup.card_dvd_of_le hfac.le_E₂)⟩
    have hrankE : elementaryAbelianPRank q ↥E = 2 := by
      rw [(FNI_sigma_complement_prime_data h₁ G hG04 M E hsigma04).2.1 q hqE |>.1, hrankM]
    obtain ⟨B, hBE, hB⟩ := exists_isElementaryAbelianPlane_le hq (by rw [hrankE])
    have hplane : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane q M B :=
      ⟨hM, hq, hqσ, hBE.trans hEM, hB⟩
    exact hxCsing ((FNI_sigma_complement_regular_factors h₂ h₃ h₄ G hG04 q M B E E₁ E₂ E₃
      hplane hsigma04 hBE hsplit04).2 x hx1 (Or.inl hxE₃))
  have houter : FreeCore.IsInternalSemidirectProduct E E₃ E₁ := by
    have h := hfac.semidirect_E
    rwa [hE₂, bot_sup_eq] at h
  have hE₁ne : E₁ ≠ ⊥ := by
    intro hb
    have hE₃E : E₃ = E := by rw [← houter.sup_eq, hb, sup_bot_eq]
    have : IsMulCommutative ↥E₃ := IsCyclic.isMulCommutative
    have hE₃cent : E₃ ≤ centralizer (E : Set G) := by
      rw [← hE₃E]; exact Subgroup.le_centralizer E₃
    have hcE := hfac.centralizer_E₃
    rw [centralizerIn_eq] at hcE
    exact hE₃ne (le_bot_iff.1 (le_trans (le_inf le_rfl hE₃cent) hcE.le))
  have hcent : ∀ P : Subgroup G, P ≤ E₁ → (Nat.card ↥P).Prime → P ≤ centralizer (E₃ : Set G) := by
    intro P hPE₁ hPprime
    by_contra hPnc
    refine hxCsing ?_
    have h := h₅ G hG M E E₁ E₂ E₃ hfac (Nat.card ↥P) hPprime P hPE₁ rfl hPnc x hxE₃ hx1
    rwa [centralizerIn_eq, centralizer_coe_zpowers] at h
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (fun hc => hE₁ne (Subgroup.card_eq_one.1 hc))
  obtain ⟨P, hPE₁, hPcard⟩ := exists_le_natCard_eq_of_prime_dvd hp hpdvd
  have hPcent : P ≤ centralizer (E₃ : Set G) := hcent P hPE₁ (hPcard ▸ hp)
  have hPne : P ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot] at hPcard; exact hp.ne_one hPcard.symm
  obtain ⟨b, hbP, hb1⟩ := P.bot_or_exists_ne_one.resolve_left hPne
  have hbcentE₃ : E₃ ≤ centralizer ({b} : Set G) := by
    have h := le_centralizer_of_le_centralizer (A := E₃) (Y := (zpowers b : Subgroup G))
      (zpowers_le.2 (hPcent hbP))
    rwa [centralizer_coe_zpowers] at h
  have hbfix : centralizerIn E₃ (zpowers b) ≠ ⊥ := by
    rw [centralizerIn_eq, centralizer_coe_zpowers]
    intro hbot
    exact hE₃ne (le_bot_iff.1 (hbot ▸ le_inf le_rfl hbcentE₃))
  refine ⟨hE₂, hE₁ne, houter, ?_, ?_⟩
  ·
    intro X hXE hXprime
    have hdvd : Nat.card ↥X ∣ Nat.card ↥E₃ * Nat.card ↥E₁ := by
      rw [← houter.natCard_eq_mul]; exact Subgroup.card_dvd_of_le hXE
    rcases (Nat.Prime.dvd_mul hXprime).1 hdvd with h3 | h1
    ·
      have hq3 : Nat.card ↥X ∈ tau3Primes M :=
        mem_of_dvd_natCard_of_isHallPiSubgroup_subgroupOf hfac.le_E₃ hfac.hall_E₃ hXprime h3
      have hXpi : IsPiSubgroup (tau3Primes M) X :=
        isPiSubgroup_of_natCard_eq_pow hXprime hq3 ⟨1, by rw [pow_one]⟩
      have hnorm3 : (E₃.subgroupOf E).Normal :=
        (normal_subgroupOf_iff_le_normalizer hfac.le_E₃).2 houter.le_normalizer
      have hXE₃ : X ≤ E₃ :=
        le_of_isHallPiSubgroup_normal_subgroupOf hnorm3 hfac.hall_E₃ hXE hXpi
      exact le_normalizer_of_le_of_isCyclic hXE₃ houter.le_normalizer
    ·
      have hq1 : Nat.card ↥X ∈ tau1Primes M :=
        mem_of_dvd_natCard_of_isHallPiSubgroup_subgroupOf hfac.le_E₁ hfac.hall_E₁ hXprime h1
      have hXpi : IsPiSubgroup (tau1Primes M) X :=
        isPiSubgroup_of_natCard_eq_pow hXprime hq1 ⟨1, by rw [pow_one]⟩
      obtain ⟨H, hH, hXH⟩ := exists_isHallPiSubgroupOf_ge_of_isPiSubgroup hEsolv hXE hXpi
      obtain ⟨c, hcE, hconj⟩ := exists_mem_conj_smul_eq_of_isHallPiSubgroupOf hEsolv hH
        ⟨hfac.le_E₁, hfac.hall_E₁⟩
      have hX'E₁ : (MulAut.conj c • X : Subgroup G) ≤ E₁ := by
        rw [← hconj]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hXH
      have hX'prime : (Nat.card ↥(MulAut.conj c • X : Subgroup G)).Prime := by
        rw [natCard_conj_smul]; exact hXprime
      have hX'cent := hcent _ hX'E₁ hX'prime
      have hE₃n : E₃ ≤ normalizer ((MulAut.conj c • X : Subgroup G) : Set G) :=
        (le_centralizer_of_le_centralizer hX'cent).trans (centralizer_le_normalizer _)
      have hE₁n : E₁ ≤ normalizer ((MulAut.conj c • X : Subgroup G) : Set G) :=
        le_normalizer_of_le_of_isCyclic hX'E₁ Subgroup.le_normalizer
      refine le_normalizer_of_le_normalizer_conj_smul hcE ?_
      rw [← houter.sup_eq]
      exact sup_le hE₃n hE₁n
  ·
    intro Y hYE hYne
    have hfix := FNI_tau13_nonfree_product_fixed_centralizer h₁ h₂ h₃ h₄ h₆ h₇ G hG M E E₁ E₂ E₃
      hfac ⟨b, hPE₁ hbP, hb1, hbfix⟩ Y (by rw [houter.sup_eq]; exact hYE) hYne
    rw [hfix, houter.sup_eq]

end

end CFSG.FeitThompson.Proofs
