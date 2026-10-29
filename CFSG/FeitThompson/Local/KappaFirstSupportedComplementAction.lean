module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.NonfreeProductFixedCentralizerSigmaCore
import CFSG.FeitThompson.Local.TauOneHallFixedCentralizer
import CFSG.FeitThompson.Local.SigmaComplementAbelianNilpotent
import CFSG.FeitThompson.Local.KappaHallThirdFactorSupportedComplement
import CFSG.FeitThompson.Local.NonabelianAmbientSingleRankTwoPrime
import CFSG.FeitThompson.Local.KappaPositiveMultipleCoreTrivialResidual
import CFSG.FeitThompson.Local.NonTIFittingCyclicComplement
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep03 (IsAmbient IsSemidirect IsHallPiOf cent
  cent1 IsThreeHallSetup)
open CFSG.FeitThompson.Prep05 (centralizerIn_eq)
open CFSG.FeitThompson.Prep09 (centIn_def)

universe u

variable {G : Type*} [Group G]

theorem le_normalizer_of_le_of_isMulCommutative {K X : Subgroup G} [IsMulCommutative ↥K]
    (hXK : X ≤ K) : K ≤ normalizer (X : Set G) :=
  le_trans (fun _ hk => mem_centralizer_iff.2 fun _ hh =>
    mul_comm_of_mem_of_isMulCommutative (hXK hh) hk) (centralizer_le_normalizer _)

theorem inf_centralizer_sup_eq_bot_of_coordinates {D B Y : Subgroup G}
    (hBD : B ≤ normalizer (D : Set G)) (hDB : D ⊓ B = ⊥)
    (hYD : Y ≤ normalizer (D : Set G)) (hYB : Y ≤ normalizer (B : Set G))
    (hD : D ⊓ centralizer (Y : Set G) = ⊥) (hB : B ⊓ centralizer (Y : Set G) = ⊥) :
    (D ⊔ B) ⊓ centralizer (Y : Set G) = ⊥ := by
  have huniq : ∀ a₁ ∈ D, ∀ b₁ ∈ B, ∀ a₂ ∈ D, ∀ b₂ ∈ B,
      a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ heq
    have hmem : a₂⁻¹ * a₁ ∈ D ⊓ B := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha₂) ha₁, ?_⟩
      have h2 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
        rw [show a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ by group, heq]
        group
      rw [h2]
      exact mul_mem hb₂ (inv_mem hb₁)
    rw [hDB, Subgroup.mem_bot] at hmem
    have ha : a₁ = a₂ := by
      have h3 : a₂ * (a₂⁻¹ * a₁) = a₂ * 1 := by rw [hmem]
      simpa [mul_assoc] using h3
    refine ⟨ha, ?_⟩
    rw [ha] at heq
    exact mul_left_cancel heq
  refine le_bot_iff.1 fun u hu => ?_
  obtain ⟨huDB, hucent⟩ := Subgroup.mem_inf.1 hu
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D B hBD] at huDB
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 huDB
  have key : ∀ y ∈ (Y : Set G), y * a * y⁻¹ = a ∧ y * b * y⁻¹ = b := by
    intro y hy
    have hcomm : y * (a * b) = a * b * y := (mem_centralizer_iff.1 hucent) y hy
    have haD : y * a * y⁻¹ ∈ D := (mem_normalizer_iff.1 (hYD hy) a).1 ha
    have hbB : y * b * y⁻¹ ∈ B := (mem_normalizer_iff.1 (hYB hy) b).1 hb
    have heq : (y * a * y⁻¹) * (y * b * y⁻¹) = a * b := by
      rw [show (y * a * y⁻¹) * (y * b * y⁻¹) = y * (a * b) * y⁻¹ by group, hcomm]
      group
    exact huniq _ haD _ hbB _ ha _ hb heq
  have haC : a ∈ D ⊓ centralizer (Y : Set G) :=
    Subgroup.mem_inf.2 ⟨ha, mem_centralizer_iff.2 fun y hy => by
      have h := (key y hy).1
      calc y * a = y * a * y⁻¹ * y := by group
        _ = a * y := by rw [h]⟩
  have hbC : b ∈ B ⊓ centralizer (Y : Set G) :=
    Subgroup.mem_inf.2 ⟨hb, mem_centralizer_iff.2 fun y hy => by
      have h := (key y hy).2
      calc y * b = y * b * y⁻¹ * y := by group
        _ = b * y := by rw [h]⟩
  rw [hD, Subgroup.mem_bot] at haC
  rw [hB, Subgroup.mem_bot] at hbC
  rw [haC, hbC, mul_one]
  exact Subgroup.mem_bot.2 rfl

theorem exists_prime_line_le_zpowers [Finite G] {k : G} (hk : k ≠ 1) :
    ∃ (q : ℕ) (Y : Subgroup G), q.Prime ∧ Y ≤ zpowers k ∧ Nat.card ↥Y = q ∧
      centralizer ({k} : Set G) ≤ centralizer (Y : Set G) := by
  have hko : orderOf k ≠ 1 := fun h => hk (orderOf_eq_one_iff.1 h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hko
  refine ⟨q, zpowers (k ^ (orderOf k / q)), hq, zpowers_le.2 (pow_mem (mem_zpowers k) _), ?_, ?_⟩
  · rw [Nat.card_zpowers, orderOf_pow_orderOf_div (orderOf_pos k).ne' hqd]
  · exact centralizer_singleton_le_centralizer_zpowers_pow k _

theorem FNI_kappa_first_supported_complement_action
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_tau12_fixed_plane_line_core_free.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_kappa_first_supported_complement_action.{u} := by
  intro G _ _ M E E₁ E₂ E₃ K hsetup hKne hK hKE₁
  have hamb03 : IsAmbient G := hsetup.ambient
  have hamb02 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hamb03.odd_natCard, hamb03.isSimpleGroup, hamb03.not_isMulCommutative,
      hamb03.forall_isSolvable⟩
  have hamb04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G := isOddSimpleMinimal_of_isAmbient hamb03
  have hamb05 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hamb03.odd_natCard, hamb03.isSimpleGroup, hamb03.not_isMulCommutative,
      hamb03.forall_isSolvable⟩
  have hamb09 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    isMinimalSimpleOddOrder_of_isAmbient hamb03
  have hM : IsCoatom M := hsetup.isCoatom
  have hdecomp : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    isInternalSemidirectProduct_of_isSemidirect hsetup.decomp
  have hEM : E ≤ M := hdecomp.right_le
  have hoddG : Odd (Nat.card G) := hamb03.odd_natCard
  have hMG : Nat.card ↥M ∣ Nat.card G := Subgroup.card_subgroup_dvd_card M
  have hE₁E : E₁ ≤ E := hsetup.isHall_E₁.1
  have hE₂E : E₂ ≤ E := hsetup.isHall_E₂.1
  have hE₃E : E₃ ≤ E := hsetup.isHall_E₃.1
  have hKM : K ≤ M := hK.1
  have hKE : K ≤ E := hKE₁.trans hE₁E
  have hfac : CFSG.FeitThompson.Prep05.IsTauFactorization M E E₁ E₂ E₃ :=
    isTauFactorization_of_isThreeHallSetup hsetup
  have hsc04 : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hM, hdecomp⟩
  have hE₁τ : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥E₁ → q ∈ tau1Primes M := fun q hq hd =>
    hsetup.isHall_E₁.2.1 q (Nat.mem_primeFactors.2 ⟨hq, hd, Nat.card_pos.ne'⟩)
  have hE₂τ : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥E₂ → q ∈ tauTwoPrimes M := fun q hq hd =>
    hsetup.isHall_E₂.2.1 q (Nat.mem_primeFactors.2 ⟨hq, hd, Nat.card_pos.ne'⟩)
  have hE₃τ : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥E₃ → q ∈ tau3Primes M := fun q hq hd =>
    hsetup.isHall_E₃.2.1 q (Nat.mem_primeFactors.2 ⟨hq, hd, Nat.card_pos.ne'⟩)
  have hcycOfRank : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥M → elementaryAbelianPRank q ↥M ≤ 1 →
      ∃ S : Sylow q ↥M, IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) :=
    fun q hq hdvd hr => exists_isCyclic_sylow_of_elementaryAbelianPRank_le_one M hq
      (Odd.of_dvd_nat hoddG (hdvd.trans hMG)) hr
  have hfix1 := FTS_tau_one_hall_fixed_centralizer h₁ h₆ h₇ G hamb09 M hM E hEM hdecomp E₁
    hE₁E (isHallPiSubgroup_subgroupOf_of_isHallPiOf hsetup.isHall_E₁)
  have hfixE₁ : ∀ X : Subgroup G, X ≤ E₁ → X ≠ ⊥ →
      sigmaCore M ⊓ centralizer (X : Set G) = sigmaCore M ⊓ centralizer (E₁ : Set G) := by
    intro X hXE₁ hXne
    have h := hfix1.2 X hXE₁ hXne
    rwa [centIn_def, centIn_def] at h
  obtain ⟨p, hp, hpK⟩ : ∃ p, p.Prime ∧ p ∣ Nat.card ↥K :=
    Nat.exists_prime_and_dvd fun h => hKne (Subgroup.card_eq_one.1 h)
  have hpκ : p ∈ kappaPrimes M := hK.2.1 p (Nat.mem_primeFactors.2 ⟨hp, hpK, Nat.card_pos.ne'⟩)
  obtain ⟨y, hyK, hyo⟩ := exists_mem_orderOf_eq_of_dvd hp hpK
  have hYcard : Nat.card ↥(zpowers y) = p := by rw [Nat.card_zpowers, hyo]
  have hYK : (zpowers y : Subgroup G) ≤ K := zpowers_le.2 hyK
  have hYbot : (zpowers y : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hYcard
    exact hp.ne_one hYcard.symm
  have hcycp : ∃ S : Sylow p ↥M, IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) := by
    obtain ⟨-, -, -, S, hS, -⟩ := mem_kappaPrimes_iff.1 hpκ
    exact ⟨S, hS⟩
  have hYne : sigmaCore M ⊓ centralizer ((zpowers y : Subgroup G) : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_mem_kappaPrimes hp hcycp hpκ (hYK.trans hKM) hYcard
  have hE₁ne : sigmaCore M ⊓ centralizer (E₁ : Set G) ≠ ⊥ := by
    rw [← hfixE₁ _ (hYK.trans hKE₁) hYbot]
    exact hYne
  have hE₁κ : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥E₁ → q ∈ kappaPrimes M := by
    intro q hq hd
    have hqτ := hE₁τ q hq hd
    obtain ⟨x, hxE₁, hxo⟩ := exists_mem_orderOf_eq_of_dvd hq hd
    have hXcard : Nat.card ↥(zpowers x) = q := by rw [Nat.card_zpowers, hxo]
    have hXE₁ : (zpowers x : Subgroup G) ≤ E₁ := zpowers_le.2 hxE₁
    have hXbot : (zpowers x : Subgroup G) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hXcard
      exact hq.ne_one hXcard.symm
    have hne : sigmaCore M ⊓ centralizer ((zpowers x : Subgroup G) : Set G) ≠ ⊥ := by
      rw [hfixE₁ _ hXE₁ hXbot]
      exact hE₁ne
    exact mem_kappaPrimes_of_inf_centralizer_ne_bot hq
      (notMem_sigmaPrimes_of_mem_tau1Primes hqτ)
      (hcycOfRank q hq (dvd_natCard_of_mem_tau1Primes hqτ)
        (le_of_eq (elementaryAbelianPRank_eq_one_of_mem_tau1Primes hqτ)))
      (hXE₁.trans (hE₁E.trans hEM)) hXcard hne
  have hKE₁' : K = E₁ := by
    have hone : K.relIndex E₁ = 1 := by
      by_contra hne
      have hne0 : K.relIndex E₁ ≠ 0 :=
        show (K.subgroupOf E₁).index ≠ 0 from Subgroup.index_ne_zero_of_finite
      obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.2 (by omega : 1 < K.relIndex E₁)
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrd : r ∣ K.relIndex E₁ := Nat.dvd_of_mem_primeFactors hr
      have hrE : r ∣ Nat.card ↥E₁ := hrd.trans (Subgroup.relIndex_dvd_card _ _)
      have hrM : r ∣ K.relIndex M := by
        rw [← Subgroup.relIndex_mul_relIndex K E₁ M hKE₁ (hE₁E.trans hEM)]
        exact hrd.mul_right _
      refine hK.2.2 r (Nat.mem_primeFactors.2 ⟨hrp, hrM, ?_⟩) (hE₁κ r hrp hrE)
      exact show (K.subgroupOf M).index ≠ 0 from Subgroup.index_ne_zero_of_finite
    exact le_antisymm hKE₁ (Subgroup.relIndex_eq_one.1 hone)
  have hKcyc : IsCyclic ↥K := hKE₁' ▸ hfix1.1
  have hKcomm : IsMulCommutative ↥K := hKcyc.isMulCommutative
  have hκτ₁ : ∀ q ∈ kappaPrimes M, q ∈ tau1Primes M := by
    intro q hq
    have hqp : q.Prime := prime_of_mem_kappaPrimes hq
    have hqM : q ∣ Nat.card ↥M := (mem_kappaPrimes_iff.1 hq).2.1
    have hmul : Nat.card ↥K * K.relIndex M = Nat.card ↥M := natCard_mul_relIndex hKM
    have hqK : q ∣ Nat.card ↥K := by
      rcases (Nat.Prime.dvd_mul hqp).1 (hmul ▸ hqM) with h | h
      · exact h
      · exact absurd hq (hK.2.2 q (Nat.mem_primeFactors.2 ⟨hqp, h,
          show (K.subgroupOf M).index ≠ 0 from Subgroup.index_ne_zero_of_finite⟩))
    exact hE₁τ q hqp (hKE₁' ▸ hqK)
  have hUE : (E₃ ⊔ E₂ : Subgroup G) ≤ E := sup_le hE₃E hE₂E
  have hUM : (E₃ ⊔ E₂ : Subgroup G) ≤ M := hUE.trans hEM
  have hE₃₂ : E₃ ⊓ E₂ = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hsetup.decomp_outer.2.2.2.2]
    exact inf_le_inf_left _ (le_sup_left : E₂ ≤ E₂ ⊔ E₁)
  have hE₂N₃ : E₂ ≤ normalizer (E₃ : Set G) := hE₂E.trans hsetup.decomp_outer.2.2.1
  have hcardU : Nat.card ↥(E₃ ⊔ E₂ : Subgroup G) = Nat.card ↥E₃ * Nat.card ↥E₂ :=
    natCard_sup_of_le_normalizer hE₂N₃ (disjoint_iff.2 hE₃₂)
  have hUprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(E₃ ⊔ E₂ : Subgroup G) →
      q ∈ tau3Primes M ∨ q ∈ tauTwoPrimes M := by
    intro q hq hd
    rw [hcardU] at hd
    rcases (Nat.Prime.dvd_mul hq).1 hd with h | h
    · exact Or.inl (hE₃τ q hq h)
    · exact Or.inr (hE₂τ q hq h)
  have hENorm : E ≤ normalizer ((E₃ ⊔ E₂ : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hsetup.normal_E₂E₃
  have hsupUK : (E₃ ⊔ E₂ : Subgroup G) ⊔ K = E := by
    rw [hKE₁', sup_assoc]
    exact hsetup.decomp_outer.2.2.2.1
  have hcopUK : (Nat.card ↥(E₃ ⊔ E₂ : Subgroup G)).Coprime (Nat.card ↥K) := by
    refine Nat.coprime_of_dvd fun k hk hkU hkK => ?_
    have hkτ₁ : k ∈ tau1Primes M := hE₁τ k hk (hKE₁' ▸ hkK)
    rcases hUprime k hk hkU with h | h
    · exact Set.disjoint_left.1 (disjoint_tau1Primes_tau3Primes M) hkτ₁ h
    · exact Set.disjoint_left.1 (disjoint_tauTwoPrimes_tau1Primes M) h hkτ₁
  have hinfUK : (E₃ ⊔ E₂ : Subgroup G) ⊓ K = ⊥ :=
    disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard hcopUK)
  have hcardE : Nat.card ↥E
      = Nat.card ↥(E₃ ⊔ E₂ : Subgroup G) * Nat.card ↥K := by
    rw [← hsupUK]
    exact natCard_sup_of_le_normalizer (hKE.trans hENorm) (disjoint_iff.2 hinfUK)
  have hE₃free : ∀ (q : ℕ) (Y : Subgroup G), q.Prime → Y ≤ E₁ → Nat.card ↥Y = q →
      E₃ ⊓ centralizer (Y : Set G) = ⊥ := by
    intro q₀ Y hq₀ hYE₁ hYcard₀
    have hYbot₀ : Y ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hYcard₀
      exact hq₀.ne_one hYcard₀.symm
    have hYfixne : sigmaCore M ⊓ centralizer (Y : Set G) ≠ ⊥ := by
      rw [hfixE₁ _ hYE₁ hYbot₀]
      exact hE₁ne
    by_contra hne
    obtain ⟨b, hbY, hb1, hbgen⟩ :=
      exists_zpowers_eq_of_prime_natCard (B := Y) (by rw [hYcard₀]; exact hq₀)
    have hhyp : ∃ b ∈ E₁, b ≠ 1 ∧
        CFSG.FeitThompson.Prep05.centralizerIn E₃ (zpowers b) ≠ ⊥ := by
      refine ⟨b, hYE₁ hbY, hb1, ?_⟩
      rw [centralizerIn_eq, hbgen]
      exact hne
    have hcommon := FNI_tau13_nonfree_product_fixed_centralizer h₁ h₂ h₃ h₄ h₆ h₇ G hamb05
      M E E₁ E₂ E₃ hfac hhyp
    obtain ⟨q, hq, hqd⟩ : ∃ q, q.Prime ∧
        q ∣ Nat.card ↥(E₃ ⊓ centralizer (Y : Set G) : Subgroup G) :=
      Nat.exists_prime_and_dvd fun h => hne (Subgroup.card_eq_one.1 h)
    obtain ⟨z, hzC, hzo⟩ := exists_mem_orderOf_eq_of_dvd hq hqd
    have hQcard : Nat.card ↥(zpowers z) = q := by rw [Nat.card_zpowers, hzo]
    have hQC : (zpowers z : Subgroup G) ≤ E₃ ⊓ centralizer (Y : Set G) := zpowers_le.2 hzC
    have hQE₃ : (zpowers z : Subgroup G) ≤ E₃ := hQC.trans inf_le_left
    have hQbot : (zpowers z : Subgroup G) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hQcard
      exact hq.ne_one hQcard.symm
    have hQfix := hcommon (zpowers z) (hQE₃.trans le_sup_left) hQbot
    have hYfix := hcommon Y (hYE₁.trans le_sup_right) hYbot₀
    have hQne : sigmaCore M ⊓ centralizer ((zpowers z : Subgroup G) : Set G) ≠ ⊥ := by
      rw [← centralizerIn_eq, hQfix, ← hYfix, centralizerIn_eq]
      exact hYfixne
    have hqτ₃ : q ∈ tau3Primes M := hE₃τ q hq (hQcard ▸ Subgroup.card_dvd_of_le hQE₃)
    have hqκ : q ∈ kappaPrimes M :=
      mem_kappaPrimes_of_inf_centralizer_ne_bot hq (notMem_sigmaPrimes_of_mem_tau3Primes hqτ₃)
        (hcycOfRank q hq (dvd_natCard_of_mem_tau3Primes hqτ₃)
          (le_of_eq (elementaryAbelianPRank_eq_one_of_mem_tau3Primes hqτ₃)))
        (hQE₃.trans (hE₃E.trans hEM)) hQcard hQne
    exact Set.disjoint_left.1 (disjoint_tau1Primes_tau3Primes M) (hκτ₁ q hqκ) hqτ₃
  have hE₂free : ∀ (q : ℕ) (Y : Subgroup G), q.Prime → Y ≤ E₁ → Nat.card ↥Y = q →
      E₂ ⊓ centralizer (Y : Set G) = ⊥ := by
    intro p₀ Y hp₀ hYE₁ hYcard₀
    have hYbot₀ : Y ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hYcard₀
      exact hp₀.ne_one hYcard₀.symm
    have hYfixne : sigmaCore M ⊓ centralizer (Y : Set G) ≠ ⊥ := by
      rw [hfixE₁ _ hYE₁ hYbot₀]
      exact hE₁ne
    have hp₀τ : p₀ ∈ tau1Primes M :=
      hE₁τ p₀ hp₀ (hYcard₀ ▸ Subgroup.card_dvd_of_le hYE₁)
    by_contra hne
    obtain ⟨q, hq, hqd⟩ : ∃ q, q.Prime ∧
        q ∣ Nat.card ↥(E₂ ⊓ centralizer (Y : Set G) : Subgroup G) :=
      Nat.exists_prime_and_dvd fun h => hne (Subgroup.card_eq_one.1 h)
    obtain ⟨z, hzC, hzo⟩ := exists_mem_orderOf_eq_of_dvd hq hqd
    have hQcard : Nat.card ↥(zpowers z) = q := by rw [Nat.card_zpowers, hzo]
    have hQC : (zpowers z : Subgroup G) ≤ E₂ ⊓ centralizer (Y : Set G) := zpowers_le.2 hzC
    have hQE₂ : (zpowers z : Subgroup G) ≤ E₂ := hQC.trans inf_le_left
    have hqτ₂ : q ∈ tauTwoPrimes M := hE₂τ q hq (hQcard ▸ Subgroup.card_dvd_of_le hQE₂)
    obtain ⟨A, hAE, hAplane⟩ := exists_plane_le_of_isInternalSemidirectProduct hqτ₂ hdecomp
    have hosA : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane q M A :=
      ⟨hM, hq, notMem_sigmaPrimes_of_mem_tauTwoPrimes hqτ₂, hAE.trans hEM, hAplane⟩
    obtain ⟨-, hlines, -⟩ := h₂ G hamb04 q M A E hosA hsc04 hAE
    have hQA : (zpowers z : Subgroup G) ≤ A := hlines _ (hQE₂.trans hE₂E) hQcard
    have hAY : A ⊓ centralizer (Y : Set G) ≠ ⊥ := by
      intro h
      have hz1 : z ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_inf.2 ⟨hQA (mem_zpowers z),
        (Subgroup.mem_inf.1 (hQC (mem_zpowers z))).2⟩
      rw [Subgroup.mem_bot] at hz1
      rw [hz1, orderOf_one] at hzo
      exact hq.one_lt.ne hzo
    exact hYfixne (h₅ G hamb04 p₀ q M E Y A hsc04 hp₀τ (hYE₁.trans hE₁E) hYcard₀ hqτ₂ hAE
      hAplane hAY)
  have hUfree : ∀ k ∈ K, k ≠ 1 →
      (E₃ ⊔ E₂ : Subgroup G) ⊓ centralizer ({k} : Set G) = ⊥ := by
    intro k hk hk1
    obtain ⟨q, Y, hq, hYk, hYcard₀, hcentle⟩ := exists_prime_line_le_zpowers (G := G) hk1
    have hYK : Y ≤ K := hYk.trans (zpowers_le.2 hk)
    have hYE₁ : Y ≤ E₁ := hYK.trans hKE₁
    have hYN₃ : Y ≤ normalizer (E₃ : Set G) :=
      (hYE₁.trans hE₁E).trans hsetup.decomp_outer.2.2.1
    have hYN₂ : Y ≤ normalizer (E₂ : Set G) :=
      (hYE₁.trans (le_sup_right : E₁ ≤ E₂ ⊔ E₁)).trans hsetup.decomp_inner.2.2.1
    have hzero := inf_centralizer_sup_eq_bot_of_coordinates hE₂N₃ hE₃₂ hYN₃ hYN₂
      (hE₃free q Y hq hYE₁ hYcard₀) (hE₂free q Y hq hYE₁ hYcard₀)
    refine le_bot_iff.1 (le_trans ?_ (le_of_eq hzero))
    exact inf_le_inf_left _ hcentle
  have hUcentK : (E₃ ⊔ E₂ : Subgroup G) ⊓ centralizer (K : Set G) = ⊥ := by
    obtain ⟨k, hk, hk1⟩ : ∃ k ∈ K, k ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hKne (le_bot_iff.1 fun x hx => Subgroup.mem_bot.2 (hc x hx))
    refine le_bot_iff.1 (le_trans ?_ (le_of_eq (hUfree k hk hk1)))
    exact inf_le_inf_left _ (centralizer_le (by simpa using hk))
  have hMsolv : Group.IsSolvable ↥M := hamb03.forall_isSolvable M hM.1
  have hKsolv : Group.IsSolvable ↥K := @isSolvable_of_le _ _ _ _ hKM hMsolv
  have hUsolv : Group.IsSolvable ↥(E₃ ⊔ E₂ : Subgroup G) :=
    @isSolvable_of_le _ _ _ _ hUM hMsolv
  have habelE' := (FBG_sigma_complement_abelian_nilpotent h₁ h₄ G hamb02 M hM).2 E hdecomp
  have hUcomm : IsMulCommutative ↥(E₃ ⊔ E₂ : Subgroup G) := by
    have hle : (E₃ ⊔ E₂ : Subgroup G) ≤ ⁅(E₃ ⊔ E₂ : Subgroup G), K⁆ :=
      @le_commutator_of_coprime_of_inf_centralizer_eq_bot _ _ _ _ _ hKsolv hUsolv
        (hKE.trans hENorm) hcopUK.symm hUcentK
    exact @isMulCommutative_of_le _ _ _ _ habelE'
      (hle.trans (Subgroup.commutator_mono hUE hKE))
  have hUhall : IsHallPiOf (sigmaPrimes M ∪ kappaPrimes M)ᶜ (E₃ ⊔ E₂) M := by
    refine ⟨hUM, ?_, ?_⟩
    · intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrd : r ∣ Nat.card ↥(E₃ ⊔ E₂ : Subgroup G) := Nat.dvd_of_mem_primeFactors hr
      have hnotτ₁ : r ∉ tau1Primes M := by
        rcases hUprime r hrp hrd with h | h
        · exact fun hc => Set.disjoint_left.1 (disjoint_tau1Primes_tau3Primes M) hc h
        · exact fun hc => Set.disjoint_left.1 (disjoint_tauTwoPrimes_tau1Primes M) h hc
      rw [Set.mem_compl_iff, Set.mem_union]
      rintro (hc | hc)
      · rcases hUprime r hrp hrd with h | h
        · exact Set.disjoint_left.1 (disjoint_tau3Primes_sigmaPrimes M) h hc
        · exact notMem_sigmaPrimes_of_mem_tauTwoPrimes h hc
      · exact hnotτ₁ (hκτ₁ r hc)
    · intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrd : r ∣ (E₃ ⊔ E₂ : Subgroup G).relIndex M := Nat.dvd_of_mem_primeFactors hr
      have hidx : (E₃ ⊔ E₂ : Subgroup G).relIndex M
          = Nat.card ↥(sigmaCore M) * Nat.card ↥K := by
        have h1 : Nat.card ↥(E₃ ⊔ E₂ : Subgroup G) * (E₃ ⊔ E₂ : Subgroup G).relIndex M
            = Nat.card ↥M := natCard_mul_relIndex hUM
        have h2 : Nat.card ↥M = Nat.card ↥(sigmaCore M) * Nat.card ↥E := hdecomp.natCard_eq_mul
        have hUpos : 0 < Nat.card ↥(E₃ ⊔ E₂ : Subgroup G) := Nat.card_pos
        have h3 : Nat.card ↥(E₃ ⊔ E₂ : Subgroup G) * (E₃ ⊔ E₂ : Subgroup G).relIndex M
            = Nat.card ↥(E₃ ⊔ E₂ : Subgroup G) * (Nat.card ↥(sigmaCore M) * Nat.card ↥K) := by
          rw [h1, h2, hcardE]
          ring
        exact Nat.eq_of_mul_eq_mul_left hUpos h3
      rw [hidx] at hrd
      rw [Set.notMem_compl_iff, Set.mem_union]
      rcases (Nat.Prime.dvd_mul hrp).1 hrd with h | h
      · exact Or.inl (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) r
          (Nat.mem_primeFactors.2 ⟨hrp, h, Nat.card_pos.ne'⟩))
      · exact Or.inr (hE₁κ r hrp (hKE₁' ▸ h))
  refine ⟨hKE₁', hUcomm, hENorm, hUhall, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hsetup.decomp.1, ?_, hsetup.decomp.2.2.1, ?_, ?_⟩
    · rw [hsupUK]; exact hsetup.decomp.2.1
    · rw [hsupUK]; exact hsetup.decomp.2.2.2.1
    · rw [hsupUK]; exact hsetup.decomp.2.2.2.2
  · exact ⟨le_sup_left, le_sup_right, by rw [hsupUK]; exact hENorm, rfl, hinfUK⟩
  · exact fun X hXK _ => le_normalizer_of_le_of_isMulCommutative hXK
  · rw [hKE₁']
    exact hE₁ne
  · intro X hXK hXne
    rw [hKE₁'] at hXK ⊢
    exact hfixE₁ X hXK hXne
  · exact fun k hk hk1 => hUfree k hk hk1

end

end CFSG.FeitThompson.Proofs
