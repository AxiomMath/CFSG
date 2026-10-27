module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaFirstSupportedComplementAction
import CFSG.FeitThompson.Local.KappaHallThirdFactorSupportedComplement
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.KappaGlobalPairExhaustion
import CFSG.FeitThompson.Local.KappaFixedSubgroupDerivedAndHall
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideComplement
import CFSG.FeitThompson.Local.TwoBetaFixedCoresHallPosition
import CFSG.FeitThompson.Local.NonabelianAmbientSingleRankTwoPrime
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence

namespace CFSG.FeitThompson.Prep03

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] {X Y Z : Subgroup G} {c : G}

theorem conjSub_eq_self_of_mem {N : Subgroup G} (hc : c ∈ N) : conjSub N c = N := by
  ext x
  rw [mem_conjSub]
  refine ⟨fun h => ?_, fun h => N.mul_mem (N.mul_mem hc h) (N.inv_mem hc)⟩
  have h' := N.mul_mem (N.mul_mem (N.inv_mem hc) h) hc
  simpa [mul_assoc] using h'

theorem conjSub_normalizer (Y : Subgroup G) (c : G) :
    conjSub (normalizer (Y : Set G)) c = normalizer ((conjSub Y c : Subgroup G) : Set G) := by
  rw [conjSub_eq_map, conjSub_eq_map,
    Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj c⁻¹).bijective]

theorem conjSub_commutator (Y X : Subgroup G) (c : G) :
    conjSub ⁅Y, X⁆ c = ⁅conjSub Y c, conjSub X c⁆ := by
  rw [conjSub_eq_map, conjSub_eq_map, conjSub_eq_map, Subgroup.map_commutator]

@[simp] theorem conjSub_bot (c : G) : conjSub (⊥ : Subgroup G) c = ⊥ := conjSub_eq_bot_iff.2 rfl

theorem conjSub_inv_eq_conj_smul (Y : Subgroup G) (c : G) :
    conjSub Y c⁻¹ = MulAut.conj c • Y := by rw [conjSub_eq_map, inv_inv]; rfl

theorem isSemidirect_conjSub (h : IsSemidirect X Y Z) (c : G) :
    IsSemidirect (conjSub X c) (conjSub Y c) (conjSub Z c) :=
  ⟨conjSub_mono h.1 c, conjSub_mono h.2.1 c,
    by rw [← conjSub_normalizer]; exact conjSub_mono h.2.2.1 c,
    by rw [← conjSub_sup, h.2.2.2.1],
    by rw [← conjSub_inf, h.2.2.2.2, conjSub_bot]⟩

theorem IsThreeHallSetup.conjSub_of_mem {G : Type*} [Group G] [Fintype G]
    {M E E₁ E₂ E₃ : Subgroup G} (h : IsThreeHallSetup G M E E₁ E₂ E₃) {c : G} (hc : c ∈ E) :
    IsThreeHallSetup G M E (conjSub E₁ c) (conjSub E₂ c) (conjSub E₃ c) where
  ambient := h.ambient
  isCoatom := h.isCoatom
  decomp := h.decomp
  isHall_E₁ := by
    have h' := isHallPiOf_conjSub h.isHall_E₁ c; rwa [conjSub_eq_self_of_mem hc] at h'
  isHall_E₂ := by
    have h' := isHallPiOf_conjSub h.isHall_E₂ c; rwa [conjSub_eq_self_of_mem hc] at h'
  isHall_E₃ := by
    have h' := isHallPiOf_conjSub h.isHall_E₃ c; rwa [conjSub_eq_self_of_mem hc] at h'
  decomp_outer := by
    have h' := isSemidirect_conjSub h.decomp_outer c
    rwa [conjSub_eq_self_of_mem hc, conjSub_sup] at h'
  decomp_inner := by
    have h' := isSemidirect_conjSub h.decomp_inner c
    rwa [conjSub_sup] at h'
  isCyclic_E₁ := (isCyclic_conjSub_iff E₁ c).2 h.isCyclic_E₁
  isCyclic_E₃ := (isCyclic_conjSub_iff E₃ c).2 h.isCyclic_E₃
  le_derived_E₃ := by
    have h' := conjSub_mono h.le_derived_E₃ c
    rwa [conjSub_commutator, conjSub_eq_self_of_mem hc] at h'
  normal_E₂E₃ := by
    have h' := conjSub_mono h.normal_E₂E₃ c
    rwa [conjSub_eq_self_of_mem hc, conjSub_normalizer, conjSub_sup] at h'
  cent_E₃ := by
    have h0 : conjSub (cent E₃ (E : Set G)) c = conjSub (⊥ : Subgroup G) c := by rw [h.cent_E₃]
    rwa [cent_conjSub, ← coe_conjSub, conjSub_eq_self_of_mem hc, conjSub_bot] at h0

end

end CFSG.FeitThompson.Prep03

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep03 (IsAmbient IsSemidirect IsHallPiOf cent
  cent1 IsThreeHallSetup conjSub)

universe u

variable {G : Type*} [Group G]

theorem le_normalizer_bot' (K : Subgroup G) : K ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
  intro x _
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp

theorem isThreeHallSetup_of_isNormalizedTauHallSplitting {G : Type*} [Group G] [Fintype G]
    (hamb : IsAmbient G) {M E E₁ E₂ E₃ : Subgroup G} (hM : IsCoatom M)
    (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E)
    (h : _root_.CFSG.FeitThompson.IsNormalizedTauHallSplitting M E E₁ E₂ E₃) :
    IsThreeHallSetup G M E E₁ E₂ E₃ where
  ambient := hamb
  isCoatom := hM
  decomp := isSemidirect_of_isInternalSemidirectProduct hsd
  isHall_E₁ := isHallPiOf_of_isHallPiSubgroup_subgroupOf h.le_E₁ h.isHall_E₁
  isHall_E₂ := isHallPiOf_of_isHallPiSubgroup_subgroupOf h.le_E₂ h.isHall_E₂
  isHall_E₃ := isHallPiOf_of_isHallPiSubgroup_subgroupOf h.le_E₃ h.isHall_E₃
  decomp_outer := isSemidirect_of_isInternalSemidirectProduct h.outer
  decomp_inner := isSemidirect_of_isInternalSemidirectProduct h.inner
  isCyclic_E₁ := h.isCyclic_E₁
  isCyclic_E₃ := h.isCyclic_E₃
  le_derived_E₃ := h.le_commutator_E₃
  normal_E₂E₃ := h.normal_E₂_sup_E₃
  cent_E₃ := h.centralizer_E₃

theorem FNI_kappa_semiprime_complement_existence
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_tau12_fixed_plane_line_core_free.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonfree_third_factor_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u} := by
  intro G _ _ hamb M K hM hκ hK
  have hsimple := hamb.isSimpleGroup
  have hMne : M ≠ ⊤ := hM.1
  have hKM : K ≤ M := hK.1
  obtain ⟨p₀, hp₀κ⟩ := hκ
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hp₀ : p₀.Prime := prime_of_mem_kappaPrimes hp₀κ
    have hp₀M : p₀ ∣ Nat.card ↥M := (mem_kappaPrimes_iff.1 hp₀κ).2.1
    refine hK.2.2 p₀ (Nat.mem_primeFactors.2 ⟨hp₀, ?_, ?_⟩) hp₀κ
    · rw [hKbot, Subgroup.relIndex_bot_left]; exact hp₀M
    · rw [hKbot, Subgroup.relIndex_bot_left]; exact Nat.card_pos.ne'
  refine ⟨hKne, ?_⟩
  have hKσ : IsPiSubgroup ((sigmaPrimes M)ᶜ) K :=
    isPiSubgroup_iff.2 fun r hr =>
      Set.disjoint_left.1 (disjoint_kappaPrimes_sigmaPrimes M) (hK.2.1 r hr)
  obtain ⟨E, hKE, hsd⟩ := exists_isInternalSemidirectProduct_sigmaCore_ge
    hamb.not_isMulCommutative hamb.odd_natCard hamb.forall_isSolvable hM hKM hKσ
  have hEM : E ≤ M := hsd.right_le
  have hEsolv : Group.IsSolvable ↥E :=
    hamb.forall_isSolvable E fun h => hMne (top_le_iff.1 (h ▸ hEM))
  obtain ⟨E₁, E₂, E₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G
    (isOddSimpleMinimal_of_isAmbient hamb) M E ⟨hM, hsd⟩
  have hsetup : IsThreeHallSetup G M E E₁ E₂ E₃ :=
    isThreeHallSetup_of_isNormalizedTauHallSplitting hamb hM hsd hsplit
  by_cases hcase : ∀ r ∈ (Nat.card ↥K).primeFactors, r ∈ tau1Primes M
  ·
    obtain ⟨F₁, hF₁, hKF₁⟩ := exists_isHallPiSubgroupOf_ge_of_isPiSubgroup (π := tau1Primes M)
      hEsolv hKE (isPiSubgroup_iff.2 hcase)
    have hE₁Hall : CFSG.FeitThompson.IsHallPiSubgroupOf
        (tau1Primes M) E₁ E :=
      CFSG.FeitThompson.isHallPiSubgroupOf_iff.2
        ⟨hsetup.isHall_E₁.1, isHallPiSubgroup_subgroupOf_of_isHallPiOf hsetup.isHall_E₁⟩
    obtain ⟨c, hcE, hc⟩ := exists_mem_conj_smul_eq_of_isHallPiSubgroupOf hEsolv hE₁Hall hF₁
    have hconj : conjSub E₁ c⁻¹ = F₁ := by
      rw [CFSG.FeitThompson.Prep03.conjSub_inv_eq_conj_smul]; exact hc
    have hsetup' : IsThreeHallSetup G M E F₁ (conjSub E₂ c⁻¹) (conjSub E₃ c⁻¹) := by
      have := hsetup.conjSub_of_mem (E.inv_mem hcE)
      rwa [hconj] at this
    obtain ⟨hKeq, hUcomm, -, hUhall, hsd1, hsd2, hnorm, hcentne, hcenteq, hfree⟩ :=
      FNI_kappa_first_supported_complement_action h₁ h₂ h₃ h₄ h₅ h₇ h₈ G M E F₁
        (conjSub E₂ c⁻¹) (conjSub E₃ c⁻¹) K hsetup' hKne hK hKF₁
    refine ⟨conjSub E₃ c⁻¹ ⊔ conjSub E₂ c⁻¹, K, hUcomm, hUhall, hsd1, hsd2, hKne, ?_, le_refl K,
      hnorm, hcenteq, hcentne, hfree⟩
    have hsupE : (conjSub E₃ c⁻¹ ⊔ conjSub E₂ c⁻¹) ⊔ K = E := by
      rw [sup_assoc, hKeq]; exact hsetup'.decomp_outer.2.2.2.1
    rw [hsupE, hKeq]
    exact hsetup'.isHall_E₁
  ·
    push Not at hcase
    obtain ⟨p, hpK, hpτ₁⟩ := hcase
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpK
    have hpκ : p ∈ kappaPrimes M := hK.2.1 p hpK
    have hpM : p ∣ Nat.card ↥M := (mem_kappaPrimes_iff.1 hpκ).2.1
    have hpσ : p ∉ sigmaPrimes M := (mem_kappaPrimes_iff.1 hpκ).2.2.1
    have hpcyc : ∃ S : Sylow p ↥M, IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) := by
      obtain ⟨-, -, -, S, hS, -⟩ := mem_kappaPrimes_iff.1 hpκ
      exact ⟨S, hS⟩
    have hpτ₃ : p ∈ tau3Primes M :=
      (mem_tau1Primes_union_tau3Primes_of_isCyclic_sylow hp hpM hpσ hpcyc).resolve_left hpτ₁
    obtain ⟨hKE', hE₂, hE₁ne, hnorm, hcentne, hcenteq⟩ :=
      FNI_kappa_third_supported_complement_action h₁ h₆ G M E E₁ E₂ E₃ K hsetup hK hKE
        ⟨p, ⟨hpκ, hpτ₃⟩, Nat.dvd_of_mem_primeFactors hpK⟩
    have hcard : Nat.card ↥(sigmaCore M) * Nat.card ↥K = Nat.card ↥M := by
      have hsup := natCard_sup_of_le_normalizer (U := sigmaCore M) (B := E)
        (hEM.trans hsd.le_normalizer) hsd.disjoint
      rw [hsd.sup_eq] at hsup
      rw [hKE']; exact hsup.symm
    have hMprimes : ∀ r ∈ (Nat.card ↥M).primeFactors, r ∈ sigmaPrimes M ∪ kappaPrimes M := by
      intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrd : r ∣ Nat.card ↥(sigmaCore M) * Nat.card ↥K :=
        hcard ▸ Nat.dvd_of_mem_primeFactors hr
      rcases (Nat.Prime.dvd_mul hrp).1 hrd with h | h
      · exact Or.inl (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) r
          (Nat.mem_primeFactors.2 ⟨hrp, h, Nat.card_pos.ne'⟩))
      · exact Or.inr (hK.2.1 r (Nat.mem_primeFactors.2 ⟨hrp, h, Nat.card_pos.ne'⟩))
    refine ⟨⊥, E₁, inferInstance, ⟨bot_le, ?_, ?_⟩, ?_, ?_, hE₁ne, ?_, ?_, hnorm, hcenteq,
      hcentne, ?_⟩
    · simp
    · intro r hr
      rw [Subgroup.relIndex_bot_left] at hr
      exact fun hc => hc (hMprimes r hr)
    · rw [bot_sup_eq, hKE']; exact hsetup.decomp
    · exact ⟨bot_le, le_sup_right, le_normalizer_bot' _, rfl, by simp⟩
    · rw [bot_sup_eq, hKE']; exact hsetup.isHall_E₁
    · rw [hKE']; exact hsetup.isHall_E₁.1
    · intro k _ _
      simp [CFSG.FeitThompson.Prep03.cent1]

end

end CFSG.FeitThompson.Proofs
