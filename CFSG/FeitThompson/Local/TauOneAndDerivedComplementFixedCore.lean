module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.TauOnePrimeCentralizerInclusion
import CFSG.FeitThompson.Local.OutsideSigmaPlaneComplementNormality
import CFSG.FeitThompson.Local.SignalizerNilpotentSupportingCore
import CFSG.FeitThompson.Local.SigmaCoreComplementFixedInDerived
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.InvariantComplementFittingSelfCentralizing
import CFSG.FeitThompson.Local.InvariantHallSubgroupsConjugate
import CFSG.FeitThompson.Local.PrimeExtensionMaximalInvariantSubgroup
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Local.CriticalRegularComplementFixedPoints
import CFSG.FeitThompson.Local.PrimeCentralizerAbelianCommutatorConjugates
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Local.CoprimeSolvableCommutatorDecomposition

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise
open CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem map_subtype_centralizer_subgroupOf {J X : Subgroup G} (hXJ : X ≤ J) :
    (centralizer ((X.subgroupOf J : Subgroup ↥J) : Set ↥J)).map J.subtype =
      J ⊓ centralizer (X : Set G) := by
  rw [centralizer_subgroupOf_of_le hXJ, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem sup_inf_centralizer_commutator_eq_of_le_normalizer [Finite G] {A K : Subgroup G}
    (hA : IsMulCommutative ↥A) (hKA : K ≤ normalizer (A : Set G))
    (hcop : (Nat.card ↥K).Coprime (Nat.card ↥A)) :
    (A ⊓ centralizer (K : Set G)) ⊔ ⁅A, K⁆ = A := by
  have hAL : A ≤ A ⊔ K := le_sup_left
  have hKL : K ≤ A ⊔ K := le_sup_right
  have hVnormal : (A.subgroupOf (A ⊔ K)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hKA)
  have hcop' : (Nat.card ↥(K.subgroupOf (A ⊔ K))).Coprime
      (Nat.card ↥(A.subgroupOf (A ⊔ K))) := by
    rw [natCard_subgroupOf_of_le' hKL, natCard_subgroupOf_of_le' hAL]; exact hcop
  have key := sup_inf_centralizer_commutator_eq (A.subgroupOf (A ⊔ K)) (K.subgroupOf (A ⊔ K))
    (isMulCommutative_subgroupOf_of_isMulCommutative hA) hcop'
  have hmap := congrArg (Subgroup.map (A ⊔ K).subtype) key
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (A ⊔ K).subtype_injective,
    map_subtype_centralizer_subgroupOf hKL, Subgroup.map_subgroupOf_eq_of_le hAL,
    commutator_subgroupOf hAL hKL,
    Subgroup.map_subgroupOf_eq_of_le (commutator_le_sup A K)] at hmap
  rwa [← inf_assoc, inf_eq_left.2 hAL] at hmap

theorem exists_prime_natCard_le_of_ne_bot [Finite G] {Y : Subgroup G} (hY : Y ≠ ⊥) :
    ∃ (r : ℕ) (R : Subgroup G), r.Prime ∧ R ≤ Y ∧ Nat.card ↥R = r ∧ r ∣ Nat.card ↥Y := by
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (fun h => hY (Subgroup.card_eq_one.1 h))
  obtain ⟨x, hxY, hx⟩ := exists_mem_orderOf_eq_of_dvd hr hrd
  exact ⟨r, zpowers x, hr, Subgroup.zpowers_le.2 hxY, by rw [Nat.card_zpowers, hx], hrd⟩

theorem FTS_tau_one_and_derived_complement_fixed_core
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (_h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₄ : Statements.FTS_outside_sigma_plane_structure.{u})
    (_h₅ : Statements.FTS_plane_maximal_overgroups.{u}) :
    Statements.FTS_tau_one_and_derived_complement_fixed_core.{u} := by
  intro G _ _ hG M hM E hEM hsemi E₁ hE₁E hE₁ne hE₁hall
  have hG4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG7 : CFSG.FeitThompson.IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG8 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  set U : Subgroup G := centIn (sigmaCore M) (E₁ : Set G) ⊓
    centIn (sigmaCore M) ((⁅E, E⁆ : Subgroup G) : Set G)
  have hUS : U ≤ sigmaCore M := le_trans inf_le_left inf_le_left
  have htwo : (tauTwoPrimes M).Nonempty → U = ⊥ := by
    rintro ⟨p, hp⟩
    obtain ⟨hpp, hpσ, hprank⟩ := mem_tauTwoPrimes_iff.1 hp
    obtain ⟨hπE, hrank, -, -, -, -, -, -⟩ :=
      FNI_sigma_complement_prime_data h₁ G hG4 M E ⟨hM, hsemi⟩
    obtain ⟨A0, hA0M, hA0⟩ := exists_isPlaneAt_of_elementaryAbelianPRank_eq_two hpp hprank
    have hpM : p ∣ Nat.card ↥M :=
      dvd_trans (by rw [hA0.2]; exact dvd_pow_self p two_ne_zero)
        (Subgroup.card_dvd_of_le hA0M)
    have hpE : p ∈ _root_.CFSG.FeitThompson.primeDivisorsOf ↥E := by
      rw [hπE]
      exact ⟨_root_.CFSG.FeitThompson.mem_primeDivisorsOf.2 ⟨hpp, hpM⟩, hpσ⟩
    obtain ⟨A, hAE, hA⟩ :=
      exists_isPlaneAt_of_elementaryAbelianPRank_eq_two hpp (by rw [(hrank p hpE).1, hprank])
    have hAM : A ≤ M := hAE.trans hEM
    have hAexp : ∀ x ∈ A, x ^ p = 1 := (isElementaryAbelian_iff.1 hA.1).2
    have hAnorm : E ≤ normalizer (A : Set G) :=
      FTS_outside_sigma_plane_complement_normality h₄ G hG8 M A E p hM hpp hpσ hAM hA hEM
        hsemi hAE
    have hSA : sigmaCore M ⊓ centralizer (A : Set G) = ⊥ :=
      (h₄ G hG8 M A p hM hpp hpσ hAM hA).2.1
    obtain ⟨r, R, hr, hRE₁, hRcard, hrd⟩ := exists_prime_natCard_le_of_ne_bot hE₁ne
    have hrτ : r ∈ tau1Primes M := by
      refine isPiSubgroup_iff.1 hE₁hall.isPiSubgroup r ?_
      rw [natCard_subgroupOf_of_le' hE₁E]
      exact Nat.mem_primeFactors.2 ⟨hr, hrd, Nat.card_pos.ne'⟩
    have hpnotE₁ : ¬ p ∣ Nat.card ↥E₁ := by
      intro hd
      have hmem : p ∈ tau1Primes M := by
        refine isPiSubgroup_iff.1 hE₁hall.isPiSubgroup p ?_
        rw [natCard_subgroupOf_of_le' hE₁E]
        exact Nat.mem_primeFactors.2 ⟨hpp, hd, Nat.card_pos.ne'⟩
      have h2 := (mem_tau1Primes_iff.1 hmem).2.2.2.1
      rw [hprank] at h2
      exact absurd h2 (by norm_num)
    have hcop : (Nat.card ↥E₁).Coprime (Nat.card ↥A) := by
      rw [hA.2]
      exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpnotE₁).symm
    have hsplit : (A ⊓ centralizer (E₁ : Set G)) ⊔ ⁅A, E₁⁆ = A :=
      sup_inf_centralizer_commutator_eq_of_le_normalizer hA.isMulCommutative
        (hE₁E.trans hAnorm) hcop
    have hUcomm : U ≤ centralizer (A : Set G) := by
      intro u hu
      obtain ⟨⟨huS, huE₁⟩, ⟨-, huE'⟩⟩ := hu
      have hcommAE : (⁅A, E₁⁆ : Subgroup G) ≤ ⁅E, E⁆ := commutator_mono hAE hE₁E
      have hu2 : u ∈ centralizer ((⁅A, E₁⁆ : Subgroup G) : Set G) :=
        Subgroup.centralizer_le (by exact_mod_cast hcommAE) huE'
      have hu1 : u ∈ centralizer ((A ⊓ centralizer (E₁ : Set G) : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨hyA, hyE₁⟩ := hy
        by_cases hy1 : y = 1
        · simp [hy1]
        ·
          have hyord : orderOf y = p := by
            have hd : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one (hAexp y hyA)
            rcases (Nat.dvd_prime hpp).1 hd with h | h
            · exact absurd (orderOf_eq_one_iff.1 h) hy1
            · exact h
          have hyR : (zpowers y : Subgroup G) ≤ centIn E (R : Set G) := by
            refine le_inf (Subgroup.zpowers_le.2 (hAE hyA)) (Subgroup.zpowers_le.2 ?_)
            exact Subgroup.mem_centralizer_iff.2 fun g hg =>
              Subgroup.mem_centralizer_iff.1 hyE₁ g (hRE₁ hg)
          have hincl := FTS_tau_one_prime_centralizer_inclusion h₃ G hG M hM E hEM hsemi
            r p hr hpp hrτ R (hRE₁.trans hE₁E) hRcard (zpowers y) hyR
            (by rw [Nat.card_zpowers, hyord])
          have huR : u ∈ centIn (sigmaCore M) (R : Set G) :=
            ⟨huS, Subgroup.centralizer_le (by exact_mod_cast hRE₁) huE₁⟩
          exact Subgroup.mem_centralizer_iff.1 (hincl huR).2 y (Subgroup.mem_zpowers y)
      rw [← hsplit]
      exact mem_centralizer_sup hu1 hu2
    rw [eq_bot_iff, ← hSA]
    exact le_inf hUS hUcomm
  refine ⟨?_, htwo⟩
  rcases Set.eq_empty_or_nonempty (tauTwoPrimes M) with hτ₂ | hτ₂
  ·
    obtain ⟨F₁, F₂, F₃, hsplit, -⟩ :=
      FNI_sigma_complement_three_factors h₁ G hG4 M E ⟨hM, hsemi⟩
    have hF₂ : F₂ = ⊥ := by
      refine Subgroup.card_eq_one.1 ?_
      by_contra hne
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hmem : q ∈ (Nat.card ↥(F₂.subgroupOf E)).primeFactors := by
        rw [natCard_subgroupOf_of_le' hsplit.le_E₂]
        exact Nat.mem_primeFactors.2 ⟨hq, hqd, Nat.card_pos.ne'⟩
      have hq2 := isPiSubgroup_iff.1 hsplit.isHall_E₂.isPiSubgroup q hmem
      rw [hτ₂] at hq2
      exact hq2
    have hEsup : F₃ ⊔ F₁ = E := by
      have h := hsplit.outer.sup_eq
      rwa [hF₂, bot_sup_eq] at h
    have hcommE : (⁅E, E⁆ : Subgroup G) ≤ E := (commutator_le_sup E E).trans (by simp)
    have hFsup : (⁅E, E⁆ : Subgroup G) ⊔ F₁ = E :=
      le_antisymm (sup_le hcommE hsplit.le_E₁)
        (le_trans (le_of_eq hEsup.symm)
          (sup_le (le_sup_of_le_left hsplit.le_commutator_E₃) le_sup_right))
    have hEne : E ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hEM))
    have hEsolv : Group.IsSolvable ↥E := hG.isSolvable_of_ne_top E hEne
    obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup
      (isHallSubgroup_iff_isHallPiSubgroup.2 hsplit.isHall_E₁)
      (isHallSubgroup_iff_isHallPiSubgroup.2 hE₁hall)
    have hgG : MulAut.conj (g : G) • F₁ = E₁ := conj_smul_eq_of_subgroupOf hsplit.le_E₁ hE₁E hg
    have hEE₁ : (⁅E, E⁆ : Subgroup G) ⊔ E₁ = E := by
      have h1 : MulAut.conj (g : G) • ((⁅E, E⁆ : Subgroup G) ⊔ F₁) = E := by
        rw [hFsup, conj_smul_eq_self_iff_mem_normalizer]
        exact Subgroup.le_normalizer g.2
      rwa [Subgroup.smul_sup, hgG, conj_smul_eq_self_iff_mem_normalizer.2
        (le_normalizer_commutator_self (S := E) Subgroup.le_normalizer g.2)] at h1
    have hUE : U ≤ sigmaCore M ⊓ centralizer (E : Set G) := by
      intro u hu
      obtain ⟨⟨huS, huE₁⟩, ⟨-, huE'⟩⟩ := hu
      exact ⟨huS, hEE₁ ▸ mem_centralizer_sup huE' huE₁⟩
    exact hUE.trans (FTS_complement_fixed_core_contained_derived G hG7 M hM E hEM hsemi)
  · rw [htwo hτ₂]; exact bot_le

end

end CFSG.FeitThompson.Proofs
