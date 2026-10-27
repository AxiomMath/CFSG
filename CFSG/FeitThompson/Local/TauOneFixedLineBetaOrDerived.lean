module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.TauOneAndDerivedComplementFixedCore
import CFSG.FeitThompson.Local.OutsideBetaInvariantSylowCentralizesDerived
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.OvergroupJoinsInvariantPrimeSubgroups
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.QuotientFittingInvariantComplement
import CFSG.FeitThompson.Local.PrimeExtensionMaximalInvariantSubgroup
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise
open CFSG.FeitThompson.Prep09

universe u

theorem FTS_tau_one_fixed_line_beta_or_derived
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₃ : Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₄ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₅ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₆ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_tau_one_fixed_line_beta_or_derived.{u} := by
  intro G _ _ hG M hM E hEM hsemi E₁ hE₁E hE₁ne hE₁hall q hq X hXc hXcard
  by_cases hqβ : q ∈ betaPrimes ↥M
  · exact Or.inl hqβ
  refine Or.inr ?_
  have hfin : Fintype G := Fintype.ofFinite G
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG8 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  obtain ⟨hHallOf, hHallG, -⟩ := h₁ G hG2 M hM
  have hXS : X ≤ sigmaCore M := hXc.trans inf_le_left
  have hqodd : Odd q := by
    refine hG.odd_natCard.of_dvd_nat ?_
    rw [← hXcard]
    exact (Subgroup.card_dvd_of_le le_top).trans (by simp)
  have hEσ : ∀ r ∈ (Nat.card ↥E).primeFactors, r ∉ sigmaPrimes M := by
    rw [← index_subgroupOf_left_eq hsemi]
    exact hHallOf.2.notMem_of_mem_primeFactors_index
  have hcopE : (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥E) := by
    refine Nat.coprime_of_dvd fun r hr hrS hrE => ?_
    exact hEσ r (Nat.mem_primeFactors.2 ⟨hr, hrE, Nat.card_pos.ne'⟩)
      (isPiSubgroup_iff.1 hHallG.isPiSubgroup r
        (Nat.mem_primeFactors.2 ⟨hr, hrS, Nat.card_pos.ne'⟩))
  have hcopE₁ : (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥E₁) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hE₁E) hcopE
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hES : E ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    hEM.trans (le_normalizer_sigmaCore M)
  have hE₁S : E₁ ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) := hE₁E.trans hES
  have hsolvSE : Group.IsSolvable ↥(sigmaCore M ⊔ E : Subgroup G) :=
    isSolvable_of_le_of_isSolvable (sup_le (sigmaCore_le M) hEM) hsolvM
  have hsolvSE₁ : Group.IsSolvable ↥(sigmaCore M ⊔ E₁ : Subgroup G) :=
    isSolvable_of_le_of_isSolvable (sup_le (sigmaCore_le M) (hE₁E.trans hEM)) hsolvM
  have hqπ : IsPiNumber ({q} : Set ℕ) q := by
    refine isPiNumber_iff.2 fun p hp => ?_
    rw [Nat.Prime.primeFactors hq] at hp
    simpa using hp
  obtain ⟨V, hVS, hVhall, -, hEV⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer (D := sigmaCore M)
      (A := E) (R := ⊥) hsolvSE hES hcopE ({q} : Set ℕ) bot_le
      (by simp [isPiNumber_one]) Subgroup.le_normalizer_of_normal
  have hVsylow : CFSG.FeitThompson.Prep08.IsSylowOf q V (sigmaCore M) :=
    (CFSG.FeitThompson.Prep08.isSylowOf_iff_natCard hq hVS).2
      (natCard_eq_pow_factorization_of_isHallSubgroup_singleton hq hVS hVhall)
  have hVE' : ⁅V, (⁅E, E⁆ : Subgroup G)⁆ = ⊥ :=
    FTS_outside_beta_invariant_sylow_centralizes_derived_complement h₁ h₆ G hG8 M E V q hM hEM
      hsemi hq hqodd hqβ hVsylow hEV
  have hVcE' : V ≤ centralizer ((⁅E, E⁆ : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hVE'
  have hXcE₁ : X ≤ centralizer (E₁ : Set G) := hXc.trans inf_le_right
  have hE₁X : E₁ ≤ normalizer (X : Set G) := le_normalizer_of_le_centralizer hXcE₁
  obtain ⟨W, hWS, hWhall, hXW, hE₁W⟩ :=
    exists_isHallSubgroup_subgroupOf_ge_le_normalizer_of_le_normalizer (D := sigmaCore M)
      (A := E₁) (R := X) hsolvSE₁ hE₁S hcopE₁ ({q} : Set ℕ) hXS (by rw [hXcard]; exact hqπ) hE₁X
  obtain ⟨c, hc, hcWV⟩ :=
    exists_mem_inf_centralizer_conj_inv_smul_eq_of_le_normalizer (π := ({q} : Set ℕ))
      hsolvSE₁ hE₁S hcopE₁ hWS hVS hWhall hVhall hE₁W (hE₁E.trans hEV)
  rw [Subgroup.mem_inf] at hc
  obtain ⟨hcS, hcE₁⟩ := hc
  have hXcV : (MulAut.conj c⁻¹ • X : Subgroup G) ≤ V := by
    rw [← hcWV]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hXW
  have hXcS : (MulAut.conj c⁻¹ • X : Subgroup G) ≤ sigmaCore M := hXcV.trans hVS
  have hXcE₁' : (MulAut.conj c⁻¹ • X : Subgroup G) ≤ centralizer (E₁ : Set G) :=
    conj_inv_smul_le_centralizer hcE₁ hXcE₁
  have hjoint := (FTS_tau_one_and_derived_complement_fixed_core h₁ h₂ h₃ h₄ h₅ G hG M hM E hEM
    hsemi E₁ hE₁E hE₁ne hE₁hall).1
  have hXcderived : (MulAut.conj c⁻¹ • X : Subgroup G) ≤ ⁅sigmaCore M, sigmaCore M⁆ :=
    le_trans (le_inf (le_inf hXcS hXcE₁') (le_inf hXcS (hXcV.trans hVcE'))) hjoint
  have hnorm : (MulAut.conj c • (⁅sigmaCore M, sigmaCore M⁆ : Subgroup G) : Subgroup G) =
      ⁅sigmaCore M, sigmaCore M⁆ :=
    conj_smul_eq_self_iff_mem_normalizer.2
      (le_normalizer_commutator_self (S := sigmaCore M) Subgroup.le_normalizer hcS)
  have hfinal := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj c).2 hXcderived
  rw [hnorm] at hfinal
  refine le_trans (le_of_eq ?_) hfinal
  rw [map_inv, smul_inv_smul]

end

end CFSG.FeitThompson.Proofs
