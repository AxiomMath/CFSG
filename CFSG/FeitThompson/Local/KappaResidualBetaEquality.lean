module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
import CFSG.FeitThompson.Local.KappaResidualFixedSpaceAndPrimeOrder
import CFSG.FeitThompson.Local.DerivedComplementCentralizesBetaPrimeHall
import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem sigmaPrimes_subset_primeFactors_natCard_sigmaCore [Finite G] {M : Subgroup G}
    (h : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) M) :
    sigmaPrimes M ⊆ (Nat.card ↥(sigmaCore M)).primeFactors := by
  intro p hp
  have hpp : p.Prime := prime_of_mem_sigmaPrimes hp
  have hpM : p ∣ Nat.card ↥M := dvd_natCard_of_mem_sigmaPrimes hp
  have hidx : ¬ p ∣ ((sigmaCore M).subgroupOf M).index := fun hdvd =>
    h.2.notMem_of_mem_primeFactors_index p
      (Nat.mem_primeFactors.2 ⟨hpp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hp
  have hcard := Subgroup.card_mul_index ((sigmaCore M).subgroupOf M)
  have hsub : Nat.card ↥((sigmaCore M).subgroupOf M) = Nat.card ↥(sigmaCore M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv
  rw [hsub] at hcard
  refine Nat.mem_primeFactors.2 ⟨hpp, ?_, Nat.card_pos.ne'⟩
  rcases (Nat.Prime.dvd_mul hpp).1 (hcard ▸ hpM) with hh | hh
  · exact hh
  · exact absurd hh hidx

theorem FBG_kappa_residual_beta_equality
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₃ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₄ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₅ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_kappa_residual_beta_equality.{u} := by
  intro G _ _ hG M K U hsetup
  have : Fintype G := Fintype.ofFinite G
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hG02 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hG07 : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable⟩
  obtain ⟨hHallOf, -, -⟩ := h₁ G hG02 M hsetup.isCoatom
  obtain ⟨-, -, V, -, -, -, -, hsemiM, -, hCSV, -, -, hVderiv⟩ :=
    FBG_kappa_residual_fixed_space_and_prime_order h₁ h₂ h₃ h₄ G hG M K U hsetup
  obtain ⟨H, hHhall, hHcomm⟩ :=
    FTS_derived_complement_centralizes_beta_prime_hall h₁ h₅ G hG07 M hsetup.isCoatom
      (V ⊔ K) hsemiM.right_le hsemiM
  have hVH : ⁅V, H⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono hVderiv le_rfl).trans hHcomm.le)
  have hHcent : H ≤ centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 ((Subgroup.commutator_comm H V).trans hVH)
  have hHbot : H = ⊥ := by
    have hle : H ≤ sigmaCore M ⊓ centralizer (V : Set G) := le_inf hHhall.1 hHcent
    rw [show sigmaCore M ⊓ centralizer (V : Set G) = ⊥ from hCSV] at hle
    exact le_bot_iff.1 hle
  have hidx : (H.subgroupOf (sigmaCore M)).index = Nat.card ↥(sigmaCore M) := by
    rw [hHbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
  refine Set.Subset.antisymm (fun p hp => ?_)
    (betaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard hG.isSolvable
      hsetup.isCoatom)
  have hpS : p ∈ (Nat.card ↥(sigmaCore M)).primeFactors :=
    sigmaPrimes_subset_primeFactors_natCard_sigmaCore hHallOf hp
  have hout := hHhall.2.notMem_of_mem_primeFactors_index p (hidx ▸ hpS)
  by_contra hpβ
  exact hout ⟨prime_of_mem_sigmaPrimes hp, hpβ⟩

end

end CFSG.FeitThompson.Proofs
