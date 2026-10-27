module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.KappaCandidateCyclicTorus
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import Mathlib

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise CFSG.FeitThompson.Prep03

variable {G : Type*} [Group G]

theorem isSemidirect_bot_sup_right {K : Subgroup G} :
    IsSemidirect ((⊥ : Subgroup G) ⊔ K) ⊥ K :=
  ⟨bot_le, le_sup_right, by rw [Subgroup.normalizer_eq_top]; exact le_top, rfl, bot_inf_eq _⟩

theorem eq_bot_of_isSemidirect_of_isSemidirect [Finite G] {M S U K : Subgroup G}
    (h : IsSemidirect M S K) (hU : IsSemidirect M S (U ⊔ K))
    (hUK : IsSemidirect (U ⊔ K) U K) : U = ⊥ := by
  have h1 := natCard_of_isSemidirect h
  have h2 := natCard_of_isSemidirect hU
  have h3 := natCard_of_isSemidirect hUK
  have key : Nat.card ↥S * Nat.card ↥K * 1 = Nat.card ↥S * Nat.card ↥K * Nat.card ↥U := by
    rw [mul_one]
    calc Nat.card ↥S * Nat.card ↥K = Nat.card ↥M := h1.symm
      _ = Nat.card ↥S * Nat.card ↥U * Nat.card ↥K := by rw [h2, h3, mul_assoc]
      _ = Nat.card ↥S * Nat.card ↥K * Nat.card ↥U := by ring
  have hpos : 0 < Nat.card ↥S * Nat.card ↥K := Nat.mul_pos Nat.card_pos Nat.card_pos
  exact Subgroup.card_eq_one.1 (Nat.eq_of_mul_eq_mul_left hpos key).symm

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup Pointwise CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FNI_kappa_trivial_residual_prime_fixed_core
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_candidate_family_common_factors.{u})
    (h₃ : Statements.FNI_kappa_candidate_has_nontrivial_residual.{u})
    (h₄ : Statements.FNI_kappa_local_pair.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u} := by
  intro G _ _ M K A Z hsetup hsplit
  obtain ⟨-, -, -, -, -, -, -, hdirect, hZcyc, -⟩ := h₄ G M K A Z hsetup
  have hKcyc : IsCyclic ↥K := Subgroup.isCyclic_of_le hdirect.1
  have hno : ¬ ∃ U : Subgroup G, U ≠ ⊥ ∧ IsSemidirect M (sigmaCore M) (U ⊔ K) ∧
      IsSemidirect (U ⊔ K) U K := by
    rintro ⟨U, hUne, hU, hUK⟩
    exact hUne (eq_bot_of_isSemidirect_of_isSemidirect hsplit hU hUK)
  have hsplit' : IsSemidirect M (sigmaCore M) ((⊥ : Subgroup G) ⊔ K) := by rwa [bot_sup_eq]
  have hM' : (⁅M, M⁆ : Subgroup G) = sigmaCore M := by
    have h := (FNI_kappa_derived_complement h₄ h₅ G M K A Z hsetup).2.2 ⊥ hsplit'
      isSemidirect_bot_sup_right
    rwa [sup_bot_eq] at h
  obtain ⟨hex, -, -, -⟩ := h₂ G M K A Z (kappaFamily M K) hsetup rfl
  obtain ⟨KT, hKTself, hKThall⟩ := hex
  have hfam : IsKappaFamilySetup G M K A Z (kappaFamily M K) KT :=
    ⟨hsetup, rfl, hKTself, hKThall⟩
  have hAprime : (Nat.card ↥A).Prime :=
    (FNI_kappa_candidate_cyclic_torus h₁ h₂ h₃ h₅ h₆ h₇ h₈ G M K A Z _ KT hfam).2.2.2.2 hno
  obtain ⟨-, U₀, E₁, -, -, -, -, -, -, -, -, hcent, -, -⟩ :=
    h₅ G hsetup.ambient M K hsetup.isCoatom hsetup.kappa_nonempty hsetup.isHall_K
  refine ⟨hKcyc, hM', hAprime, ?_⟩
  intro X hXK hXne
  rw [hcent X hXK hXne, hsetup.A_eq]

end CFSG.FeitThompson.Proofs

end
