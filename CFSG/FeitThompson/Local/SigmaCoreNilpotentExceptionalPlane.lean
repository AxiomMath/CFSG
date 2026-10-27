module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaCoreConjugateTrivialExceptionalPlane
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
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

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup Pointwise

universe u

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem inf_sigmaCore_eq_bot_of_natCard_eq_prime {M E : Subgroup G} (hp : p.Prime)
    (hpM : p ∉ sigmaPrimes M) (hE : Nat.card ↥E = p) : sigmaCore M ⊓ E = ⊥ := by
  by_contra hne
  have hdvd : Nat.card ↥(sigmaCore M ⊓ E) ∣ p := hE ▸ Subgroup.card_dvd_of_le inf_le_right
  have hcard : Nat.card ↥(sigmaCore M ⊓ E) = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hne
    · exact h
  have hdvdS : p ∣ Nat.card ↥(sigmaCore M) := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  exact hpM (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
    (Nat.mem_primeFactors.2 ⟨hp, hdvdS, Nat.card_pos.ne'⟩))

theorem exists_notMem_conjBy_eq_of_notMem_sigmaPrimes {M P : Subgroup G} (hp : p.Prime)
    (hpM : p ∉ sigmaPrimes M) (hdvd : p ∣ Nat.card ↥M) (hP : IsSylowSubgroupOf p P M) :
    ∃ g : G, g ∉ M ∧ conjBy P g = P := by
  have hNP : ¬ normalizer (P : Set G) ≤ M := fun h =>
    hpM ((mem_sigmaPrimes_iff_exists_subgroup hp).2 ⟨hdvd, P, hP.1, hP.2, h⟩)
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.1 hNP
  exact ⟨g, hgM, mem_normalizer_iff_conj_smul_eq.1 (inv_mem hgN)⟩

theorem FTS_exceptional_core_nilpotent
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_exceptional_core_nilpotent.{u} := by
  intro G _ _ hG p M A₀ A P hc
  have hp : p.Prime := hc.prime
  have hM : IsCoatom M := hc.isCoatom
  have hAM : A ≤ M := hc.le_of_A.trans hc.le_of_P
  have hAcard : Nat.card ↥A = p ^ 2 := hc.isElementaryAbelianPlane.natCard hp.ne_zero
  have hpM : p ∣ Nat.card ↥M := by
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le hAM)
    rw [hAcard]; exact dvd_pow_self p two_ne_zero
  obtain ⟨g, hgM, hPg⟩ :=
    exists_notMem_conjBy_eq_of_notMem_sigmaPrimes hp hc.notMem_sigmaPrimes hpM hc.isSylowSubgroupOf
  have hAMg : A ≤ conjBy M g := by
    refine hc.le_of_A.trans ?_
    rw [← hPg]
    exact conjBy_le_conjBy_iff.2 hc.le_of_P
  obtain ⟨-, hCA₀⟩ :=
    FTS_exceptional_core_conjugate_intersection h₁ h₂ G hG p M A₀ A P hc g hgM hAMg
  set E : Subgroup G := conjBy A₀ g with hEdef
  have hEcard : Nat.card ↥E = p := by rw [hEdef, natCard_conjBy, hc.natCard_A₀]
  have hEM : E ≤ M := by
    refine le_trans ?_ hc.le_of_P
    rw [hEdef, ← hPg]
    exact conjBy_le_conjBy_iff.2 (hc.le_of_A₀.trans hc.le_of_A)
  have hEbot : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    exact hp.one_lt.ne hEcard
  have hSne : sigmaCore M ≠ ⊤ := fun h =>
    hM.1 (top_le_iff.1 (h ▸ sigmaCore_le M))
  have : Group.IsSolvable ↥(sigmaCore M) := hG.isSolvable _ hSne
  refine isNilpotent_of_isSolvable_of_le_normalizer
    (inf_sigmaCore_eq_bot_of_natCard_eq_prime hp hc.notMem_sigmaPrimes hEcard) hEbot
    (hEM.trans (le_normalizer_sigmaCore M)) ?_
  intro e he hne
  rw [centralizer_singleton_eq_of_natCard_eq_prime hp hEcard he hne]
  exact hCA₀

end

end CFSG.FeitThompson.Proofs
