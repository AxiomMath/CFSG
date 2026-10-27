module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NilpotentSigmaPrimeSeparation
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson.Prep08
open Subgroup

universe u

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M N A : Subgroup G}

theorem sigmaPrimes_conjSubgroup (N : Subgroup G) (g : G) :
    sigmaPrimes (Prep08.conjSubgroup N g) = sigmaPrimes N := sigmaPrimes_conj_smul N g⁻¹

theorem le_sigmaCore_of_isPlaneAt [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    (hM : IsCoatom M) (hp : p ∈ sigmaPrimes M) (hAM : A ≤ M) (hA : IsPlaneAt p A) :
    A ≤ sigmaCore M := by
  have hpp := prime_of_mem_sigmaPrimes hp
  have hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M) :=
    (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM).isHallPiSubgroup
  have hcard : Nat.card ↥(A.subgroupOf M) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hA.natCard]
  have hpi : IsPiSubgroup (sigmaPrimes M) (A.subgroupOf M) := by
    refine isPiSubgroup_iff.2 fun q hq => ?_
    rw [hcard, Nat.primeFactors_pow _ two_ne_zero, hpp.primeFactors] at hq
    simpa [Finset.mem_singleton.1 hq] using hp
  have h := hHall.le_of_isPiSubgroup hpi
  intro x hx
  have hx' : (⟨x, hAM hx⟩ : ↥M) ∈ A.subgroupOf M := hx
  exact h hx'

theorem sigmaCore_inf_le_centralizer_of_inf_sigmaCore_eq_bot
    (h : sigmaCore N ⊓ sigmaCore M = ⊥) :
    sigmaCore N ⊓ M ≤ centralizer ((sigmaCore M ⊓ N : Subgroup G) : Set G) := by
  refine le_centralizer_of_le_normalizer_of_inf_eq_bot (H := M ⊓ N)
    (le_inf inf_le_right (inf_le_left.trans (sigmaCore_le N)))
    (le_inf (inf_le_left.trans (sigmaCore_le M)) inf_le_right)
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf (H := sigmaCore N) (K := M)
      (Subgroup.mem_inf.2 ⟨le_normalizer_sigmaCore N (Subgroup.mem_inf.1 hx).2,
        Subgroup.le_normalizer (Subgroup.mem_inf.1 hx).1⟩))
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf (H := sigmaCore M) (K := N)
      (Subgroup.mem_inf.2 ⟨le_normalizer_sigmaCore M (Subgroup.mem_inf.1 hx).1,
        Subgroup.le_normalizer (Subgroup.mem_inf.1 hx).2⟩)) ?_
  refine le_bot_iff.1 (le_trans ?_ h.le)
  exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)

theorem FTS_opposite_sigma_plane_core_intersection
    (h₁ : Statements.FTS_outside_sigma_plane_structure.{u}) :
    Statements.FTS_opposite_sigma_plane_core_intersection.{u} := by
  intro G _ _ hG M N A p hM hN hpM hpN hA hplane
  have := hG.isSimpleGroup
  have hpp := prime_of_mem_sigmaPrimes hpM
  obtain ⟨hnil, hcent, -⟩ := h₁ G hG N A p hN hpp hpN (hA.trans inf_le_right) hplane
  have hnc : ∀ g : G, M ≠ Prep08.conjSubgroup N g := fun g hg =>
    hpN (by rw [← sigmaPrimes_conjSubgroup N g, ← hg]; exact hpM)
  obtain ⟨-, hsep⟩ := FTS_nilpotent_sigma_prime_separation G hG N M hN hM hnc hnil
  have hAS : A ≤ sigmaCore M ⊓ N :=
    le_inf (le_sigmaCore_of_isPlaneAt hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM hpM (hA.trans inf_le_left) hplane) (hA.trans inf_le_right)
  have hJ : sigmaCore N ⊓ M ≤ centralizer ((A : Subgroup G) : Set G) :=
    (sigmaCore_inf_le_centralizer_of_inf_sigmaCore_eq_bot hsep).trans
      (Subgroup.centralizer_le hAS)
  exact le_bot_iff.1 (hcent.le.trans' (le_inf inf_le_left hJ))

end

end CFSG.FeitThompson.Proofs
