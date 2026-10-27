module

public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.OddOrder.SigmaPrimesWellDefined
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions
import CFSG.FeitThompson.Representations.TensorAndDualCharacters
import Mathlib.Data.Complex.Basic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M N : Subgroup G}

theorem eq_of_conj_smul_eq_of_normalizer_le [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hpM : p ∈ sigmaPrimes M)
    {X : Subgroup G} (hXbot : ⊥ < X) (hXM : X ≤ M) (hXp : IsPGroup p X)
    (hXN : normalizer (X : Set G) ≤ N) {g : G} (hg : N = MulAut.conj g • M) : M = N := by
  have hXNle : X ≤ N := Subgroup.le_normalizer.trans hXN
  obtain ⟨c, hc, hcMN⟩ := exists_mem_centralizer_conj_smul_localOvergroups hna hodd hsolv hM hpM
    hXbot.ne' hXp (N₁ := M) (N₂ := N) (mem_localOvergroups_iff.2 ⟨⟨1, by simp⟩, hXM⟩)
    (mem_localOvergroups_iff.2 ⟨⟨g, hg⟩, hXNle⟩)
  have hcN : c ∈ N := hXN (Subgroup.centralizer_le_normalizer _ hc)
  have hfix : MulAut.conj c • N = N := by
    rw [conj_smul_eq_map_conj]; exact map_conj_eq_self hcN
  exact smul_left_cancel (MulAut.conj c) (hcMN.trans hfix.symm)

theorem not_exists_conj_smul_eq_of_normalizer_le [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (_hN : IsCoatom N) (hMN : M ≠ N) (hpM : p ∈ sigmaPrimes M)
    {X : Subgroup G} (hXbot : ⊥ < X) (hXM : X ≤ M) (hXp : IsPGroup p X)
    (hXN : normalizer (X : Set G) ≤ N) :
    ¬ ∃ g : G, N = MulAut.conj g • M := by
  rintro ⟨g, hg⟩
  exact hMN (eq_of_conj_smul_eq_of_normalizer_le hna hodd hsolv hM hpM hXbot hXM hXp hXN hg)

theorem conj_smul_ne_of_normalizer_le [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    (hM : IsCoatom M) (hN : IsCoatom N) (hMN : M ≠ N) (hpM : p ∈ sigmaPrimes M)
    {X : Subgroup G} (hXbot : ⊥ < X) (hXM : X ≤ M) (hXp : IsPGroup p X)
    (hXN : normalizer (X : Set G) ≤ N) (g : G) : MulAut.conj g • M ≠ N := fun h =>
  not_exists_conj_smul_eq_of_normalizer_le hna hodd hsolv hM hN hMN hpM hXbot hXM hXp hXN
    ⟨g, h.symm⟩

end

end CFSG.FeitThompson
