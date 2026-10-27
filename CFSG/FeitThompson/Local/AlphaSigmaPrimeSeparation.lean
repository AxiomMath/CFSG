module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
public import CFSG.FeitThompson.Definitions.SigmaPrimesAndSigmaCore
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.ConjugationUniqueMaximalOvergroup
import CFSG.FeitThompson.OddOrder.SigmaSylowIsAmbientSylow
import CFSG.FeitThompson.OddOrder.RankThreeUniquenessMaximalOvergroup
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Order
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Positivity.Finset

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {G : Type*} [Group G] {p : ℕ} {M T : Subgroup G}

private theorem exists_ambient_sylow_isUniqueMaximalOvergroup [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) (hp : p.Prime)
    (hpM : p ∈ sigmaPrimes M) (hrank : 3 ≤ elementaryAbelianPRank p G) :
    ∃ P : Subgroup G, Nat.card ↥P = p ^ (Nat.card G).factorization p ∧
      IsUniqueMaximalOvergroup P M := by
  obtain ⟨-, P, hPM, hPcard, -⟩ := (mem_sigmaPrimes_iff_exists_subgroup hp).1 hpM
  have hPG : Nat.card ↥P = p ^ (Nat.card G).factorization p :=
    natCard_eq_pow_factorization_of_mem_sigmaPrimes hpM hPM hPcard
  have hPrank : 3 ≤ elementaryAbelianPRank p ↥P := by
    rw [elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hp hPG]; exact hrank
  have hPtop : P ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hPM))
  obtain ⟨N, hN⟩ := exists_isUniqueMaximalOvergroup_of_three_le_maxElementaryAbelianPRank
    hna hodd hsolv hPtop (hPrank.trans (elementaryAbelianPRank_le_maxElementaryAbelianPRank hp))
  refine ⟨P, hPG, ?_⟩
  rw [hN.eq_of_isCoatom hM hPM]
  exact hN

theorem notMem_sigmaPrimes_of_mem_alphaPrimes_of_not_conj [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) (hT : IsCoatom T)
    (hMT : ∀ g : G, MulAut.conj g • M ≠ T) (hp : p ∈ alphaPrimes ↥M) : p ∉ sigmaPrimes T := by
  intro hpT
  obtain ⟨hpp, hrankM⟩ := mem_alphaPrimes.1 hp
  have := Fact.mk hpp
  have hrank : 3 ≤ elementaryAbelianPRank p G :=
    hrankM.trans (elementaryAbelianPRank_subgroup_le hpp.one_lt M)
  have hpM : p ∈ sigmaPrimes M := alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM hp
  obtain ⟨P, hPG, hPM⟩ :=
    exists_ambient_sylow_isUniqueMaximalOvergroup hna hodd hsolv hM hpp hpM hrank
  obtain ⟨Q, hQG, hQT⟩ :=
    exists_ambient_sylow_isUniqueMaximalOvergroup hna hodd hsolv hT hpp hpT hrank
  obtain ⟨g, hg⟩ := exists_conj_smul_eq hPG hQG
  have hconj : IsUniqueMaximalOvergroup Q (MulAut.conj g • M) := by
    rw [← hg]; exact hPM.smul g
  exact hMT g (hconj.unique hQT)

theorem disjoint_alphaPrimes_sigmaPrimes_of_not_conj [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) (hT : IsCoatom T)
    (hMT : ∀ g : G, MulAut.conj g • M ≠ T) :
    Disjoint (alphaPrimes ↥M) (sigmaPrimes T) :=
  Set.disjoint_left.2 fun _ hp =>
    notMem_sigmaPrimes_of_mem_alphaPrimes_of_not_conj hna hodd hsolv hM hT hMT hp

theorem disjoint_sigmaPrimes_alphaPrimes_of_not_conj [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M) (hT : IsCoatom T)
    (hMT : ∀ g : G, MulAut.conj g • M ≠ T) :
    Disjoint (sigmaPrimes M) (alphaPrimes ↥T) := by
  refine (disjoint_alphaPrimes_sigmaPrimes_of_not_conj hna hodd hsolv hT hM ?_).symm
  intro g h
  exact hMT g⁻¹ (by rw [← h, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul])

end

end CFSG.FeitThompson
