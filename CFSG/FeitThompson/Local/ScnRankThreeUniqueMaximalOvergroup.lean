module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.CommutatorNormalizerUniqueOvergroup
import CFSG.FeitThompson.Local.NonuniqueAbelianEscapingCentralizer
import CFSG.FeitThompson.Local.OutsideSigmaSylowCentralPrimeElement
import CFSG.FeitThompson.Local.SelfCentralizingAbelianSylowConstraint
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem exists_isUniqueMaximalOvergroup_of_scn_three_le_elementaryAbelianPRank
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hp : p.Prime) (P : Sylow p G) {A : Subgroup G}
    (hAnormal : (A.subgroupOf (P : Subgroup G)).Normal)
    (hAself : centralizer (A : Set G) ⊓ (P : Subgroup G) = A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A) :
    ∃ M : Subgroup G, IsUniqueMaximalOvergroup A M := by
  have := Fact.mk hp
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_inf_centralizer_eq hAself
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h] at hArank
    have hle : elementaryAbelianPRank p ↥(⊥ : Subgroup G) ≤ Nat.card ↥(⊥ : Subgroup G) :=
      elementaryAbelianPRank_le_card hp.one_lt
    rw [Subgroup.card_bot] at hle
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAne
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hCle : centralizer (A : Set G) ≤ centralizer ({(a : G)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 a.2)
  have hCAtop : centralizer (A : Set G) ≠ ⊤ := fun h =>
    (centralizer_singleton_lt_top hna ha1').ne (top_le_iff.1 (h ▸ hCle))
  have hAC : A ≤ centralizer (A : Set G) := have := hAcomm; Subgroup.le_centralizer A
  have hAtop : A ≠ ⊤ := fun h => hCAtop (top_le_iff.1 (h ▸ hAC))
  refine exists_isUniqueMaximalOvergroup hAtop fun N N' hN hAN hN' hAN' => ?_
  by_contra hNN'
  have hAtwo : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ A ≤ M₁ ∧ A ≤ M₂ ∧ M₁ ≠ M₂ :=
    ⟨N, N', hN, hN', hAN, hAN', hNN'⟩
  obtain ⟨M, hM, hCM⟩ := exists_isCoatom_ge_of_ne_top hCAtop
  obtain ⟨B, hBA, hBcomm, hBexp, hBcard⟩ :=
    (mem_elementaryAbelianRanks_subgroup_iff (H := A) (d := 2) hp).1
      ((le_elementaryAbelianPRank_iff hp.one_lt).1 (by omega))
  have hBe : IsElementaryAbelian p B := isElementaryAbelian_iff.2
    ⟨IsMulCommutative.of_comm fun x y => Subtype.ext (hBcomm x x.2 y y.2), hBexp⟩
  obtain ⟨-, -, -, L, hL, hLM, -, hCAL⟩ :=
    exists_escaping_centralizer_of_isElementaryAbelian hp hna hodd hsolv hAcomm hN hN' hNN'
      hAN hAN' hBA hBe hBcard hM hCM
  have hMuniq := isUniqueMaximalOvergroup_normalizer_commutator_normalizer_of_scn hna hodd hsolv hp
    P hAnormal hAself hArank hAtwo hM hCM
  have hLuniq := isUniqueMaximalOvergroup_normalizer_commutator_normalizer_of_scn hna hodd hsolv hp
    P hAnormal hAself hArank hAtwo hL hCAL
  exact hLM (hMuniq.unique hLuniq).symm

theorem centralizer_le_of_isUniqueMaximalOvergroup_of_inf_centralizer_eq [Finite G]
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) {A M P : Subgroup G} (hAne : A ≠ ⊥)
    (hAself : centralizer (A : Set G) ⊓ P = A) (hAM : IsUniqueMaximalOvergroup A M) :
    centralizer (A : Set G) ≤ M := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAne
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hCle : centralizer (A : Set G) ≤ centralizer ({(a : G)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 a.2)
  have hCAtop : centralizer (A : Set G) ≠ ⊤ := fun h =>
    (centralizer_singleton_lt_top hna ha1').ne (top_le_iff.1 (h ▸ hCle))
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_inf_centralizer_eq hAself
  have hAC : A ≤ centralizer (A : Set G) := have := hAcomm; Subgroup.le_centralizer A
  exact hAM.le_of_ne_top hAC hCAtop

end

end CFSG.FeitThompson
