module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.MaximalPlaneCentralizerPrimeTorsion
public import CFSG.FeitThompson.Representations.PrimeCentralTorsionCharacteristic
public import Mathlib.GroupTheory.Nilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped commutatorElement

open Subgroup

variable {p : ℕ} {R : Type*} [Group R] {E : Subgroup R}

theorem mem_upperCentralSeries_two_iff {x : R} :
    x ∈ Subgroup.upperCentralSeries R 2 ↔ ⁅zpowers x, (⊤ : Subgroup R)⁆ ≤ center R := by
  have key : ∀ y : R, y ∈ Subgroup.upperCentralSeries R 2 ↔ ∀ z : R, ⁅y, z⁆ ∈ center R :=
    fun y => by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
        Subgroup.upperCentralSeries_one]
  rw [key]
  refine ⟨fun h => Subgroup.commutator_le.2 ?_, fun h y => ?_⟩
  · intro a ha b _
    exact (key a).1 (Subgroup.zpowers_le.2 ((key x).2 h) ha) b
  · exact h (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x) (Subgroup.mem_top y))

theorem centerTorsionBy_le_of_maximal
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E) :
    centerTorsionBy R p ≤ E := fun _ hz =>
  setOf_pow_eq_one_center_subset_of_maximal hE
    ⟨mem_center_of_mem_centerTorsionBy hz, pow_eq_one_of_mem_centerTorsionBy hz⟩

theorem centerTorsionBy_ne_bot_of_isPGroup [Finite R] [Nontrivial R] (hp : p.Prime)
    (hRp : IsPGroup p R) : centerTorsionBy R p ≠ ⊥ := by
  have := Fact.mk hp
  obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hRp).mp ‹Nontrivial R›
  exact centerTorsionBy_ne_bot hp hcard hn

theorem centerTorsionBy_ne_of_maximal [Finite R] (hp : p.Prime)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    centerTorsionBy R p ≠ E := by
  intro hZE
  have hEcen : (E : Set R) ⊆ (center R : Set R) := by
    rw [← hZE]; exact centerTorsionBy_le_center p
  have h2 := elementaryAbelianPRank_centralizer_of_maximal hp hE hplane
  rw [Subgroup.centralizer_eq_top_iff_subset.2 hEcen,
    elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt (Subgroup.topEquiv (G := R))] at h2
  omega

theorem natCard_centerTorsionBy_of_maximal [Finite R] (hp : p.Prime) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    Nat.card (centerTorsionBy R p) = p := by
  have hnt : Nontrivial R := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    rw [elementaryAbelianPRank_eq_zero_of_subsingleton hp.one_lt] at hrank
    omega
  have hbot : centerTorsionBy R p ≠ ⊥ := centerTorsionBy_ne_bot_of_isPGroup hp hRp
  have hle := centerTorsionBy_le_of_maximal hE
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp (hplane ▸ Subgroup.card_dvd_of_le hle)
  interval_cases k
  · exact absurd (Subgroup.card_eq_one.mp (by simpa using hkeq)) hbot
  · simpa using hkeq
  · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [hplane, hkeq]))
      (centerTorsionBy_ne_of_maximal hp hE hplane hrank)

theorem centerTorsionBy_le_and_natCard_eq_of_maximal [Finite R] (hp : p.Prime) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hrank : 3 ≤ elementaryAbelianPRank p R) :
    centerTorsionBy R p ≤ E ∧ Nat.card (centerTorsionBy R p) = p :=
  ⟨centerTorsionBy_le_of_maximal hE, natCard_centerTorsionBy_of_maximal hp hRp hE hplane hrank⟩

end

end CFSG.FeitThompson
