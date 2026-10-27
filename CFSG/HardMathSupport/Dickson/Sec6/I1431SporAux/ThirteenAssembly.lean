module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMNo65Monster

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Blueprint CFSG.Monster.Existence

section Abstract

variable {G : Type} [Group G]

theorem noOrder65_of_cases [Finite G] (hE : MonsterExistenceStatement G)
    (hB65 : NoOrder 65 NativeSporadic.B) (hCo65 : NoOrder 65 NativeSporadic.Co1)
    (hn : ∀ x : G, orderOf x = 13 →
      ¬ 5 ∣ Nat.card (centralizer ({x} : Set G)) ∨ ¬ 5 ∣ (invComm x).ncard) :
    NoOrder 65 G := by
  refine noOrder65_of_involution hE hB65 hCo65 fun g hg => ?_
  have hg0 : g ≠ 1 := by
    rintro rfl
    simp at hg
  have hord_pow : ∀ n : ℕ, n ≠ 0 → orderOf (g ^ n) = 65 / Nat.gcd 65 n := fun n hn => by
    rw [orderOf_pow' _ hn, hg]
  have hx : orderOf (g ^ 5) = 13 := by rw [hord_pow 5 (by norm_num)]; norm_num
  have hz : orderOf (g ^ 13) = 5 := by rw [hord_pow 13 (by norm_num)]; norm_num
  have hzx : g ^ 13 * g ^ 5 = g ^ 5 * g ^ 13 := (Commute.pow_pow_self g 13 5).eq
  rcases hn _ hx with hC | hI
  · exfalso
    apply hC
    have hmem : g ^ 13 ∈ centralizer ({g ^ 5} : Set G) := mem_centralizer_singleton_iff.2 hzx
    have := Subgroup.orderOf_dvd_natCard (centralizer ({g ^ 5} : Set G)) hmem
    rwa [hz] at this
  · have hmod := ncard_modEq_fixed (p := 5) (by norm_num) hz
      (conj_closed_invComm (x := g ^ 5) (a := g ^ 13) hzx)
    have hne : {s | s ∈ invComm (g ^ 5) ∧ g ^ 13 * s = s * g ^ 13}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Set.ncard_empty] at hmod
      exact hI ((Nat.modEq_zero_iff_dvd).1 hmod)
    obtain ⟨t, ⟨ht2, ht1, htx⟩, htz⟩ := hne
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨t, orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1, ?_⟩
    have hg_eq : g = (g ^ 5) ^ 8 * ((g ^ 13) ^ 3)⁻¹ := by group
    have hc1 : Commute t (g ^ 5) := htx
    have hc2 : Commute t (g ^ 13) := htz.symm
    have hc : Commute t g := by
      conv_rhs => rw [hg_eq]
      exact (hc1.pow_right 8).mul_right (hc2.pow_right 3).inv_right
    exact hc.eq

end Abstract

end CFSG.HardMathSupport.Dickson.Sec6.I1431
