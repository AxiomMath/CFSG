module

public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.FeitThompson.Local.FrattiniQuotientAutomorphismKernelPGroup
import CFSG.FeitThompson.OddOrder.QuotientFrobeniusAction
import CFSG.FeitThompson.OddOrder.FreeActionKernelCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {A K : Type*} [Group A] [Group K]

theorem prime_dvd_card_sub_one_of_fixedPointFree [Finite K] {p : ℕ} (hp : p.Prime)
    {ρ : A →* MulAut K} {a : A} (hcard : Nat.card A = p)
    (hfree : MonoidHom.FixedPointFree (ρ a : K → K)) : p ∣ Nat.card K - 1 := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.pos.ne')
  let _inst : MulDistribMulAction A K := MulDistribMulAction.compHom K ρ
  rw [← hcard]
  refine card_dvd_card_sub_one_of_smul_eq_self A K fun k hk c hc => ?_
  by_contra hc1
  exact hk (hfree k (apply_eq_self_of_mem_zpowers ρ (show ρ c k = k from hc)
    (zpowers_eq_top_of_ne_one hp hcard hc1 ▸ Subgroup.mem_top a)))

section Main

variable [Finite K] [Group.IsSolvable K] {p : ℕ} {ρ : A →* MulAut K} {a : A}

theorem one_lt_card_quotient_commutator [Nontrivial K] : 1 < Nat.card (K ⧸ commutator K) := by
  have h : Nat.card (K ⧸ commutator K) ≠ 1 := by
    rw [← Subgroup.index_eq_card, Ne, Subgroup.index_eq_one]
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := K)).ne
  have := Nat.card_pos (α := K ⧸ commutator K)
  omega

theorem fixedPointFree_quotientAut_commutator (hp : p.Prime) (hcard : Nat.card A = p)
    (ha : Subgroup.zpowers a = ⊤) (hfree : MonoidHom.FixedPointFree (ρ a : K → K)) :
    MonoidHom.FixedPointFree
      ((isInvariantSubgroup_of_characteristic ρ (commutator K)).quotientAut a :
        K ⧸ commutator K → K ⧸ commutator K) :=
  fixedPointFree_quotientAut hp hcard ha hfree
    (isInvariantSubgroup_of_characteristic ρ (commutator K))

theorem prime_dvd_card_quotient_commutator_sub_one (hp : p.Prime) (hcard : Nat.card A = p)
    (ha : Subgroup.zpowers a = ⊤) (hfree : MonoidHom.FixedPointFree (ρ a : K → K)) :
    p ∣ Nat.card (K ⧸ commutator K) - 1 :=
  prime_dvd_card_sub_one_of_fixedPointFree hp hcard
    (fixedPointFree_quotientAut_commutator hp hcard ha hfree)

theorem add_one_le_card_quotient_commutator [Nontrivial K] (hp : p.Prime) (hcard : Nat.card A = p)
    (ha : Subgroup.zpowers a = ⊤) (hfree : MonoidHom.FixedPointFree (ρ a : K → K)) :
    p + 1 ≤ Nat.card (K ⧸ commutator K) := by
  have hd := prime_dvd_card_quotient_commutator_sub_one hp hcard ha hfree
  have h1 := one_lt_card_quotient_commutator (K := K)
  have := Nat.le_of_dvd (by omega) hd
  omega

theorem prime_dvd_card_quotient_commutator_sub_one_and_add_one_le [Nontrivial K] (hp : p.Prime)
    (hcard : Nat.card A = p) (ha : Subgroup.zpowers a = ⊤)
    (hfree : MonoidHom.FixedPointFree (ρ a : K → K)) :
    p ∣ Nat.card (K ⧸ commutator K) - 1 ∧ p + 1 ≤ Nat.card (K ⧸ commutator K) :=
  ⟨prime_dvd_card_quotient_commutator_sub_one hp hcard ha hfree,
    add_one_le_card_quotient_commutator hp hcard ha hfree⟩

theorem prime_dvd_card_quotient_commutator_sub_one_and_add_one_le' [Nontrivial K] (hp : p.Prime)
    (hcard : Nat.card A = p) (ha : Subgroup.zpowers a = ⊤)
    (hfix : FixedPoints.subgroup ρ.range K = ⊥) :
    p ∣ Nat.card (K ⧸ commutator K) - 1 ∧ p + 1 ≤ Nat.card (K ⧸ commutator K) :=
  prime_dvd_card_quotient_commutator_sub_one_and_add_one_le hp hcard ha
    ((fixedPoints_range_eq_bot_iff_fixedPointFree ρ ha).1 hfix)

theorem prime_dvd_card_abelianization_sub_one (hp : p.Prime) (hcard : Nat.card A = p)
    (ha : Subgroup.zpowers a = ⊤) (hfree : MonoidHom.FixedPointFree (ρ a : K → K)) :
    p ∣ Nat.card (Abelianization K) - 1 :=
  prime_dvd_card_quotient_commutator_sub_one hp hcard ha hfree

theorem add_one_le_card_abelianization [Nontrivial K] (hp : p.Prime) (hcard : Nat.card A = p)
    (ha : Subgroup.zpowers a = ⊤) (hfree : MonoidHom.FixedPointFree (ρ a : K → K)) :
    p + 1 ≤ Nat.card (Abelianization K) :=
  add_one_le_card_quotient_commutator hp hcard ha hfree

end Main

end CFSG.FeitThompson
