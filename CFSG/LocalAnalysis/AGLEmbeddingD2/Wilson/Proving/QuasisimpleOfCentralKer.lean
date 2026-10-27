module

public import CFSG.Assembly.Defs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Subgroup
open scoped commutatorElement

theorem commutatorElement_mem_center_of_card_eq_prime_cube {H : Type*} [Group H] {p : ℕ}
    [hp : Fact p.Prime] (hH : Nat.card H = p ^ 3) (a b : H) :
    ⁅a, b⁆ ∈ Subgroup.center H := by
  have : Finite H := Nat.finite_of_card_ne_zero (by
    rw [hH]; exact pow_ne_zero 3 hp.out.ne_zero)
  obtain ⟨j, hj0, hjc⟩ := IsPGroup.card_center_eq_prime_pow hH (by norm_num)
  have hQ : Nat.card (H ⧸ Subgroup.center H) * Nat.card (Subgroup.center H) = p ^ 3 := by
    rw [← hH, mul_comm]
    exact Subgroup.card_mul_index (Subgroup.center H)
  obtain ⟨i, hi3, hQi⟩ := (Nat.dvd_prime_pow hp.out).1 (Dvd.intro _ hQ)
  have hi2 : i ≠ 3 := by
    rintro rfl
    have hQ' := hQ
    rw [hQi] at hQ'
    have hc1 : Nat.card (Subgroup.center H) = 1 :=
      Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos 3) (by rw [mul_one]; exact hQ')
    have hjc' := hjc
    rw [hc1] at hjc'
    have := Nat.one_lt_pow (by omega : j ≠ 0) hp.out.one_lt
    omega
  have hi : i < 3 := lt_of_le_of_ne hi3 hi2
  have hQcomm : (QuotientGroup.mk a : H ⧸ Subgroup.center H) * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a := by
    interval_cases i
    · have hQ1 : Nat.card (H ⧸ Subgroup.center H) = 1 := by simpa using hQi
      have : Subsingleton (H ⧸ Subgroup.center H) := (Nat.card_eq_one_iff_unique.1 hQ1).1
      exact Subsingleton.elim _ _
    · have hQp : Nat.card (H ⧸ Subgroup.center H) = p := by simpa using hQi
      have : IsCyclic (H ⧸ Subgroup.center H) := isCyclic_of_prime_card hQp
      have hcom := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (Subgroup.center H)) (QuotientGroup.ker_mk' _).le
      have hab : a * b = b * a := hcom.is_comm.comm a b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab]
    · have hcom := IsPGroup.isMulCommutative_of_card_eq_prime_sq hQi
      exact hcom.is_comm.comm _ _
  have hmk : (QuotientGroup.mk (⁅a, b⁆ : H) : H ⧸ Subgroup.center H) = 1 := by
    rw [commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hQcomm]
    group
  exact (QuotientGroup.eq_one_iff _).1 hmk

theorem commute_commutatorElement_of_card_eq_prime_cube {G : Type*} [Group G] {p : ℕ}
    [Fact p.Prime] {P : Subgroup G} (hP : Nat.card P = p ^ 3) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) : Commute a ⁅a, b⁆ ∧ Commute b ⁅a, b⁆ := by
  have hz := commutatorElement_mem_center_of_card_eq_prime_cube hP
    (⟨a, ha⟩ : P) ⟨b, hb⟩
  have hcoe : ((⁅(⟨a, ha⟩ : P), ⟨b, hb⟩⁆ : P) : G) = ⁅a, b⁆ := rfl
  rw [Subgroup.mem_center_iff] at hz
  constructor
  · have e := congrArg Subtype.val (hz ⟨a, ha⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe] at e
    exact e
  · have e := congrArg Subtype.val (hz ⟨b, hb⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe] at e
    exact e

end CFSG.AGLEmbeddingD2.Wilson.Proving
