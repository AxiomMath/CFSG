module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix

variable {K : Type*} [Field K]

theorem exists_primitiveRoot_of_dvd [Finite K] {d : ℕ} (hd : d ∣ Nat.card K - 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hg
  have hprim : IsPrimitiveRoot g (Nat.card K - 1) := by
    rw [← hg]; exact IsPrimitiveRoot.orderOf g
  have hk0 : Nat.card K - 1 ≠ 0 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
  have hkd : (Nat.card K - 1) / d ∣ Nat.card K - 1 := Nat.div_dvd_of_dvd hd
  have he0 : (Nat.card K - 1) / d ≠ 0 := fun h0 => by
    have := Nat.eq_zero_of_dvd_of_div_eq_zero hd h0
    exact hk0 this
  have h := hprim.pow_of_dvd he0 hkd
  rw [Nat.div_div_self hd hk0] at h
  exact ⟨((g ^ ((Nat.card K - 1) / d) : Kˣ) : K), IsPrimitiveRoot.coe_units_iff.mpr h⟩

theorem card_sl_three_eq [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 3) K) =
      (Nat.card K - 1) ^ 2 * (Nat.card K ^ 3 * (((Nat.card K - 1) ^ 2 + 3 * (Nat.card K - 1) + 3) *
        ((Nat.card K - 1) + 2))) := by
  have : Fintype K := Fintype.ofFinite K
  have h := card_SL_mul_card_units (n := Fin 3) (R := K)
  rw [card_GL_field, Fin.prod_univ_three, Nat.card_units] at h
  have hq : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
  rw [hq] at h
  have h1 : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨t, ht⟩ : ∃ t, Nat.card K = t + 1 := ⟨Nat.card K - 1, by omega⟩
  rw [ht] at h ⊢
  simp only [Nat.add_sub_cancel] at h ⊢
  have ht0 : 0 < t := by omega
  refine Nat.eq_of_mul_eq_mul_right ht0 ?_
  rw [h]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have e0 : (t + 1) ^ 3 - 1 = t * (t ^ 2 + 3 * t + 3) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e1 : (t + 1) ^ 3 - (t + 1) = (t + 1) * (t * (t + 2)) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e2 : (t + 1) ^ 3 - (t + 1) ^ 2 = (t + 1) ^ 2 * t := by
    apply Nat.sub_eq_of_eq_add; ring
  rw [e0, e1, e2]
  ring

theorem card_le_of_isPGroup_sl_three [Finite K] {m t₀ : ℕ} (ht : Nat.card K - 1 = 3 ^ m * t₀)
    (ht0 : ¬ 3 ∣ t₀) (hm : 1 ≤ m) {R : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hR : IsPGroup 3 R) : Nat.card R ≤ 3 ^ (2 * m + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hR.exists_card_eq
  have hdvd : Nat.card R ∣ Nat.card (SpecialLinearGroup (Fin 3) K) := Subgroup.card_subgroup_dvd_card R
  rw [hj, card_sl_three_eq] at hdvd
  set t := Nat.card K - 1 with htdef
  have hq : Nat.card K = t + 1 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  rw [hq] at hdvd
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  set t' := 3 ^ m' * t₀ with ht'def
  have htt' : t = 3 * t' := by rw [ht, ht'def]; ring
  have h1 : t ^ 2 = 3 ^ (2 * (m' + 1)) * t₀ ^ 2 := by rw [ht]; ring
  have h2 : t ^ 2 + 3 * t + 3 = 3 * (3 * t' ^ 2 + 3 * t' + 1) := by rw [htt']; ring
  have hexpr : t ^ 2 * ((t + 1) ^ 3 * ((t ^ 2 + 3 * t + 3) * (t + 2))) =
      3 ^ (2 * (m' + 1) + 1) * (t₀ ^ 2 * ((t + 1) ^ 3 * ((3 * t' ^ 2 + 3 * t' + 1) * (t + 2)))) := by
    rw [h2, h1]; ring
  rw [hexpr] at hdvd
  have hw : ¬ 3 ∣ t₀ ^ 2 * ((t + 1) ^ 3 * ((3 * t' ^ 2 + 3 * t' + 1) * (t + 2))) := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact ht0 (Nat.prime_three.dvd_of_dvd_pow h)
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · have := Nat.prime_three.dvd_of_dvd_pow h
        omega
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
        · have h3 : 3 ∣ 3 * t' ^ 2 + 3 * t' := ⟨t' ^ 2 + t', by ring⟩
          have := (Nat.dvd_add_right h3).mp h
          omega
        · omega
  have hcop : Nat.Coprime (3 ^ j) (t₀ ^ 2 * ((t + 1) ^ 3 * ((3 * t' ^ 2 + 3 * t' + 1) * (t + 2)))) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hw)
  have hj2 : 3 ^ j ∣ 3 ^ (2 * (m' + 1) + 1) := hcop.dvd_of_dvd_mul_right hdvd
  have hjle : j ≤ 2 * (m' + 1) + 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hj2
  rw [hj]
  exact Nat.pow_le_pow_right (by norm_num) hjle

end CFSG.HardMathSupport.Curtis.Coordinator
