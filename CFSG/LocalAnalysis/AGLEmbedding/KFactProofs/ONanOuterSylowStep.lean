module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.AGLEmbedding.OuterSylow

@[expose] def Stp (p a b k : ℕ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ padicValNat p b = padicValNat p a + k ∧ (p ∣ b → p ∣ a) ∧ (p ∣ a → 1 ≤ k)

namespace Stp

variable {p : ℕ} [hp : Fact p.Prime]

theorem one : Stp p 1 1 0 :=
  ⟨one_ne_zero, one_ne_zero, by simp, id, fun h => absurd h hp.out.not_dvd_one⟩

theorem mul {a b c d k l : ℕ} (h : Stp p a b k) (h' : Stp p c d l) :
    Stp p (a * c) (b * d) (k + l) := by
  obtain ⟨ha, hb, hv, hba, hak⟩ := h
  obtain ⟨hc, hd, hv', hdc, hcl⟩ := h'
  refine ⟨mul_ne_zero ha hc, mul_ne_zero hb hd, ?_, ?_, ?_⟩
  · rw [padicValNat.mul hb hd, padicValNat.mul ha hc, hv, hv']
    ring
  · intro h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
    · exact Dvd.dvd.mul_right (hba h) c
    · exact Dvd.dvd.mul_left (hdc h) a
  · intro h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
    · have := hak h
      omega
    · have := hcl h
      omega

theorem prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {a b k : ι → ℕ}
    (h : ∀ i ∈ s, Stp p (a i) (b i) (k i)) :
    Stp p (∏ i ∈ s, a i) (∏ i ∈ s, b i) (∑ i ∈ s, k i) := by
  induction s using Finset.induction_on with
  | empty => simpa using one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem mul' {a b c d : ℕ} (h : ∃ k, Stp p a b k) (h' : ∃ k, Stp p c d k) :
    ∃ k, Stp p (a * c) (b * d) k :=
  let ⟨_, h⟩ := h
  let ⟨_, h'⟩ := h'
  ⟨_, h.mul h'⟩

theorem prod' {ι : Type*} [DecidableEq ι] (s : Finset ι) {a b : ι → ℕ}
    (h : ∀ i ∈ s, ∃ k, Stp p (a i) (b i) k) : ∃ k, Stp p (∏ i ∈ s, a i) (∏ i ∈ s, b i) k := by
  choose! k hk using h
  exact ⟨_, prod s hk⟩

omit hp in
theorem valuation_lt {a b k : ℕ} (h : Stp p a b k) (hb : p ∣ b) :
    padicValNat p a < padicValNat p b := by
  obtain ⟨-, -, hv, hba, hak⟩ := h
  have := hak (hba hb)
  omega

theorem pow_q (hp3 : 3 ≤ p) {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) :
    Stp p (q ^ N) ((q ^ p) ^ N) (N * (p - 1) * padicValNat p q) := by
  have hq0 : q ≠ 0 := by omega
  refine ⟨pow_ne_zero _ hq0, pow_ne_zero _ (pow_ne_zero _ hq0), ?_, ?_, ?_⟩
  · simp only [padicValNat.pow]
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  · intro h
    exact dvd_pow (hp.out.dvd_of_dvd_pow (hp.out.dvd_of_dvd_pow h)) (by omega)
  · intro h
    have hv := one_le_padicValNat_of_dvd hq0 (hp.out.dvd_of_dvd_pow h)
    have : 1 ≤ (p - 1) * padicValNat p q := Nat.mul_pos (by omega) hv
    calc 1 ≤ (p - 1) * padicValNat p q := this
      _ ≤ N * (p - 1) * padicValNat p q := by
        rw [mul_assoc]
        exact Nat.le_mul_of_pos_left _ (by omega)

theorem dvd_pow_sub_one_iff {x : ℕ} (hx : 1 ≤ x) : p ∣ x ^ p - 1 ↔ p ∣ x - 1 := by
  have h1 : ((x ^ p - 1 : ℕ) : ZMod p) = ((x - 1 : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hx), Nat.cast_sub hx, Nat.cast_pow, ZMod.pow_card]
  rw [← ZMod.natCast_eq_zero_iff, h1, ZMod.natCast_eq_zero_iff]

theorem dvd_pow_add_one_iff {x : ℕ} : p ∣ x ^ p + 1 ↔ p ∣ x + 1 := by
  have h1 : ((x ^ p + 1 : ℕ) : ZMod p) = ((x + 1 : ℕ) : ZMod p) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_pow, ZMod.pow_card]
  rw [← ZMod.natCast_eq_zero_iff, h1, ZMod.natCast_eq_zero_iff]

theorem sub_prime_pow (hodd : Odd p) {x : ℕ} (hx : 2 ≤ x) :
    Stp p (x - 1) (x ^ p - 1) (if p ∣ x - 1 then 1 else 0) := by
  have hpx : 1 < x ^ p := Nat.one_lt_pow hp.out.ne_zero (by omega)
  refine ⟨by omega, by omega, ?_, (dvd_pow_sub_one_iff (by omega)).1, fun h => by simp [h]⟩
  by_cases h : p ∣ x - 1
  · have hnx : ¬ p ∣ x := fun hpx' => hp.out.not_dvd_one (by
      have h2 := Nat.dvd_sub hpx' h
      rwa [show x - (x - 1) = 1 by omega] at h2)
    have := padicValNat.pow_sub_pow (y := 1) hodd (by omega) h hnx hp.out.ne_zero
    simpa [h, padicValNat_self] using this
  · have h' : ¬ p ∣ x ^ p - 1 := fun h'' => h ((dvd_pow_sub_one_iff (by omega)).1 h'')
    simp [h, padicValNat.eq_zero_of_not_dvd h, padicValNat.eq_zero_of_not_dvd h']

theorem add_prime_pow (hodd : Odd p) {x : ℕ} (hx : 1 ≤ x) :
    Stp p (x + 1) (x ^ p + 1) (if p ∣ x + 1 then 1 else 0) := by
  refine ⟨by omega, by omega, ?_, dvd_pow_add_one_iff.1, fun h => by simp [h]⟩
  by_cases h : p ∣ x + 1
  · have hnx : ¬ p ∣ x := fun hpx' => hp.out.not_dvd_one ((Nat.dvd_add_right hpx').1 h)
    have := padicValNat.pow_add_pow (y := 1) hodd h hnx hodd
    simpa [h, padicValNat_self] using this
  · have h' : ¬ p ∣ x ^ p + 1 := fun h'' => h (dvd_pow_add_one_iff.1 h'')
    simp [h, padicValNat.eq_zero_of_not_dvd h, padicValNat.eq_zero_of_not_dvd h']

theorem sub_pow (hodd : Odd p) {q e : ℕ} (hq : 2 ≤ q) (he : 1 ≤ e) :
    Stp p (q ^ e - 1) ((q ^ p) ^ e - 1) (if p ∣ q ^ e - 1 then 1 else 0) := by
  rw [pow_right_comm]
  exact sub_prime_pow hodd (by
    have := Nat.one_lt_pow (n := e) (by omega) (show 1 < q by omega)
    omega)

theorem add_pow (hodd : Odd p) {q e : ℕ} (hq : 1 ≤ q) :
    Stp p (q ^ e + 1) ((q ^ p) ^ e + 1) (if p ∣ q ^ e + 1 then 1 else 0) := by
  rw [pow_right_comm]
  exact add_prime_pow hodd (Nat.one_le_pow _ _ hq)

theorem sub_pow' (hodd : Odd p) {q : ℕ} (hq : 2 ≤ q) (e : ℕ) (he : 1 ≤ e := by norm_num) :
    Stp p (q ^ e - 1) ((q ^ p) ^ e - 1) (if p ∣ q ^ e - 1 then 1 else 0) :=
  sub_pow hodd hq he

theorem add_pow' (hodd : Odd p) {q : ℕ} (hq : 1 ≤ q) (e : ℕ) :
    Stp p (q ^ e + 1) ((q ^ p) ^ e + 1) (if p ∣ q ^ e + 1 then 1 else 0) :=
  add_pow hodd hq

theorem sub_one (hodd : Odd p) {q : ℕ} (hq : 2 ≤ q) :
    Stp p (q - 1) (q ^ p - 1) (if p ∣ q - 1 then 1 else 0) :=
  sub_prime_pow hodd hq

end Stp

end CFSG.AGLEmbedding.OuterSylow
