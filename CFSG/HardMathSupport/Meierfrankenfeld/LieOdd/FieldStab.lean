module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem pow_char_eq_self_of_mul_mem {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    [CharP K p] {D : AddSubgroup K} (hD : D.index = p) {c : K} (hc : ∀ x ∈ D, c * x ∈ D) :
    c ^ p = c := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  set ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K with hι
  have hιmem : ∀ z : ZMod p, ∀ d ∈ D, ι z * d ∈ D := by
    intro z d hd
    have hz : ι z = ((z.val : ℕ) : K) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val z]
      exact map_natCast ι _
    rw [hz, ← nsmul_eq_mul]
    exact D.nsmul_mem hd _
  have hDtop : D ≠ ⊤ := by
    intro h
    rw [h, AddSubgroup.index_top] at hD
    omega
  obtain ⟨x0, hx0⟩ : ∃ x0 : K, x0 ∉ D := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hDtop (eq_top_iff.2 fun x _ => hcon x)
  let f : ZMod p → K ⧸ D := fun z => (ι z * x0 : K)
  have hinj : Function.Injective f := by
    intro z1 z2 h
    have h' : -(ι z1 * x0) + ι z2 * x0 ∈ D := QuotientAddGroup.eq.1 h
    have hdiff : ι (z2 - z1) * x0 ∈ D := by
      convert h' using 1
      rw [map_sub]
      ring
    by_contra hne
    have hw : z2 - z1 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have hu : ι ((z2 - z1)⁻¹) * ι (z2 - z1) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hw, map_one]
    apply hx0
    have : x0 = ι ((z2 - z1)⁻¹) * (ι (z2 - z1) * x0) := by
      rw [← mul_assoc, hu, one_mul]
    rw [this]
    exact hιmem _ _ hdiff
  have hcard : Fintype.card (ZMod p) = Fintype.card (K ⧸ D) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card]
    exact hD.symm
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  have hsurj : ∀ y : K, ∃ z : ZMod p, -(ι z * x0) + y ∈ D := by
    intro y
    obtain ⟨z, hz⟩ := hbij.2 (QuotientAddGroup.mk y)
    exact ⟨z, QuotientAddGroup.eq.1 hz⟩
  obtain ⟨z, hz⟩ := hsurj (c * x0)
  set w : K := c - ι z with hw_def
  have hwx0 : w * x0 ∈ D := by
    have : w * x0 = -(ι z * x0) + c * x0 := by rw [hw_def]; ring
    rw [this]
    exact hz
  have hall : ∀ x : K, w * x ∈ D := by
    intro x
    obtain ⟨m, hm⟩ := hsurj x
    have hd : w * (-(ι m * x0) + x) ∈ D := by
      have : w * (-(ι m * x0) + x) = c * (-(ι m * x0) + x) - ι z * (-(ι m * x0) + x) := by
        rw [hw_def]; ring
      rw [this]
      exact D.sub_mem (hc _ hm) (hιmem z _ hm)
    have hsplit : w * x = w * (-(ι m * x0) + x) + ι m * (w * x0) := by ring
    rw [hsplit]
    exact D.add_mem hd (hιmem m _ hwx0)
  have hw0 : w = 0 := by
    by_contra hne
    apply hDtop
    refine eq_top_iff.2 fun y _ => ?_
    have hy : w * (w⁻¹ * y) = y := by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [← hy]
    exact hall _
  have hc_eq : c = ι z := by
    rw [hw_def, sub_eq_zero] at hw0
    exact hw0
  rw [hc_eq, ← map_pow, ZMod.pow_card]

theorem pow_char_eq_self_of_sq {K : Type*} [Field K] [Finite K] {p e : ℕ} [Fact p.Prime]
    [CharP K p] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) (heo : Odd e) {a : K}
    (ha : (a ^ 2) ^ p = a ^ 2) : a ^ p = a := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ e := by rw [← Nat.card_eq_fintype_card, hK]
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hfrob : ∀ x : K, x ^ (p ^ e) = x := fun x => by
    rw [← hcard]
    exact FiniteField.pow_card x
  have h2 : (a ^ p) ^ 2 = a ^ 2 := by
    rw [← ha, ← pow_mul, ← pow_mul, mul_comm]
  have h3 : (a ^ p - a) * (a ^ p + a) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · exact sub_eq_zero.1 h
  · have hneg : a ^ p = -a := eq_neg_of_add_eq_zero_left h
    have hsq : a ^ (p ^ 2) = a := by
      rw [sq, pow_mul, hneg, Odd.neg_pow hodd, hneg, neg_neg]
    obtain ⟨k, hk⟩ := heo
    have hpow : ∀ n : ℕ, a ^ (p ^ (2 * n)) = a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, pow_mul, ih, hsq]
    have hodd_e : a ^ (p ^ e) = -a := by
      rw [hk, show p ^ (2 * k + 1) = p ^ (2 * k) * p by ring, pow_mul, hpow k, hneg]
    have hfin : -a = a := by rw [← hodd_e, hfrob]
    have h2a : (2 : K) * a = 0 := by linear_combination -hfin
    have h2ne : (2 : K) ≠ 0 := by
      intro h0
      have hdvd : p ∣ 2 := by
        rw [← CharP.cast_eq_zero_iff K p] at *
        exact_mod_cast h0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 hdvd)
    have ha0 : a = 0 := (mul_eq_zero.1 h2a).resolve_left h2ne
    rw [ha0, zero_pow (Fact.out : p.Prime).ne_zero]

theorem card_sq_pow_char_le {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] :
    Nat.card {a : Kˣ // ((a : K) ^ 2) ^ p = (a : K) ^ 2} ≤ 2 * (p - 1) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have : NeZero (2 * (p - 1)) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩
  have hfix : ∀ a : Kˣ, ((a : K) ^ 2) ^ p = (a : K) ^ 2 ↔ a ^ (2 * (p - 1)) = 1 := by
    intro a
    have hexp : ((a : K) ^ 2) ^ p = (a : K) ^ 2 * (a : K) ^ (2 * (p - 1)) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hcoe : ((a ^ (2 * (p - 1)) : Kˣ) : K) = (a : K) ^ (2 * (p - 1)) := by
      rw [Units.val_pow_eq_pow_val]
    rw [hexp, Units.ext_iff, Units.val_one, hcoe]
    constructor
    · intro h
      exact mul_left_cancel₀ (pow_ne_zero 2 a.ne_zero) (by rw [h, mul_one])
    · intro h
      rw [h, mul_one]
  refine le_trans (Nat.card_le_card_of_injective
    (fun a => (⟨a.1, (mem_rootsOfUnity _ _).2 ((hfix a.1).1 a.2)⟩ :
      rootsOfUnity (2 * (p - 1)) K)) ?_) (card_rootsOfUnity K (2 * (p - 1)))
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun x : rootsOfUnity (2 * (p - 1)) K => (x : Kˣ)) hab

theorem card_pow_char_units_le {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    [CharP K p] : Nat.card {a : Kˣ // (a : K) ^ p = a} ≤ p - 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have : NeZero (p - 1) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩
  have hfix : ∀ a : Kˣ, (a : K) ^ p = a ↔ a ^ (p - 1) = 1 := by
    intro a
    have hexp : (a : K) ^ p = (a : K) ^ (p - 1) * a := by
      rw [← pow_succ]
      congr 1
      omega
    have hcoe : ((a ^ (p - 1) : Kˣ) : K) = (a : K) ^ (p - 1) := by
      rw [Units.val_pow_eq_pow_val]
    rw [hexp, Units.ext_iff, Units.val_one, hcoe]
    constructor
    · intro h
      exact mul_right_cancel₀ a.ne_zero (by rw [h, one_mul])
    · intro h
      rw [h, one_mul]
  refine le_trans (Nat.card_le_card_of_injective
    (fun a => (⟨a.1, (mem_rootsOfUnity _ _).2 ((hfix a.1).1 a.2)⟩ :
      rootsOfUnity (p - 1) K)) ?_) (card_rootsOfUnity K (p - 1))
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun x : rootsOfUnity (p - 1) K => (x : Kˣ)) hab

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
