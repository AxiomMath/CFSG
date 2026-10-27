module

public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Choose.Dvd
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDefs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Finset

theorem not_dvd_choose_add_mul {p : ℕ} (hp : p.Prime) (A j m : ℕ) (hj : j < p) :
    ¬ p ∣ Nat.choose A (j + p * m) ↔ j ≤ A % p ∧ ¬ p ∣ Nat.choose (A / p) m := by
  have := Fact.mk hp
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := A) (k := j + p * m) (p := p)
  have hj1 : (j + p * m) % p = j := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hj2 : (j + p * m) / p = m := by
    rw [Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hj, zero_add]
  rw [hj1, hj2] at h
  have h2 : p ∣ Nat.choose A (j + p * m) ↔ p ∣ Nat.choose (A % p) j * Nat.choose (A / p) m := by
    rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
    exact ⟨fun h0 => h.symm.trans h0, fun h0 => h.trans h0⟩
  rw [h2, hp.dvd_mul]
  have h3 : p ∣ Nat.choose (A % p) j ↔ A % p < j := by
    constructor
    · intro hd
      by_contra hle
      have hc := hp.coprime_choose_of_lt (Nat.mod_lt A hp.pos) (not_lt.mp hle)
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc (dvd_refl p) hd)
    · intro hlt
      rw [Nat.choose_eq_zero_of_lt hlt]
      exact dvd_zero p
  rw [h3, not_or, not_lt]

theorem digitProd_succ (p n A : ℕ) : digitProd p (n + 1) A = (A % p + 1) * digitProd p n (A / p) := by
  unfold digitProd
  rw [Finset.prod_range_succ']
  have h : ∀ i ∈ range n, (A / p ^ (i + 1) % p + 1) = (A / p) / p ^ i % p + 1 := by
    intro i _
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
  rw [Finset.prod_congr rfl h, mul_comm, pow_zero, Nat.div_one]

theorem card_filter_not_dvd_choose {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∀ A : ℕ, A < p ^ n →
      ((range (p ^ n)).filter (fun m => ¬ p ∣ Nat.choose A m)).card = digitProd p n A := by
  induction n with
  | zero =>
    intro A hA
    have hA0 : A = 0 := by simpa using hA
    subst hA0
    rw [pow_zero, Finset.range_one, Finset.filter_singleton]
    simp [digitProd, Nat.dvd_one, hp.ne_one]
  | succ n ih =>
    intro A hA
    have hA' : A / p < p ^ n := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      rwa [← pow_succ]
    have key : ((range (p ^ (n + 1))).filter (fun m => ¬ p ∣ Nat.choose A m)).card =
        (range (A % p + 1) ×ˢ ((range (p ^ n)).filter (fun m => ¬ p ∣ Nat.choose (A / p) m))).card := by
      refine Finset.card_nbij' (fun m => (m % p, m / p)) (fun x => x.1 + p * x.2) ?_ ?_ ?_ ?_
      · intro m hm
        simp only [mem_coe, mem_filter, mem_range, mem_product] at hm ⊢
        obtain ⟨hm1, hm2⟩ := hm
        have hmp : m % p < p := Nat.mod_lt _ hp.pos
        have h0 := not_dvd_choose_add_mul hp A (m % p) (m / p) hmp
        rw [Nat.mod_add_div] at h0
        have h' := h0.mp hm2
        refine ⟨Nat.lt_succ_of_le h'.1, ?_, h'.2⟩
        rw [Nat.div_lt_iff_lt_mul hp.pos]
        rwa [← pow_succ]
      · intro x hx
        simp only [mem_coe, mem_filter, mem_range, mem_product] at hx ⊢
        obtain ⟨hx1, hx2, hx3⟩ := hx
        have hxp : x.1 < p := lt_of_le_of_lt (Nat.le_of_lt_succ hx1) (Nat.mod_lt _ hp.pos)
        refine ⟨?_, ?_⟩
        · calc x.1 + p * x.2 < p * (x.2 + 1) := by
                rw [mul_add, mul_one, add_comm (p * x.2)]
                exact Nat.add_lt_add_right hxp _
            _ ≤ p * p ^ n := Nat.mul_le_mul_left _ hx2
            _ = p ^ (n + 1) := by rw [pow_succ']
        · exact (not_dvd_choose_add_mul hp A x.1 x.2 hxp).mpr ⟨Nat.le_of_lt_succ hx1, hx3⟩
      · intro m _
        exact Nat.mod_add_div m p
      · intro x hx
        simp only [mem_coe, mem_product, mem_range] at hx
        have hxp : x.1 < p := lt_of_le_of_lt (Nat.le_of_lt_succ hx.1) (Nat.mod_lt _ hp.pos)
        refine Prod.ext ?_ ?_
        · show (x.1 + p * x.2) % p = x.1
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxp]
        · show (x.1 + p * x.2) / p = x.2
          rw [Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hxp, zero_add]
    rw [key, card_product, card_range, ih (A / p) hA', digitProd_succ]

end CFSG.GH74.GLS.Stage4.Rest
