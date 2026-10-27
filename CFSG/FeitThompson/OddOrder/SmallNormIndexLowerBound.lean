module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import CFSG.FeitThompson.OddOrder.GeometricSumCongruences

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

variable {p q u h x : ℕ}

theorem natModEq_one_of_mul_modEq_one (hu : u ≡ 1 [MOD q]) (hux : u * x ≡ 1 [MOD q]) :
    x ≡ 1 [MOD q] :=
  calc x = 1 * x := (one_mul x).symm
    _ ≡ u * x [MOD q] := (hu.mul_right x).symm
    _ ≡ 1 [MOD q] := hux

theorem geomSum_index_modEq (hq : 0 < q) (hqu : q * u = ∑ i ∈ range q, p ^ i)
    (hh : h = u * x) (hhp : h ≡ 1 [MOD p]) : x ≡ q [MOD p] :=
  calc x = 1 * x := (one_mul x).symm
    _ ≡ (∑ i ∈ range q, p ^ i) * x [MOD p] := ((sum_range_pow_modEq_one hq).mul_right x).symm
    _ = q * h := by rw [← hqu, hh]; ring
    _ ≡ q * 1 [MOD p] := hhp.mul_left q
    _ = q := mul_one q

theorem geomSum_pos (hq : 0 < q) : 0 < ∑ i ∈ range q, p ^ i :=
  Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, Finset.mem_range.2 hq, by simp⟩

theorem geomSum_index_lower_bound (hpodd : Odd p) (hqodd : Odd q) (hq1 : 1 < q) (hqp : q < p)
    (hpq : p ≡ 1 [MOD q]) (hxodd : Odd x) (hqu : q * u = ∑ i ∈ range q, p ^ i)
    (hh : h = u * x) (hhp : h ≡ 1 [MOD p]) (hhq : h ≡ 1 [MOD q]) (huq : u ≡ 1 [MOD q]) :
    q + (q + 1) * p ≤ x := by
  have hxq : x ≡ q [MOD p] := geomSum_index_modEq (by omega) hqu hh hhp
  have hx1 : x ≡ 1 [MOD q] := natModEq_one_of_mul_modEq_one huq (hh ▸ hhq)
  have hmod : x % p = q := by
    have h0 := hxq
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hqp] at h0
  obtain ⟨n, hxn⟩ : ∃ n, x = q + n * p := by
    refine ⟨x / p, ?_⟩
    have h1 := Nat.div_add_mod x p
    rw [hmod, Nat.mul_comm p] at h1
    omega
  have hnq : n ≡ 1 [MOD q] :=
    calc n = 0 + n * 1 := by ring
      _ ≡ q + n * p [MOD q] :=
          (Nat.ModEq.add (Nat.modEq_zero_iff_dvd.2 dvd_rfl) (hpq.mul_left n)).symm
      _ = x := hxn.symm
      _ ≡ 1 [MOD q] := hx1
  have hne : Even n := by
    have h3 : Even (x - q) := Nat.Odd.sub_odd hxodd hqodd
    have h4 : x - q = n * p := by omega
    rw [h4, Nat.even_mul] at h3
    exact h3.resolve_right (Nat.not_even_iff_odd.2 hpodd)
  have hnge : q + 1 ≤ n := by
    have hn1 : n % q = 1 := by
      have h5 := hnq
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hq1] at h5
    by_contra hcon
    have hnle : n ≤ q := by omega
    rcases eq_or_lt_of_le hnle with rfl | hlt
    · rw [Nat.mod_self] at hn1; omega
    · rw [Nat.mod_eq_of_lt hlt] at hn1
      exact Nat.not_even_one (hn1 ▸ hne)
  calc q + (q + 1) * p ≤ q + n * p := Nat.add_le_add_left (Nat.mul_le_mul_right p hnge) q
    _ = x := hxn.symm

theorem pow_lt_of_geomSum_index_le (hp : 1 ≤ p) (hq : 0 < q)
    (hqu : q * u = ∑ i ∈ range q, p ^ i) (hh : h = u * x)
    (hxge : q + (q + 1) * p ≤ x) : p ^ q < h := by
  have hSpos : 0 < ∑ i ∈ range q, p ^ i := geomSum_pos hq
  have hu : 0 < u := Nat.pos_of_ne_zero fun hu0 => by simp [hu0] at hqu; omega
  have hSp : p ^ q ≤ (∑ i ∈ range q, p ^ i) * p := by
    have h1 := sum_range_pow_mul_sub_one (p := p) hp q
    have h2 : (∑ i ∈ range q, p ^ i) * (p - 1)
        = (∑ i ∈ range q, p ^ i) * p - (∑ i ∈ range q, p ^ i) := by
      rw [Nat.mul_sub, mul_one]
    have h3 : (∑ i ∈ range q, p ^ i) ≤ (∑ i ∈ range q, p ^ i) * p :=
      Nat.le_mul_of_pos_right _ hp
    omega
  calc p ^ q ≤ (∑ i ∈ range q, p ^ i) * p := hSp
    _ = q * u * p := by rw [hqu]
    _ < u * (q + (q + 1) * p) := by have := Nat.mul_pos hu hq; nlinarith
    _ ≤ u * x := Nat.mul_le_mul_left u hxge
    _ = h := hh.symm

theorem geomSum_lt_cofactor (hpodd : Odd p) (hqodd : Odd q) (hq1 : 1 < q) (hqp : q < p)
    (hpq : p ≡ 1 [MOD q]) (hxodd : Odd x) (hqu : q * u = ∑ i ∈ range q, p ^ i)
    (hh : h = u * x) (hhp : h ≡ 1 [MOD p]) (hhq : h ≡ 1 [MOD q]) (huq : u ≡ 1 [MOD q]) :
    p ^ q < h :=
  pow_lt_of_geomSum_index_le (by omega) (by omega) hqu hh
    (geomSum_index_lower_bound hpodd hqodd hq1 hqp hpq hxodd hqu hh hhp hhq huq)

theorem geomSum_index_lower_bound_and_lt_cofactor (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q < p) (hpq : p ≡ 1 [MOD q])
    (hxodd : Odd x) (hqu : q * u = ∑ i ∈ range q, p ^ i) (hh : h = u * x)
    (hhp : h ≡ 1 [MOD p]) (hhq : h ≡ 1 [MOD q]) (huq : u ≡ 1 [MOD q]) :
    q + (q + 1) * p ≤ x ∧ p ^ q < h := by
  have hpodd := hp.odd_of_ne_two hp2
  have hqodd := hq.odd_of_ne_two hq2
  have hq1 : 1 < q := hq.one_lt
  exact ⟨geomSum_index_lower_bound hpodd hqodd hq1 hqp hpq hxodd hqu hh hhp hhq huq,
    geomSum_lt_cofactor hpodd hqodd hq1 hqp hpq hxodd hqu hh hhp hhq huq⟩

end CFSG.FeitThompson
