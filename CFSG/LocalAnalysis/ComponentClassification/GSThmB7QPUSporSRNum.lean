module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.GSThmB.QPUSpor

@[expose] def psp4Num (q : ℕ) : ℕ := q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1)

@[expose] def sporFactors : TauCeti.SporadicName → List (ℕ × ℕ)
  | .M11 => [(2, 4), (3, 2), (5, 1), (11, 1)]
  | .M12 => [(2, 6), (3, 3), (5, 1), (11, 1)]
  | .M22 => [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1)]
  | .M23 => [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (23, 1)]
  | .M24 => [(2, 10), (3, 3), (5, 1), (7, 1), (11, 1), (23, 1)]
  | .J1 => [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (19, 1)]
  | .J2 => [(2, 7), (3, 3), (5, 2), (7, 1)]
  | .J3 => [(2, 7), (3, 5), (5, 1), (17, 1), (19, 1)]
  | .J4 => [(2, 21), (3, 3), (5, 1), (7, 1), (11, 3), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1)]
  | .HS => [(2, 9), (3, 2), (5, 3), (7, 1), (11, 1)]
  | .McL => [(2, 7), (3, 6), (5, 3), (7, 1), (11, 1)]
  | .He => [(2, 10), (3, 3), (5, 2), (7, 3), (17, 1)]
  | .Ru => [(2, 14), (3, 3), (5, 3), (7, 1), (13, 1), (29, 1)]
  | .Suz => [(2, 13), (3, 7), (5, 2), (7, 1), (11, 1), (13, 1)]
  | .ONan => [(2, 9), (3, 4), (5, 1), (7, 3), (11, 1), (19, 1), (31, 1)]
  | .Co1 => [(2, 21), (3, 9), (5, 4), (7, 2), (11, 1), (13, 1), (23, 1)]
  | .Co2 => [(2, 18), (3, 6), (5, 3), (7, 1), (11, 1), (23, 1)]
  | .Co3 => [(2, 10), (3, 7), (5, 3), (7, 1), (11, 1), (23, 1)]
  | .Fi22 => [(2, 17), (3, 9), (5, 2), (7, 1), (11, 1), (13, 1)]
  | .Fi23 => [(2, 18), (3, 13), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (23, 1)]
  | .Fi24Prime => [(2, 21), (3, 16), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1)]
  | .HN => [(2, 14), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)]
  | .Ly => [(2, 8), (3, 7), (5, 6), (7, 1), (11, 1), (31, 1), (37, 1), (67, 1)]
  | .Th => [(2, 15), (3, 10), (5, 3), (7, 2), (13, 1), (19, 1), (31, 1)]
  | .B => [(2, 41), (3, 13), (5, 6), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1),
      (47, 1)]
  | .M => [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3), (17, 1), (19, 1), (23, 1), (29, 1),
      (31, 1), (41, 1), (47, 1), (59, 1), (71, 1)]

@[expose] def sporOrder (s : TauCeti.SporadicName) : ℕ :=
  ((sporFactors s).map fun x => x.1 ^ x.2).prod

@[expose] def psp4Allowed : TauCeti.SporadicName → ℕ → Bool
  | .Co1, q => q == 5
  | .B, q => q == 5
  | .M, q => q == 5 || q == 7 || q == 9
  | _, _ => false

@[expose] def psp4Check (s : TauCeti.SporadicName) : Bool :=
  (sporFactors s).all fun x => (List.range (x.2 / 4 + 1)).all fun f =>
    f == 0 || x.1 == 2 || decide (x.1 ^ f < 5) || 2 * sporOrder s % psp4Num (x.1 ^ f) != 0 ||
      psp4Allowed s (x.1 ^ f)

theorem psp4Check_eq_true (s : TauCeti.SporadicName) : psp4Check s = true := by
  cases s <;> decide

theorem sporFactors_prime (s : TauCeti.SporadicName) : ∀ x ∈ sporFactors s, x.1.Prime := by
  cases s <;> simp only [sporFactors, List.forall_mem_cons] <;> norm_num

theorem sporFactors_nodup (s : TauCeti.SporadicName) : ((sporFactors s).map Prod.fst).Nodup := by
  cases s <;> decide

theorem exists_eq_of_prime_dvd_prod {p : ℕ} (hp : p.Prime) :
    ∀ {l : List (ℕ × ℕ)}, (∀ x ∈ l, x.1.Prime) → p ∣ (l.map fun x => x.1 ^ x.2).prod →
      ∃ x ∈ l, p = x.1
  | [], _, h => by
    rw [List.map_nil, List.prod_nil, Nat.dvd_one] at h
    exact absurd h hp.one_lt.ne'
  | x :: l, hl, h => by
    rw [List.map_cons, List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact ⟨x, by simp, (Nat.prime_dvd_prime_iff_eq hp (hl x (by simp))).1
        (hp.dvd_of_dvd_pow h1)⟩
    · obtain ⟨y, hy, hpy⟩ := exists_eq_of_prime_dvd_prod hp
        (fun y hy => hl y (List.mem_cons_of_mem _ hy)) h1
      exact ⟨y, List.mem_cons_of_mem _ hy, hpy⟩

theorem exists_of_prime_pow_dvd_prod {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    ∀ {l : List (ℕ × ℕ)}, (∀ x ∈ l, x.1.Prime) → (l.map Prod.fst).Nodup →
      p ^ k ∣ (l.map fun x => x.1 ^ x.2).prod → ∃ x ∈ l, p = x.1 ∧ k ≤ x.2
  | [], _, _, h => by
    rw [List.map_nil, List.prod_nil, Nat.dvd_one] at h
    exact absurd h (Nat.one_lt_pow (by omega) hp.one_lt).ne'
  | x :: l, hl, hnd, h => by
    rw [List.map_cons, List.prod_cons] at h
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hpx : p = x.1
    · subst hpx
      have hnot : ¬ x.1 ∣ (l.map fun y => y.1 ^ y.2).prod := by
        intro hd
        obtain ⟨y, hy, hxy⟩ := exists_eq_of_prime_dvd_prod hp
          (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hd
        exact hnd.1 (hxy ▸ List.mem_map_of_mem hy)
      have hcop : Nat.Coprime (x.1 ^ k) (l.map fun y => y.1 ^ y.2).prod :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hnot)
      exact ⟨x, by simp, rfl,
        (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 (hcop.dvd_of_dvd_mul_right h)⟩
    · have hcop : Nat.Coprime (p ^ k) (x.1 ^ x.2) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes hp (hl x (by simp))).2 hpx)
      obtain ⟨y, hy, h1, h2⟩ := exists_of_prime_pow_dvd_prod hp hk
        (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hnd.2 (hcop.dvd_of_dvd_mul_left h)
      exact ⟨y, List.mem_cons_of_mem _ hy, h1, h2⟩

theorem psp4_allowed (s : TauCeti.SporadicName) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (h : psp4Num (p ^ f) ∣ 2 * sporOrder s) :
    psp4Allowed s (p ^ f) = true := by
  have h4 : p ^ (4 * f) ∣ sporOrder s := by
    have h1 : p ^ (4 * f) ∣ 2 * sporOrder s := by
      refine (Dvd.intro (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) ?_).trans h
      rw [psp4Num, mul_comm 4 f, pow_mul, mul_assoc]
    have hcop : Nat.Coprime (p ^ (4 * f)) 2 :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    exact hcop.dvd_of_dvd_mul_left h1
  obtain ⟨x, hx, rfl, hk⟩ := exists_of_prime_pow_dvd_prod hp (by omega) (sporFactors_prime s)
    (sporFactors_nodup s) h4
  have hc := psp4Check_eq_true s
  rw [psp4Check, List.all_eq_true] at hc
  have hc2 := hc x hx
  rw [List.all_eq_true] at hc2
  have hc3 := hc2 f (List.mem_range.2 (by omega))
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc3
  obtain (((h0 | h2) | h5') | hmod) | hA := hc3
  · omega
  · exact absurd h2 hp2
  · omega
  · exact absurd (Nat.mod_eq_zero_of_dvd h) hmod
  · exact hA

end CFSG.ComponentClassification.GSThmB.QPUSpor
