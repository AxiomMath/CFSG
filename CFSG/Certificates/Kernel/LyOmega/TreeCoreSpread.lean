module

public import Certificates.Data.Kernel.LyOmega.Tree
import CFSG.Certificates.Kernel.Spor.PackFld
import all CFSG.Certificates.Kernel.Spor.OrdSound
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

public section

namespace CFSG.KS.LyOm.TreeCore

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop CFSG.KS.PackFld

private theorem bAndT {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

private theorem strictN_eqT (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

private theorem picks {MS : List ℕ} : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun i ih => bAnd(Nat.beq (pickL MS i) (spMask i), ih)) n = true →
    ∀ i < n, pickL MS i = spMask i
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨hb, hr⟩ := bAndT h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact picks n hr i hi
    · exact Nat.eq_of_beq_eq_true hb

private noncomputable def accA (MS : List ℕ) (x n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) x
    (fun i acc => strictN acc (fun a => sp1 a (pickL MS i)
      (Nat.mul (nat_lit 9) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 15) i))))) n

private theorem accA_succ {MS : List ℕ} (hMS : ∀ i < 16, pickL MS i = spMask i) (x : ℕ) {i : ℕ}
    (hi : i < 16) :
    accA MS x (i + 1) = (accA MS x i ^^^ (accA MS x i &&& spMask i)) |||
      ((accA MS x i &&& spMask i) <<< (9 * 2 ^ (15 - i))) := by
  show strictN (accA MS x i) (fun a => sp1 a (pickL MS i)
      (Nat.mul (nat_lit 9) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 15) i)))) = _
  rw [strictN_eqT, hMS i hi]
  unfold sp1
  rw [strictN_eqT]
  show (accA MS x i ^^^ (accA MS x i &&& spMask i)) |||
      ((accA MS x i &&& spMask i) <<< (9 * (1 <<< (15 - i)))) = _
  rw [Nat.one_shiftLeft]

private def pos (i e : ℕ) : ℕ := 3 * e + 9 * (e - e % 2 ^ (16 - i))

private theorem two_pow_sixteen_sub {i : ℕ} (hi : i < 16) :
    2 ^ (16 - i) = 2 * 2 ^ (15 - i) := by
  rw [show 16 - i = (15 - i) + 1 by omega, Nat.pow_succ, Nat.mul_comm]

private theorem pos_succ {i : ℕ} (hi : i < 16) (e : ℕ) :
    pos (i + 1) e = pos i e +
      if 2 ^ (15 - i) ≤ e % 2 ^ (16 - i) then 9 * 2 ^ (15 - i) else 0 := by
  unfold pos
  rw [show 16 - (i + 1) = 15 - i by omega, two_pow_sixteen_sub hi]
  have hT : 0 < 2 ^ (15 - i) := Nat.two_pow_pos _
  generalize 2 ^ (15 - i) = T at hT ⊢
  have hmod : e % T = e % (2 * T) % T := (Nat.mod_mod_of_dvd e (Dvd.intro_left 2 rfl)).symm
  have hl : e % (2 * T) < 2 * T := Nat.mod_lt _ (by omega)
  have hle : e % (2 * T) ≤ e := Nat.mod_le _ _
  rw [hmod]
  generalize e % (2 * T) = l at hl hle ⊢
  split_ifs with hc
  · have : l % T = l - T := by
      rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]
    rw [this]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

private theorem mask_fld {i : ℕ} (hi : i < 16) :
    Fld (12 * 2 ^ (16 - i)) (spMask i) (fun j => if j < 2 ^ i then
      (2 ^ (3 * 2 ^ (15 - i)) - 1) <<< (3 * 2 ^ (15 - i)) else 0) := by
  have e1 : spMask i = ((1 <<< (3 * (1 <<< (15 - i)))) - 1) <<< (3 * (1 <<< (15 - i))) *
      rep1 (12 * (1 <<< (15 - i + 1))) (1 <<< (15 - (15 - i))) := rfl
  rw [e1]
  simp only [Nat.one_shiftLeft]
  rw [show 15 - (15 - i) = i by omega, show 15 - i + 1 = 16 - i by omega,
    CFSG.KS.Ord.rep1_eq (Or.inl (by positivity)), Finset.mul_sum]
  have ha : (2 ^ (3 * 2 ^ (15 - i)) - 1) <<< (3 * 2 ^ (15 - i)) < 2 ^ (12 * 2 ^ (16 - i)) := by
    rw [Nat.shiftLeft_eq]
    have h1 : (2 ^ (3 * 2 ^ (15 - i)) - 1) * 2 ^ (3 * 2 ^ (15 - i)) <
        2 ^ (3 * 2 ^ (15 - i)) * 2 ^ (3 * 2 ^ (15 - i)) :=
      Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos) (Nat.two_pow_pos _)
    rw [← Nat.pow_add] at h1
    refine lt_of_lt_of_le h1 (Nat.pow_le_pow_right Nat.two_pos ?_)
    rw [two_pow_sixteen_sub hi]
    omega
  have := CFSG.KS.Ord.fld_pk (w := 12 * 2 ^ (16 - i)) (n := 2 ^ i)
    (g := fun _ => (2 ^ (3 * 2 ^ (15 - i)) - 1) <<< (3 * 2 ^ (15 - i))) (fun _ _ => ha)
  unfold CFSG.KS.Ord.pk at this
  exact this

private theorem mask_bit {i e k : ℕ} (hi : i < 16) (he : e < 65536) (hk : k < 3) :
    (spMask i).testBit (pos i e + k) = decide (2 ^ (15 - i) ≤ e % 2 ^ (16 - i)) := by
  have hF := mask_fld hi
  have hh : e / 2 ^ (16 - i) < 2 ^ i := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show i + (16 - i) = 16 by omega]
    exact he
  have hd := Nat.div_add_mod e (2 ^ (16 - i))
  have hl := Nat.mod_lt e (Nat.two_pow_pos (16 - i))
  have hq : pos i e + k =
      12 * 2 ^ (16 - i) * (e / 2 ^ (16 - i)) + (3 * (e % 2 ^ (16 - i)) + k) := by
    unfold pos
    rw [Nat.mul_assoc]
    generalize 2 ^ (16 - i) * (e / 2 ^ (16 - i)) = u at hd ⊢
    generalize e % 2 ^ (16 - i) = l at hd ⊢
    omega
  have hj : 3 * (e % 2 ^ (16 - i)) + k < 12 * 2 ^ (16 - i) := by omega
  rw [hq, hF _ _ hj]
  beta_reduce
  rw [if_pos hh, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  generalize e % 2 ^ (16 - i) = l at hl ⊢
  rw [two_pow_sixteen_sub hi] at hl
  generalize 2 ^ (15 - i) = T at hl ⊢
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

private theorem step_iff {A m s : ℕ} {p p' : ℕ → ℕ} {c : ℕ → Prop} [DecidablePred c]
    {X : ℕ → ℕ → Prop}
    (IH : ∀ q, A.testBit q = true ↔ ∃ e < 65536, ∃ k < 3, q = p e + k ∧ X e k)
    (hm : ∀ e < 65536, ∀ k < 3, m.testBit (p e + k) = decide (c e))
    (hp : ∀ e, p' e = p e + if c e then s else 0) (q : ℕ) :
    ((A ^^^ (A &&& m)) ||| ((A &&& m) <<< s)).testBit q = true ↔
      ∃ e < 65536, ∃ k < 3, q = p' e + k ∧ X e k := by
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft,
    Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · have hA : A.testBit q = true := by
        cases hA : A.testBit q <;> simp_all
      have hM : m.testBit q = false := by
        cases hM : m.testBit q <;> simp_all
      obtain ⟨e, he, k, hk, hq, hX⟩ := (IH q).1 hA
      rw [hq, hm e he k hk] at hM
      have hc : ¬ c e := by simpa using hM
      exact ⟨e, he, k, hk, by rw [hp, if_neg hc, Nat.add_zero]; exact hq, hX⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hs, h1, h2⟩ := h
      obtain ⟨e, he, k, hk, hq, hX⟩ := (IH _).1 h1
      rw [hq, hm e he k hk] at h2
      have hc : c e := by simpa using h2
      refine ⟨e, he, k, hk, ?_, hX⟩
      rw [hp, if_pos hc]
      omega
  · rintro ⟨e, he, k, hk, rfl, hX⟩
    by_cases hc : c e
    · right
      rw [hp, if_pos hc]
      have e1 : p e + s + k - s = p e + k := by omega
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by omega, ?_, ?_⟩
      · rw [e1]
        exact (IH _).2 ⟨e, he, k, hk, rfl, hX⟩
      · rw [e1, hm e he k hk]
        simpa using hc
    · left
      rw [hp, if_neg hc, Nat.add_zero, (IH _).2 ⟨e, he, k, hk, rfl, hX⟩, hm e he k hk]
      simp [hc]

private theorem bit_lt {x N q : ℕ} (hx : x < 2 ^ N) (h : x.testBit q = true) : q < N := by
  by_contra hq
  rw [Nat.testBit_lt_two_pow
    (lt_of_lt_of_le hx (Nat.pow_le_pow_right Nat.two_pos (Nat.le_of_not_lt hq)))] at h
  exact Bool.false_ne_true h

private theorem acc_bits {MS : List ℕ} (hMS : ∀ i < 16, pickL MS i = spMask i) {x : ℕ}
    (hx : x < 2 ^ 196608) : ∀ i ≤ 16, ∀ q, (accA MS x i).testBit q = true ↔
      ∃ e < 65536, ∃ k < 3, q = pos i e + k ∧ x.testBit (3 * e + k) = true := by
  intro i
  induction i with
  | zero =>
    intro _ q
    show x.testBit q = true ↔ _
    have p0 : ∀ e < 65536, pos 0 e = 3 * e := fun e he => by
      unfold pos
      rw [Nat.mod_eq_of_lt (show e < 2 ^ (16 - 0) by norm_num; omega), Nat.sub_self,
        Nat.mul_zero, Nat.add_zero]
    constructor
    · intro h
      have hq : q < 196608 := bit_lt hx h
      refine ⟨q / 3, by omega, q % 3, Nat.mod_lt _ (by norm_num), ?_, ?_⟩
      · rw [p0 _ (by omega)]
        omega
      · rw [show 3 * (q / 3) + q % 3 = q by omega]
        exact h
    · rintro ⟨e, he, k, hk, rfl, h⟩
      rw [p0 e he]
      exact h
  | succ i ih =>
    intro hi q
    rw [accA_succ hMS x (by omega : i < 16)]
    exact step_iff (c := fun e => 2 ^ (15 - i) ≤ e % 2 ^ (16 - i)) (ih (by omega))
      (fun e he k hk => mask_bit (by omega) he hk) (pos_succ (by omega)) q

theorem spreadB_eq {MS : List ℕ} (hMS : spMasksOK MS = true) {x : ℕ} (hx : x < 2 ^ 196608) :
    spreadB MS x = ∑ e ∈ Finset.range 65536, x / 2 ^ (3 * e) % 8 * 2 ^ (12 * e) := by
  obtain ⟨-, hrec⟩ := bAndT hMS
  have hP := picks 16 hrec
  have hS : spreadB MS x = accA MS x 16 := rfl
  have hA := acc_bits hP hx 16 le_rfl
  have hR : Fld 12 (∑ e ∈ Finset.range 65536, x / 2 ^ (3 * e) % 8 * 2 ^ (12 * e))
      (fun t => if t < 65536 then x / 2 ^ (3 * t) % 8 else 0) := by
    have := CFSG.KS.Ord.fld_pk (w := 12) (n := 65536) (g := fun t => x / 2 ^ (3 * t) % 8)
      (fun t _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
    unfold CFSG.KS.Ord.pk at this
    exact this
  rw [hS]
  apply Nat.eq_of_testBit_eq
  intro q
  obtain ⟨E, K, hK, rfl⟩ : ∃ E K, K < 12 ∧ q = 12 * E + K :=
    ⟨q / 12, q % 12, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod q 12).symm⟩
  rw [hR E K hK, Bool.eq_iff_iff, hA]
  have p16 : ∀ e, pos 16 e = 12 * e := fun e => by
    unfold pos
    simp only [Nat.sub_self, pow_zero, Nat.mod_one, Nat.sub_zero]
    omega
  simp only [p16]
  split_ifs with hE
  · rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    constructor
    · rintro ⟨e, he, k, hk, h, hX⟩
      obtain ⟨rfl, rfl⟩ : e = E ∧ k = K := by omega
      rw [Nat.add_comm, hX]
      simp [hk]
    · intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨E, hE, K, h.1, rfl, by rw [Nat.add_comm]; exact h.2⟩
  · simp only [Nat.zero_testBit, Bool.false_eq_true, iff_false]
    rintro ⟨e, he, k, hk, h, -⟩
    omega

end CFSG.KS.LyOm.TreeCore

end
