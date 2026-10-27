module

public import Certificates.Data.Kernel.LyOmega.Tree
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

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop
open CFSG.KS.Ord CFSG.KS.PackFld

private theorem tcm_idx {r h i j : ℕ} (hi : i < h) (hj : j < r) : r * i + j < r * h := by
  have := Nat.mul_le_mul_left r (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  omega

private theorem tcm_col {w r h k : ℕ} {a : ℕ → ℕ} (hw : 0 < w) (ha : ∀ t < r * h, a t < 2 ^ w)
    (hk : k < r) :
    (pk w (r * h) a >>> (w * k)) &&& pk w (r * h) (fun t => if t % r = 0 then 2 ^ w - 1 else 0) =
      ∑ i ∈ Finset.range h, a (r * i + k) * 2 ^ (w * (r * i)) := by
  have hpos := Nat.two_pow_pos w
  have hr : 0 < r := by omega
  have hm : ∀ t < r * h, (if t % r = 0 then 2 ^ w - 1 else 0) < 2 ^ w :=
    fun t _ => by split <;> omega
  have hlt : ∀ t < r * h, t % r = 0 → t + k < r * h := by
    intro t ht h0
    have h1 := Nat.div_add_mod t r
    have h2 : t / r < h := (Nat.div_lt_iff_lt_mul hr).2 (by rw [Nat.mul_comm]; exact ht)
    have := tcm_idx h2 hk
    rw [h0] at h1
    omega
  have hF : Fld w ((pk w (r * h) a >>> (w * k)) &&&
      pk w (r * h) (fun t => if t % r = 0 then 2 ^ w - 1 else 0))
      (fun t => if t < r * h then (if t % r = 0 then a (t + k) else 0) else 0) := by
    refine fld_congr (fld_and (fld_shr k (fld_pk ha)) (fld_pk hm)) fun t => ?_
    by_cases ht : t < r * h
    · by_cases h0 : t % r = 0
      · have h3 := hlt t ht h0
        simp only [ht, h0, h3, ↓reduceIte]
        rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (ha _ h3)]
      · simp [ht, h0]
    · simp [ht]
  have hb : ∀ t < r * h, (if t % r = 0 then a (t + k) else 0) < 2 ^ w := by
    intro t ht
    by_cases h0 : t % r = 0
    · rw [ite_eq_left h0]
      exact ha _ (hlt t ht h0)
    · rw [ite_eq_right h0]
      exact hpos
  rw [pk_of_fld hw hF hb, pk_rows]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single 0]
  · have e2 : (r * i + 0) % r = 0 := by simp
    rw [e2, ite_eq_left rfl, Nat.add_zero]
  · intro j hj hj0
    rw [(dm_eq (i := i) (Finset.mem_range.1 hj)).2, ite_eq_right hj0, Nat.zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.2 hr) h0

private theorem tcm_row {w r m k : ℕ} {b : ℕ → ℕ} (hw : 0 < w) (hb : ∀ t < r * m, b t < 2 ^ w)
    (hk : k < m) :
    (pk w (r * m) b >>> (w * r * k)) &&& (2 ^ (w * r) - 1) = pk w r (fun j => b (r * k + j)) := by
  rw [Nat.mul_assoc]
  refine pk_of_fld hw (fld_congr (fld_and (fld_shr (r * k) (fld_pk hb)) (fld_RM w r)) fun t => ?_)
    fun t ht => hb _ (tcm_idx hk ht)
  by_cases ht : t < r
  · have h3 : t + r * k < r * m := by have := tcm_idx hk ht; omega
    simp only [ht, h3, ↓reduceIte]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hb _ h3), Nat.add_comm]
  · simp [ht]

private theorem tcm_sum {w r h m d : ℕ} {a b : ℕ → ℕ} (hw : 0 < w)
    (ha : ∀ t < r * h, a t < 2 ^ w) (hb : ∀ t < r * m, b t < 2 ^ w) (hdr : d ≤ r) (hdm : d ≤ m) :
    ∑ k ∈ Finset.range d, ((pk w (r * h) a >>> (w * k)) &&&
        pk w (r * h) (fun t => if t % r = 0 then 2 ^ w - 1 else 0)) *
      ((pk w (r * m) b >>> (w * r * k)) &&& (2 ^ (w * r) - 1)) =
    pk w (r * h) (fun t => ∑ k ∈ Finset.range d, a (r * (t / r) + k) * b (r * k + t % r)) := by
  calc _ = ∑ k ∈ Finset.range d, ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range r,
        a (r * i + k) * b (r * k + j) * 2 ^ (w * (r * i + j)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        rw [tcm_col hw ha (by omega), tcm_row hw hb (by omega), Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold pk
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.mul_add w, Nat.pow_add]
        ring
    _ = ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range r, ∑ k ∈ Finset.range d,
        a (r * i + k) * b (r * k + j) * 2 ^ (w * (r * i + j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        rw [pk_rows]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨e1, e2⟩ := dm_eq (i := i) (Finset.mem_range.1 hj)
        beta_reduce
        rw [e1, e2, Finset.sum_mul]

private theorem tcm_core {w r h m d S CM RM : ℕ} {a b : ℕ → ℕ} (hw : 0 < w) (hS : S = w * r)
    (hRM : RM = 2 ^ S - 1) (hCM : CM = pk w (r * h) (fun t => if t % r = 0 then 2 ^ w - 1 else 0))
    (ha : ∀ t < r * h, a t < 2 ^ w) (hb : ∀ t < r * m, b t < 2 ^ w) (hdr : d ≤ r) (hdm : d ≤ m) :
    ∑ k ∈ Finset.range d, ((pk w (r * h) a >>> (w * k)) &&& CM) *
      ((pk w (r * m) b >>> (S * k)) &&& RM) =
    pk w (r * h) (fun t => ∑ k ∈ Finset.range d, a (r * (t / r) + k) * b (r * k + t % r)) := by
  subst hS hRM hCM
  exact tcm_sum hw ha hb hdr hdm

private theorem tcm_rec_add (a : ℕ) (f : ℕ → ℕ) : ∀ n : ℕ,
    Nat.rec (motive := fun _ => ℕ) a (fun i acc => Nat.add acc (f i)) n =
      a + ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, ← Nat.add_assoc, ← tcm_rec_add a f n]
    rfl

private theorem tcm_rowsMulU (w S g q CM RM X B : ℕ) : rowsMulU w S g q CM RM X B =
    ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range g,
      ((X >>> (w * (g * j + i))) &&& CM) * ((rowsOf S (g * j) g B >>> (S * i)) &&& RM) := by
  unfold rowsMulU
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [Nat.rec_add_one, strictN_eqO]
    rw [tcm_rec_add]
    rfl

private theorem tcm_rowsOf {S g j i B : ℕ} (hi : i < g) :
    (rowsOf S (g * j) g B >>> (S * i)) &&& (2 ^ S - 1) =
      (B >>> (S * (g * j + i))) &&& (2 ^ S - 1) := by
  apply Nat.eq_of_testBit_eq
  intro b
  unfold rowsOf
  change ((((B >>> (S * (g * j))) &&& ((1 <<< (S * g)) - 1)) >>> (S * i)) &&&
    (2 ^ S - 1)).testBit b = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hb : b < S
  · have h1 : S * i + b < S * g := tcm_idx hi hb
    have h2 : S * (g * j) + (S * i + b) = S * (g * j + i) + b := by ring
    simp [hb, h1, h2]
  · simp [hb]

private theorem tcm_sum_rows (g : ℕ) (F : ℕ → ℕ) : ∀ q,
    ∑ t ∈ Finset.range (g * q), F t = ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range g, F (g * j + i)
  | 0 => by simp
  | q + 1 => by
    rw [Finset.sum_range_succ, ← tcm_sum_rows g F q, Nat.mul_succ, Finset.sum_range_add]

private theorem tcm_grp {w S g q CM RM X B : ℕ} (hRM : RM = 2 ^ S - 1) :
    rowsMulU w S g q CM RM X B =
      ∑ k ∈ Finset.range (g * q), ((X >>> (w * k)) &&& CM) * ((B >>> (S * k)) &&& RM) := by
  subst hRM
  rw [tcm_rowsMulU, tcm_sum_rows]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
  rw [tcm_rowsOf (Finset.mem_range.1 hi)]

private theorem tcm_L {w n : ℕ} (hw : 0 < w) : rep1 w n = pk w n (fun _ => 1) := by
  rw [rep1_eq (Or.inl hw)]
  unfold pk
  simp only [one_mul]

private theorem tcm_H {w n s : ℕ} :
    Nat.shiftLeft (pk w n (fun _ => 1)) s = pk w n (fun _ => 2 ^ s) := by
  change pk w n (fun _ => 1) <<< s = _
  rw [Nat.shiftLeft_eq, pk_mul]
  exact pk_congr fun _ _ => Nat.one_mul _

private theorem tcm_CM {w r h : ℕ} (hw : 0 < w) (hr : 0 < r) :
    (2 ^ w - 1) * rep1 (r * w) h = pk w (r * h) (fun t => if t % r = 0 then 2 ^ w - 1 else 0) := by
  rw [rep1_eq (Or.inl (Nat.mul_pos hr hw)), pk_rows, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single 0]
  · have e : r * w * i = w * (r * i + 0) := by ring
    have e2 : (r * i + 0) % r = 0 := by simp
    rw [e, e2, ite_eq_left rfl]
  · intro j hj hj0
    rw [(dm_eq (i := i) (Finset.mem_range.1 hj)).2, ite_eq_right hj0, Nat.zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.2 hr) h0

private theorem tcm_facts {C : Consts} (hC : constsOK C = true) :
    C.Lh = pk 12 (111 * 448) (fun _ => 1) ∧ C.Hh = pk 12 (111 * 448) (fun _ => 2 ^ (12 - 1)) ∧
    C.CMh = pk 12 (111 * 448) (fun t => if t % 111 = 0 then 2 ^ 12 - 1 else 0) ∧
    C.L7 = pk 12 (111 * 7) (fun _ => 1) ∧ C.H7 = pk 12 (111 * 7) (fun _ => 2 ^ (12 - 1)) ∧
    C.CM7 = pk 12 (111 * 7) (fun t => if t % 111 = 0 then 2 ^ 12 - 1 else 0) := by
  unfold CFSG.KC.LyOm.constsOK at hC
  obtain ⟨h1, hC⟩ := rawAnd_true hC
  obtain ⟨h2, hC⟩ := rawAnd_true hC
  obtain ⟨h3, hC⟩ := rawAnd_true hC
  obtain ⟨h4, hC⟩ := rawAnd_true hC
  obtain ⟨h5, hC⟩ := rawAnd_true hC
  obtain ⟨h6, -⟩ := rawAnd_true hC
  have e1 : C.Lh = pk 12 (111 * 448) (fun _ => 1) :=
    (Nat.eq_of_beq_eq_true h1).trans (tcm_L (w := 12) (n := 111 * 448) (by norm_num))
  have e4 : C.L7 = pk 12 (111 * 7) (fun _ => 1) :=
    (Nat.eq_of_beq_eq_true h4).trans (tcm_L (w := 12) (n := 111 * 7) (by norm_num))
  refine ⟨e1, ?_, ?_, e4, ?_, ?_⟩
  · rw [Nat.eq_of_beq_eq_true h2, e1]
    exact tcm_H
  · exact (Nat.eq_of_beq_eq_true h3).trans (tcm_CM (w := 12) (r := 111) (h := 448) (by norm_num)
      (by norm_num))
  · rw [Nat.eq_of_beq_eq_true h5, e4]
    exact tcm_H
  · exact (Nat.eq_of_beq_eq_true h6).trans (tcm_CM (w := 12) (r := 111) (h := 7) (by norm_num)
      (by norm_num))

private theorem tcm_bound {d : ℕ} {u v : ℕ → ℕ} (hu : ∀ k < d, u k < 5) (hv : ∀ k < d, v k < 5) :
    ∑ k ∈ Finset.range d, u k * v k ≤ 16 * d := by
  calc _ ≤ ∑ _k ∈ Finset.range d, 16 := Finset.sum_le_sum fun k hk => by
          have h1 := hu k (Finset.mem_range.1 hk)
          have h2 := hv k (Finset.mem_range.1 hk)
          have h3 : u k * v k ≤ 4 * 4 := Nat.mul_le_mul (by omega) (by omega)
          omega
    _ = 16 * d := by simp [Nat.mul_comm]

private theorem tcm_red {h m d : ℕ} {a b : ℕ → ℕ} (ha : ∀ t < 111 * h, a t < 5)
    (hb : ∀ t < 111 * m, b t < 5) (hdr : d ≤ 111) (hdm : d ≤ m) :
    redP 12 (pk 12 (111 * h) (fun _ => 1)) (pk 12 (111 * h) (fun _ => 2 ^ (12 - 1))) 5 8
        (pk 12 (111 * h) (fun t => ∑ k ∈ Finset.range d, a (111 * (t / 111) + k) *
          b (111 * k + t % 111))) =
      pk 12 (111 * h) (fun t => (∑ k ∈ Finset.range d, a (111 * (t / 111) + k) *
          b (111 * k + t % 111)) % 5) := by
  have hbd : ∀ t < 111 * h, ∑ k ∈ Finset.range d, a (111 * (t / 111) + k) *
      b (111 * k + t % 111) ≤ 16 * 111 := by
    intro t ht
    have h2 : t / 111 < h := (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by rw [Nat.mul_comm]; exact ht)
    have hl : t % 111 < 111 := Nat.mod_lt _ (by norm_num)
    refine le_trans (tcm_bound (fun k hk => ha _ (tcm_idx h2 (by omega)))
      (fun k hk => hb _ (tcm_idx (by omega) hl))) (by omega)
  refine redP_pk (by norm_num) (by norm_num) (fun t ht => ?_) (fun t ht => ?_)
  · have := hbd t ht
    norm_num
    omega
  · have := hbd t ht
    norm_num
    omega

private theorem tcm_RM (n : ℕ) :
    Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1) = 2 ^ n - 1 := by
  show 1 <<< n - 1 = 2 ^ n - 1
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem mulH_eq {C : Consts} (hC : constsOK C = true) {x g : ℕ → ℕ}
    (hx : ∀ t < 49728, x t < 5) (hg : ∀ t < 12321, g t < 5) :
    mulH C (∑ t ∈ Finset.range 49728, x t * 2 ^ (12 * t))
        (∑ t ∈ Finset.range 12321, g t * 2 ^ (12 * t)) =
      ∑ t ∈ Finset.range 49728,
        (∑ k ∈ Finset.range 111, x (111 * (t / 111) + k) * g (111 * k + t % 111)) % 5 *
          2 ^ (12 * t) := by
  obtain ⟨hLh, hHh, hCMh, -, -, -⟩ := tcm_facts hC
  change mulH C (pk 12 (111 * 448) x) (pk 12 (111 * 111) g) =
    pk 12 (111 * 448) (fun t => (∑ k ∈ Finset.range 111, x (111 * (t / 111) + k) *
      g (111 * k + t % 111)) % 5)
  unfold mulH rowsMulR
  rw [tcm_RM, hLh, hHh, tcm_grp rfl,
    tcm_core (S := 1332) (by norm_num) (by norm_num) rfl hCMh
      (fun t ht => by have := hx t ht; omega) (fun t ht => by have := hg t ht; omega)
      (by norm_num) (by norm_num)]
  exact tcm_red (h := 448) (m := 111) hx hg (by norm_num) (by norm_num)

theorem mul7_eq {C : Consts} (hC : constsOK C = true) {y m : ℕ → ℕ}
    (hy : ∀ t < 777, y t < 5) (hm : ∀ t < 777, m t < 5) :
    mul7 C (∑ t ∈ Finset.range 777, y t * 2 ^ (12 * t)) (∑ t ∈ Finset.range 777, m t * 2 ^ (12 * t)) =
      ∑ t ∈ Finset.range 777,
        (∑ k ∈ Finset.range 7, y (111 * (t / 111) + k) * m (111 * k + t % 111)) % 5 *
          2 ^ (12 * t) := by
  obtain ⟨-, -, -, hL7, hH7, hCM7⟩ := tcm_facts hC
  change mul7 C (pk 12 (111 * 7) y) (pk 12 (111 * 7) m) =
    pk 12 (111 * 7) (fun t => (∑ k ∈ Finset.range 7, y (111 * (t / 111) + k) *
      m (111 * k + t % 111)) % 5)
  unfold mul7 mulR
  rw [tcm_RM, hL7, hH7, mulU_eq,
    tcm_core (S := 1332) (by norm_num) (by norm_num) rfl hCM7 (fun t ht => by have := hy t ht; omega)
      (fun t ht => by have := hm t ht; omega) (by norm_num) le_rfl]
  exact tcm_red (h := 7) (m := 7) hy hm (by norm_num) le_rfl

end CFSG.KS.LyOm.TreeCore

end
