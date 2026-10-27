module

public import Certificates.Data.Kernel.F2PtSet
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.Bound.Init
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.KC.F2PtSet

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem ptStrictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem ptStrictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem le_hiOf (n : Nat) : n ≤ 64 * hiOf n := by
  change n ≤ 64 * (n >>> 6 + 1)
  rw [Nat.shiftRight_eq_div_pow]
  have e : (2 : Nat) ^ 6 = 64 := rfl
  rw [e]
  omega

theorem ptRecAnd (g : Nat → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun q acc => Bool.rec (motive := fun _ => Bool) false acc (g q)) n = true →
      ∀ q < n, g q = true
  | 0, _, q, hq => absurd hq (Nat.not_lt_zero q)
  | n + 1, h, q, hq => by
    change Bool.rec (motive := fun _ => Bool) false (Nat.rec (motive := fun _ => Bool) true
      (fun q acc => Bool.rec (motive := fun _ => Bool) false acc (g q)) n) (g n) = true at h
    cases hg : g n
    · rw [hg] at h
      exact absurd h Bool.false_ne_true
    · rw [hg] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
      · exact ptRecAnd g n h q hq
      · exact hg

theorem ptAllBelow {m n : Nat} {f : Nat → Bool} (h : allBelow m (hiOf n) f = true) (hm : m ≤ n) :
    ∀ i < m, f i = true := by
  intro i him
  have hhi := le_hiOf n
  have h1 := ptRecAnd (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2
        ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l))) 64) (hiOf n) h (i / 64) (by omega)
  have h2 := ptRecAnd (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
      (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64 h1 (i % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem ptSumBelow (m n : Nat) (f : Nat → Nat) (hm : m ≤ n) :
    sumBelow m (hiOf n) f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : Nat → Nat) (k : Nat),
      Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have sel : ∀ (b : Bool) (x : Nat), Bool.rec (motive := fun _ => Nat) 0 x b =
      if b = true then x else 0 := by
    intro b x
    cases b <;> rfl
  have hgen : ∀ h, sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => Nat) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => Nat) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq]
        have e6 : (2 : Nat) ^ 6 = 64 := rfl
        rw [e6]
        omega
      simp only [e, sel, Nat.blt_eq]
  have hhi := le_hiOf n
  rw [hgen (hiOf n), show 64 * hiOf n = m + (64 * hiOf n - m) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hiOf n - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi' => if_pos (Finset.mem_range.1 hi')

theorem sortK_spec {d n P : Nat} (h : sortK d n P = true) :
    ∀ i j, i < j → j < n → fget P i d < fget P j d := by
  have hs := ptAllBelow h (Nat.pred_le n)
  have step : ∀ i, i + 1 < n → fget P i d < fget P (i + 1) d := by
    intro i hi
    have := hs i (by rw [Nat.pred_eq_sub_one]; omega)
    rwa [Nat.blt_eq] at this
  intro i j hij hjn
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
    · exact lt_trans (ih h' (by omega)) (step j hjn)
    · exact step i hjn

theorem inW_iff {d n P z j : Nat} (hs : sortK d n P = true) (hg : gapK d n P z j = true) :
    inW d P z j = true ↔ ∃ k < n, fget P k d = z := by
  have hS := sortK_spec hs
  unfold gapK at hg
  unfold inW
  simp only [andB_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq,
    Nat.blt_eq, Nat.pred_eq_sub_one] at hg ⊢
  obtain ⟨hjn, hlo, hhi⟩ := hg
  constructor
  · rintro ⟨hj, he⟩
    exact ⟨j - 1, by omega, he⟩
  · rintro ⟨k, hk, rfl⟩
    have hkj : k + 1 = j := by
      rcases Nat.lt_trichotomy (k + 1) j with h1 | h1 | h1
      · rcases hlo with h3 | h3
        · omega
        · exact absurd (hS k (j - 1) (by omega) (by omega)) (by omega)
      · exact h1
      · rcases hhi with h3 | h3
        · omega
        · rcases Nat.lt_or_ge j k with h4 | h4
          · exact absurd (hS j k h4 hk) (by omega)
          · have hjk : j = k := by omega
            subst hjk
            omega
    subst hkj
    exact ⟨Nat.succ_pos k, by rw [Nat.add_sub_cancel]⟩

theorem imgK_spec {d n P G T : Nat} (h : imgK d n P G T = true) :
    ∀ i < n, ∃ k < n, fget P k d = vmF d G (fget P i d) := by
  unfold imgK at h
  rw [ptStrictB_eq] at h
  intro i hi
  have hi' := ptAllBelow h le_rfl i hi
  simp only [ptStrictB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hi'
  exact ⟨_, hi'.1, hi'.2⟩

theorem strictL_eq (L : List Nat) : ∀ k : List Nat → Bool, strictL L k = k L := by
  induction L with
  | nil => intro k; rfl
  | cons x L ih =>
    intro k
    change strictB x (fun x => strictL L fun L => k (x :: L)) = _
    rw [ptStrictB_eq]
    exact ih _

theorem memK_spec {x : Nat} : ∀ {L : List Nat}, memK x L = true → x ∈ L
  | [], h => absurd h Bool.false_ne_true
  | y :: L, h => by
    change orB (Nat.beq x y) (memK x L) = true at h
    rw [orB_eq, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memK_spec h)

theorem getL_mem : ∀ {L : List Nat} {g : Nat}, g < lenL L → getL 0 L g ∈ L
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: L, 0, _ => List.mem_cons_self
  | a :: L, g + 1, h => List.mem_cons_of_mem _ (getL_mem (L := L) (Nat.lt_of_succ_lt_succ h))

theorem forK_spec {d n P E : Nat} {Gs roots : List Nat} (h : forK d n P E Gs roots = true)
    (X : Set Nat) (hr : ∀ r ∈ roots, r ∈ X) (hG : ∀ g ∈ Gs, ∀ x ∈ X, vmF d g x ∈ X) :
    ∀ i < n, fget P i d ∈ X := by
  unfold forK at h
  rw [strictL_eq, strictL_eq] at h
  have hall := ptAllBelow h le_rfl
  have key : ∀ D, ∀ i < n, depF (fget E i (nat_lit 32)) < D → fget P i d ∈ X := by
    intro D
    induction D with
    | zero => intro i _ hd; exact absurd hd (Nat.not_lt_zero _)
    | succ D ih =>
      intro i hi hd
      have hi' := hall i hi
      simp only [ptStrictB_eq] at hi'
      revert hi'
      cases hz : Nat.beq (depF (fget E i (nat_lit 32))) (nat_lit 0)
      · intro hi'
        simp only [ptStrictB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hi'
        obtain ⟨hp, hg, hdp, hx⟩ := hi'
        rw [hx]
        exact hG _ (getL_mem hg) _ (ih _ hp (lt_of_lt_of_le hdp (Nat.lt_succ_iff.1 hd)))
      · intro hi'
        exact hr _ (memK_spec hi')
  exact fun i hi => key _ i hi (Nat.lt_succ_self _)

theorem gapsK_spec {d n P n' P' W : Nat} {h : Nat → Nat} (hg : gapsK d n P n' P' W h = true) :
    ∀ i < n, gapK d n' P' (h (fget P i d)) (fget W i 16) = true :=
  ptAllBelow hg le_rfl

theorem cntK_spec (d n P P' W : Nat) (h : Nat → Nat) (f : Nat → Bool) (pos : Bool) :
    cntK d n P P' W h f pos = ((Finset.range n).filter fun i =>
      f (fget P i d) = true ∧ inW d P' (h (fget P i d)) (fget W i 16) = pos).card := by
  unfold cntK
  rw [ptSumBelow _ _ _ le_rfl, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ptStrictN_eq, andB_eq]
  generalize f (fget P i d) = a
  generalize inW d P' (h (fget P i d)) (fget W i 16) = b
  cases a <;> cases b <;> cases pos <;> rfl

theorem cnt_card {d n P n' P' W : Nat} {h : Nat → Nat} {f : Nat → Bool} {pos : Bool}
    (hs : sortK d n' P' = true) (hg : gapsK d n P n' P' W h = true) :
    cntK d n P P' W h f pos = ((Finset.range n).filter fun i =>
      f (fget P i d) = true ∧ ((∃ k < n', fget P' k d = h (fget P i d)) ↔ pos = true)).card := by
  rw [cntK_spec]
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [← inW_iff hs (gapsK_spec hg i (Finset.mem_range.1 hi))]
  generalize inW d P' (h (fget P i d)) (fget W i 16) = c
  cases c <;> cases pos <;> simp

end CFSG.KC.F2PtSet

end
