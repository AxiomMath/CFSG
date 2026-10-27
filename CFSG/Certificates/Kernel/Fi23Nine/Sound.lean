module

public import Certificates.Data.Kernel.Fi23Nine.Defs
public import CFSG.Certificates.Kernel.Fi23K.EqSound
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.Fi23Nine

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KS.Raw.Orb

@[expose] noncomputable def depOf (c : Nat) : Nat := Nat.shiftRight c (nat_lit 26)

@[expose] noncomputable def letOf (c : Nat) : Nat :=
  Nat.land (Nat.shiftRight c (nat_lit 15)) (nat_lit 63)

@[expose] noncomputable def zOf (c : Nat) : Nat := Nat.shiftRight c (nat_lit 25)

theorem beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa [Nat.blt_eq] using h

theorem forAt_spec {H D : Nat → Nat} {q : Nat} (h : forAt H D q = true) :
    rootOf (fD D 0 q) < 21 ∧
    (depOf (fD D 0 q) = 0 → q = fD D 1051 (rootOf (fD D 0 q))) ∧
    (depOf (fD D 0 q) ≠ 0 → letOf (fD D 0 q) < 42 ∧ ptOf (fD D 0 q) < 31671 ∧
      tb H (letOf (fD D 0 q)) (ptOf (fD D 0 q)) = q ∧
      rootOf (fD D 0 (ptOf (fD D 0 q))) = rootOf (fD D 0 q) ∧
      depOf (fD D 0 (ptOf (fD D 0 q))) = depOf (fD D 0 q) - 1) := by
  unfold forAt at h
  rw [strictB_eq, strictB_eq, strictB_eq, bAnd_eq, Bool.and_eq_true, bIf_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨blt_true h1, fun hd => ?_, fun hd => ?_⟩
  · have hb' : Nat.beq (depOf (fD D 0 q)) 0 = true := by
      rw [hd]
      rfl
    split_ifs at h2 with hb
    · exact beq_true h2
    · exact absurd hb' hb
  · split_ifs at h2 with hb
    · exact absurd (beq_true hb) hd
    rw [strictB_eq, strictB_eq, bAnd_eq, bAnd_eq, bAnd_eq, strictB_eq, bAnd_eq] at h2
    simp only [Bool.and_eq_true] at h2
    obtain ⟨hl, hp, he, hr, hd'⟩ := h2
    refine ⟨blt_true hl, blt_true hp, beq_true he, beq_true hr, ?_⟩
    exact (beq_true hd').trans (Nat.pred_eq_sub_one)

theorem forSl_spec {H D : Nat → Nat} {lo len : Nat} (h : forSl H D lo len = true) {q : Nat}
    (h1 : lo ≤ q) (h2 : q < lo + len) (hq : q < 31671) : forAt H D q = true := by
  unfold forSl at h
  have h' := allN_iff.1 h (q - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (q - lo) = q := by
    change lo + (q - lo) = q
    omega
  rw [e, bIf_eq, if_pos (by simpa [Nat.blt_eq] using hq)] at h'
  exact h'

theorem shiftRight_three (k : Nat) : Nat.shiftRight k (nat_lit 3) = k / 8 :=
  Nat.shiftRight_eq_div_pow k 3

theorem land_seven (k : Nat) : Nat.land k (nat_lit 7) = k % 8 :=
  Nat.and_two_pow_sub_one_eq_mod k 3

theorem lgK_spec {D : Nat → Nat} (h : lgK D = true) {k : Nat} (hk : k < 144) :
    fD D 990 k < 31671 ∧ rootOf (fD D 0 (fD D 990 k)) = 3 + k / 8 ∧
      (k % 8 ≠ 7 → fD D 990 k < fD D 990 (k + 1)) := by
  unfold lgK at h
  have h' := allN_iff.1 h k hk
  rw [strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, bIf_eq] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  refine ⟨blt_true h1, ?_, fun h7 => ?_⟩
  · have := beq_true h2
    rw [shiftRight_three] at this
    exact this
  · have hb : ¬ Nat.beq (Nat.land k (nat_lit 7)) (nat_lit 7) = true := by
      intro hb
      have := beq_true hb
      rw [land_seven] at this
      exact h7 this
    rw [if_neg hb] at h3
    exact blt_true h3

theorem trK_spec {A : Nat → Nat → Nat} {ok : Nat → Bool} {D : Nat → Nat} {o r n : Nat}
    (h : trK A ok D o r n = true) {k : Nat} (hk : k < n) :
    ptOf (fD D o k) < 31671 ∧ (k = 0 → ptOf (fD D o k) = r) ∧
      (k ≠ 0 → nodeOf (fD D o k) < k ∧ ok (zOf (fD D o k)) = true ∧
        A (zOf (fD D o k)) (ptOf (fD D o (nodeOf (fD D o k)))) = ptOf (fD D o k)) := by
  unfold trK at h
  have h' := allN_iff.1 h k hk
  unfold trAt at h'
  rw [strictB_eq, strictB_eq, bAnd_eq, Bool.and_eq_true, bIf_eq] at h'
  obtain ⟨h1, h2⟩ := h'
  refine ⟨blt_true h1, fun h0 => ?_, fun h0 => ?_⟩
  · have hb : Nat.beq k 0 = true := by
      rw [h0]
      rfl
    rw [if_pos hb] at h2
    exact beq_true h2
  · have hb : ¬ Nat.beq k 0 = true := fun hb => h0 (beq_true hb)
    rw [if_neg hb, strictB_eq, strictB_eq, bAnd_eq, bAnd_eq] at h2
    simp only [Bool.and_eq_true] at h2
    obtain ⟨ha, hb', hc⟩ := h2
    exact ⟨blt_true ha, hb', beq_true hc⟩

theorem srtK_spec {D : Nat → Nat} {o s n : Nat} (h : srtK D o s n = true) {j : Nat}
    (hj : j < n) :
    nodeOf (fD D s j) < n ∧ ptOf (fD D o (nodeOf (fD D s j))) = ptOf (fD D s j) ∧
      (j + 1 < n → ptOf (fD D s j) < ptOf (fD D s (j + 1))) := by
  unfold srtK at h
  have h' := allN_iff.1 h j hj
  unfold srtAt at h'
  rw [strictB_eq, strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
    bIf_eq] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  refine ⟨blt_true h1, beq_true h2, fun hj1 => ?_⟩
  rw [if_pos (by simpa [Nat.blt_eq] using hj1)] at h3
  exact blt_true h3

theorem memL_iff (p : Nat) : ∀ s : List Nat, memL p s = true ↔ p ∈ s
  | [] => by simp [memL]
  | a :: s => by
    have e : memL p (a :: s) = bIf(Nat.beq p a, true, memL p s) := rfl
    rw [e, bIf_eq, List.mem_cons, ← memL_iff p s]
    by_cases hp : p = a
    · subst hp
      simp
    · have hb : ¬ Nat.beq p a = true := fun hb => hp (beq_true hb)
      rw [if_neg hb]
      simp [hp]

theorem mapsL_iff (f : Nat → Nat) (t : List Nat) : ∀ s : List Nat,
    (List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(memL (f a) t, ih)) s) = true ↔
      ∀ a ∈ s, f a ∈ t
  | [] => by simp
  | a :: s => by
    change bAnd(memL (f a) t, _) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, mapsL_iff f t s, List.forall_mem_cons, memL_iff]

theorem mapsL_iff' (f : Nat → Nat) (s : List Nat) : mapsL f s = true ↔ ∀ a ∈ s, f a ∈ s :=
  mapsL_iff f s s

theorem clK_iff (H : Nat → Nat) (s : List Nat) :
    clK H s = true ↔ ∀ l < 42, ∀ a ∈ s, tb H l a ∈ s := by
  unfold clK
  rw [allN_iff]
  exact forall₂_congr fun l _ => mapsL_iff' _ _

theorem cK_aux (G D : Nat → Nat) (cw : List Nat) : ∀ (sp : List Nat) (j0 : Nat),
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun a _ ih j => bAnd(Nat.beq (wv G cw a) (fD D (nat_lit 1051) j), ih (Nat.succ j))) sp)
      j0 = true → ∀ j (hj : j < sp.length), wv G cw sp[j] = fD D 1051 (j0 + j)
  | [], _, _, j, hj => absurd hj (by simp)
  | a :: sp, j0, h, j, hj => by
    change bAnd(Nat.beq (wv G cw a) (fD D (nat_lit 1051) j0), _) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    cases j with
    | zero => exact beq_true h.1
    | succ j =>
      have := cK_aux G D cw sp (Nat.succ j0) h.2 j (by simpa using hj)
      rw [List.getElem_cons_succ, this]
      congr 1
      omega

theorem cK_spec {G D : Nat → Nat} {cw sp : List Nat} (h : cK G D cw sp = true) :
    ∀ j (hj : j < sp.length), wv G cw sp[j] = fD D 1051 (21 + j) :=
  cK_aux G D cw sp 21 h

theorem wf_nil (G : Nat → Nat) (x : Nat) : wf G [] x = x := rfl

theorem wf_cons (G : Nat → Nat) (r : Nat) (w : List Nat) (x : Nat) :
    wf G (r :: w) x = wf G w (tb G r x) := by
  change strictN (tb G r x) (wf G w) = _
  rw [strictN_eq]

theorem wf_append (G : Nat → Nat) : ∀ (u v : List Nat) (x : Nat),
    wf G (u ++ v) x = wf G v (wf G u x)
  | [], _, _ => rfl
  | r :: u, v, x => by rw [List.cons_append, wf_cons, wf_cons, wf_append G u v]

theorem wf_reverse (G : Nat → Nat) : ∀ (w : List Nat) (x : Nat), wf G w.reverse x = wv G w x
  | [], _ => rfl
  | r :: w, x => by
    rw [List.reverse_cons, wf_append, wf_reverse G w, wf_cons, wf_nil, wv_cons]

theorem itW_zero (G : Nat → Nat) (w : List Nat) (x : Nat) : itW G w 0 x = x := rfl

theorem itW_succ (G : Nat → Nat) (w : List Nat) (e x : Nat) :
    itW G w (e + 1) x = itW G w e (wf G w x) := by
  change strictN (wf G w x) (itW G w e) = _
  rw [strictN_eq]

theorem xyK_spec {G : Nat → Nat} {xw yw s2 s4 : List Nat} (h : xyK G xw yw s2 s4 = true) :
    (∀ b < 6, itW G xw 6 b = b ∧ itW G yw 12 b = b ∧
      itW G xw 2 (itW G yw 4 b) = itW G yw 4 (itW G xw 2 b)) ∧
    itW G xw 2 0 = 0 ∧ itW G yw 4 0 = 0 ∧
    (∀ a ∈ s2, itW G xw 2 a ∈ s2) ∧ (∀ a ∈ s2, itW G yw 4 a ∈ s2) ∧
    (∀ a ∈ s4, itW G xw 2 a ∈ s4) ∧ (∀ a ∈ s4, itW G yw 4 a ∈ s4) ∧
    itW G xw 2 2 ≠ 2 ∧ itW G yw 4 2 ≠ 2 ∧ itW G yw 4 2 ≠ itW G xw 2 2 ∧
    itW G yw 4 2 ≠ itW G xw 2 (itW G xw 2 2) := by
  unfold xyK at h
  simp only [bAnd_eq, strictB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨fun b hb => ?_, beq_true h2, beq_true h3, (mapsL_iff' _ _).1 h4, (mapsL_iff' _ _).1 h5,
    (mapsL_iff' _ _).1 h6, (mapsL_iff' _ _).1 h7, fun e => ?_, fun e => ?_, fun e => ?_,
    fun e => ?_⟩
  · have h' := allN_iff.1 h1 b hb
    simp only [Bool.and_eq_true] at h'
    exact ⟨beq_true h'.1, beq_true h'.2.1, beq_true h'.2.2⟩
  · rw [e] at h8
    exact absurd h8 (by decide)
  · rw [e] at h9
    exact absurd h9 (by decide)
  · rw [e, Nat.beq_refl] at h10
    exact absurd h10 (by decide)
  · rw [e, Nat.beq_refl] at h11
    exact absurd h11 (by decide)

end CFSG.KC.Fi23Nine

end
