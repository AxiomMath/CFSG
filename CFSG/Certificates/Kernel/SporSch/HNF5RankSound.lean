
module

public import Certificates.Data.Kernel.SporSch.HNF5Rank
public import CFSG.Certificates.Kernel.SporSch.HNF5ModSound
public import CFSG.Sporadic.HNSchreier.RankCheckInputs
public import Mathlib.Data.List.GetD
import CFSG.Certificates.Kernel.SporSch.HNF5Lane

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native

theorem subId5_sound {T X : Nat → Nat} (hT : Canon5 T) (h : ∀ i < 133, X i = subRow5 T i) :
    subId (rows5 T) = rows5 X := by
  unfold subId
  conv_rhs => unfold rows5
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  rw [rows5_get _ i.isLt j.isLt, h i i.isLt]
  unfold subRow5
  rw [F5Lane.lane5_red5 _ j.isLt]
  have e : Nat.add (T i.val) (Nat.shiftLeft (nat_lit 4) (Nat.mul (nat_lit 16) i.val)) =
      ∑ k ∈ Finset.range 133, (lane5 (T i.val) k + if i.val = k then 4 else 0) * 2 ^ (16 * k) := by
    change T i.val + 4 <<< (16 * i.val) = _
    rw [Nat.shiftLeft_eq]
    simp only [Nat.add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [← F5Lane.row_expand (F5Lane.canon5_lt (hT i i.isLt)), Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_range.2 i.isLt)]
  have hb : ∀ k < 133, lane5 (T i.val) k + (if i.val = k then 4 else 0) < 2 ^ 16 := fun k hk => by
    have := F5Lane.canon5_lane (hT i i.isLt) hk
    split_ifs <;> omega
  rw [e, F5Lane.lane_sum5 hb j.isLt]

theorem diag5_sound {X : Nat → Nat} {r : Nat} (h : ∀ i < 133, X i = diagRow5 r i) :
    rows5 X = diagR r := by
  unfold rows5 diagR
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  rw [h i i.isLt]
  unfold diagRow5
  rw [LyM.nIf_eqL]
  by_cases hr : i.val < r
  · rw [ite_eq_left (Eq.mpr Nat.blt_eq hr), F5Lane.lane5_idRow5]
    by_cases hij : i.val = j.val
    · rw [ite_eq_left hij.symm, ite_eq_left ⟨hij, hr⟩]
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right fun hc => hij hc.1]
  · have hb : ¬ Nat.blt i.val r = true := fun hc => hr (Eq.mp Nat.blt_eq hc)
    rw [ite_eq_right hb, F5Lane.lane5_zero, ite_eq_right fun hc => hr hc.2]

@[expose] def chainOK (OP L R : Nat → Nat) (lt : Int → Nat) (n : Nat) (w : List Int) (o : Nat) :
    Bool :=
  decide (1 ≤ w.length) && decide (o + w.length ≤ n) &&
    w.all (fun l => decide (lt l < n)) &&
    OP o == 1 && L o == lt (w.getD (w.length - 1) 0) &&
    (List.range (w.length - 1)).all fun u => OP (o + u + 1) == 0 &&
      L (o + u + 1) == lt (w.getD (w.length - 2 - u) 0) && R (o + u + 1) == o + u

theorem mword_one (S Si : Array (Array (Array Nat))) (l : Int) :
    mword S Si [l] = mulM 5 133 (mletter S Si l) (idM 133) := rfl

theorem chain5_eq {MT OP L R : Nat → Nat} {n : Nat}
    (hall : ∀ k < n, ∀ b < 7, entryOK2 MT OP L R k b = true)
    (hcan : ∀ k < n, Canon5 (slice5 MT k)) {S Si : Array (Array (Array Nat))} {lt : Int → Nat}
    {w : List Int} {o : Nat} (hlet : ∀ l ∈ w, mletter S Si l = rows5 (slice5 MT (lt l)))
    (h : chainOK OP L R lt n w o = true) :
    mword S Si w = rows5 (slice5 MT (o + w.length - 1)) := by
  simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, hlen⟩, hl⟩, ho⟩, hL⟩, hs⟩ := h
  have hlt : ∀ t < w.length, mletter S Si (w.getD t 0) = rows5 (slice5 MT (lt (w.getD t 0))) ∧
      lt (w.getD t 0) < n := fun t ht => by
    have hm : w.getD t 0 ∈ w := by
      rw [List.getD_eq_getElem _ _ ht]
      exact List.getElem_mem ht
    exact ⟨hlet _ hm, hl _ hm⟩
  have key : ∀ t, t < w.length →
      mword S Si (w.drop (w.length - 1 - t)) = rows5 (slice5 MT (o + t)) := by
    intro t
    induction t with
    | zero =>
      intro _
      have e : w.drop (w.length - 1 - 0) = [w.getD (w.length - 1) 0] := by
        rw [Nat.sub_zero, List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega),
          List.getD_eq_getElem _ _ (by omega)]
      rw [e, mword_one, (hlt _ (by omega)).1, mulM5_idR (hcan _ (hlt _ (by omega)).2),
        Nat.add_zero]
      exact rows5_congr fun i hi => entry2_copy (hall o (by omega)) ho hL i hi
    | succ t ih =>
      intro ht
      obtain ⟨⟨a, b⟩, c⟩ := hs t (by omega)
      have e : w.drop (w.length - 1 - (t + 1)) =
          w.getD (w.length - 2 - t) 0 :: w.drop (w.length - 1 - t) := by
        rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ (by omega)]
        congr 2 <;> omega
      rw [e, mword, ih (by omega), (hlt _ (by omega)).1,
        mulM5_sound (hcan _ (hlt _ (by omega)).2) (hcan _ (by omega))
          (entry2_mul (hall _ (by omega)) a b c)]
      rfl
  have := key (w.length - 1) (by omega)
  rwa [show w.length - 1 - (w.length - 1) = 0 by omega, List.drop_zero,
    show o + (w.length - 1) = o + w.length - 1 by omega] at this

end CFSG.KS.SporSch

end
