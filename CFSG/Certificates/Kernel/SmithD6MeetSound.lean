module

public import Certificates.Data.Kernel.SmithD6.MeetK
public import CFSG.Certificates.Kernel.SmithD6KcSound

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree

theorem nthB_eq : ∀ (l : List (Array Nat)) (k : Nat), nthB l k = l.getD k #[]
  | [], _ => by
    change #[] = _
    simp
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => by
    rw [List.getD_cons_succ]
    exact nthB_eq l k

theorem xor_eq_zero_iff' {a b : Nat} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· ^^^ b) h
    simpa [Nat.xor_assoc] using this
  · rintro rfl
    exact Nat.xor_self a

theorem xor_left_comm' (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

theorem xor_cancel_left' (a c : Nat) : a ^^^ (a ^^^ c) = c := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem selF_xor : ∀ (bs : List Nat) (g h : Nat → Bool),
    selF (fun m => g m ^^ h m) bs = selF g bs ^^^ selF h bs
  | [], _, _ => by simp [selF]
  | b :: bs, g, h => by
    simp only [selF]
    rw [selF_xor bs (fun m => g (m + 1)) (fun m => h (m + 1))]
    cases g 0 <;> cases h 0 <;>
      simp [Nat.xor_assoc, Nat.xor_comm, xor_left_comm', xor_cancel_left']

theorem selF_false : ∀ (bs : List Nat), selF (fun _ => false) bs = 0
  | [] => rfl
  | b :: bs => by
    simp only [selF]
    rw [selF_false bs]
    simp

theorem kcRed_def (bs ps : List Nat) (x : Nat) : kcRed bs ps x = x ^^^ kcPick x bs ps := rfl

theorem kcRed_xor {bs ps : List Nat} (h : bs.length = ps.length) (x y : Nat) :
    kcRed bs ps (x ^^^ y) = kcRed bs ps x ^^^ kcRed bs ps y := by
  rw [kcRed_def, kcRed_def, kcRed_def, kcPick_eq _ bs ps h, kcPick_eq _ bs ps h,
    kcPick_eq _ bs ps h]
  have e : (fun m => (x ^^^ y).testBit (ps.getD m 0)) =
      fun m => x.testBit (ps.getD m 0) ^^ y.testBit (ps.getD m 0) := by
    funext m
    rw [Nat.testBit_xor]
  rw [e, selF_xor]
  simp only [Nat.xor_assoc, Nat.xor_comm, xor_left_comm']

theorem kcRed_zero {bs ps : List Nat} (h : bs.length = ps.length) : kcRed bs ps 0 = 0 := by
  rw [kcRed_def, kcPick_eq _ bs ps h]
  simp [selF_false]

theorem kcRed_selF {bs ps : List Nat} (h : bs.length = ps.length) :
    ∀ (bi : List Nat) (g : Nat → Bool), kcRed bs ps (selF g bi) = selF g (bi.map (kcRed bs ps))
  | [], _ => by simp [selF, kcRed_zero h]
  | b :: bi, g => by
    simp only [selF, List.map_cons]
    rw [kcRed_xor h, kcRed_selF h bi]
    cases g 0
    · simp [kcRed_zero h]
    · rfl

theorem kcRedL_eq (bs ps : List Nat) : ∀ bi : List Nat, kcRedL bs ps bi = bi.map (kcRed bs ps)
  | [] => rfl
  | b :: bi => by
    change kcRed bs ps b :: kcRedL bs ps bi = _
    rw [kcRedL_eq bs ps bi, List.map_cons]

theorem countP_range_two_mul (p : Nat → Bool) : ∀ N, (List.range (2 * N)).countP p =
    (List.range N).countP (fun d => p (2 * d)) + (List.range N).countP (fun d => p (2 * d + 1))
  | 0 => by simp
  | N + 1 => by
    have e : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
    rw [e, List.range_succ, List.range_succ, List.range_succ, List.countP_append,
      List.countP_append, List.countP_append, List.countP_append, countP_range_two_mul p N]
    simp only [List.countP_singleton]
    omega

theorem testBit_two_mul_succ (d m : Nat) : (2 * d).testBit (m + 1) = d.testBit m := by
  rw [Nat.testBit_add_one]
  congr 1
  omega

theorem testBit_two_mul_add_one_succ (d m : Nat) : (2 * d + 1).testBit (m + 1) = d.testBit m := by
  rw [Nat.testBit_add_one]
  congr 1
  omega

theorem kcZc_eq : ∀ (rs : List Nat) (acc : Nat), kcZc rs acc =
    (List.range (2 ^ rs.length)).countP fun d => acc ^^^ selF d.testBit rs == 0
  | [], acc => by
    change nIf(Nat.beq acc 0, 1, 0) = _
    cases h : Nat.beq acc 0
    · have := Nat.ne_of_beq_eq_false h
      simp [selF, this]
    · have := Nat.eq_of_beq_eq_true h
      simp [selF, this]
  | r :: rs, acc => by
    change Nat.add (kcZc rs acc) (kcZc rs (Nat.xor acc r)) = _
    rw [kcZc_eq rs acc, kcZc_eq rs, List.length_cons, Nat.pow_succ, Nat.mul_comm,
      countP_range_two_mul]
    have e1 : (fun d => acc ^^^ selF (2 * d).testBit (r :: rs) == 0) =
        fun d => acc ^^^ selF d.testBit rs == 0 := by
      funext d
      simp only [selF]
      have h0 : (2 * d).testBit 0 = false := by simp [Nat.testBit_zero]
      rw [h0, selF_congr rs (g' := d.testBit) fun m _ => testBit_two_mul_succ d m]
      simp
    have e2 : (fun d => acc ^^^ selF (2 * d + 1).testBit (r :: rs) == 0) =
        fun d => Nat.xor acc r ^^^ selF d.testBit rs == 0 := by
      funext d
      simp only [selF]
      have h0 : (2 * d + 1).testBit 0 = true := by simp [Nat.testBit_zero]
      rw [h0, selF_congr rs (g' := d.testBit) fun m _ => testBit_two_mul_add_one_succ d m]
      simp only [cond_true]
      rw [← Nat.xor_assoc]
      rfl
    rw [e1, e2]
    rfl

theorem kcMem_eq_red (bs ps : List Nat) (x : Nat) : kcMem bs ps x = (kcRed bs ps x == 0) := by
  unfold kcMem
  rw [kcRed_def]
  cases h : Nat.beq (kcPick x bs ps) x
  · have h1 := Nat.ne_of_beq_eq_false h
    have h2 : ¬ x ^^^ kcPick x bs ps = 0 := fun e => h1 (xor_eq_zero_iff'.1 e).symm
    simp [h2]
  · have h1 := Nat.eq_of_beq_eq_true h
    rw [h1]
    simp

theorem kcMeetN_eq {bi bj pj : List Nat} (hi : bi.length = 6) (hj : bj.length = pj.length) :
    kcMeetN bi bj pj =
      ((List.range 64).filter fun d => kcMem bj pj (selF d.testBit bi)).length := by
  unfold kcMeetN
  rw [kcZc_eq, kcRedL_eq, List.length_map, hi, ← List.countP_eq_length_filter]
  congr 1
  funext d
  rw [kcMem_eq_red, kcRed_selF hj, Nat.zero_xor]

end CFSG.KD.SmithD6

end
