module

public import Certificates.Data.Kernel.J3LocalK
public import CFSG.Certificates.Kernel.AxisPlane.Pop
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace CFSG.KC.J3Loc

open CFSG.KC.AxisPlane CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.F2W CFSG.KC.Loop

theorem testBit_toNatB (b : Bool) (i : Nat) : b.toNat.testBit i = (decide (i = 0) && b) := by
  cases b <;> simp [testBit_one_eq]

theorem lt128 {x : Nat} (h : x < 2 ^ 80) : x < 2 ^ 128 :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by norm_num))

theorem lanes_ext {g : Nat → Nat} {n X : Nat} (hg : ∀ i < n, g i < 2 ^ 128)
    (h : ∀ q, X.testBit q = (decide (q < 128 * n) && (g (q / 128)).testBit (q % 128))) :
    X = lanes 128 g n :=
  Nat.eq_of_testBit_eq fun q => by rw [h q, testBit_lanes (by norm_num) n hg q]

theorem lanes_split (w : Nat) (g : Nat → Nat) (a : Nat) : ∀ b,
    lanes w g (a + b) = lanes w g a + 2 ^ (w * a) * lanes w (fun i => g (a + i)) b
  | 0 => by simp [lanes]
  | b + 1 => by
    rw [← Nat.add_assoc, lanes, lanes_split w g a b, lanes, Nat.mul_add w a b, Nat.pow_add]
    ring

theorem lanes_mulR (w r : Nat) (g : Nat → Nat) : ∀ n,
    lanes w g n * r = lanes w (fun i => g i * r) n
  | 0 => by simp [lanes]
  | n + 1 => by
    simp only [lanes]
    rw [← lanes_mulR w r g n]
    ring

theorem lanes_zeroF (w : Nat) : ∀ n, lanes w (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by simp [lanes, lanes_zeroF w n]

theorem lor_shift {x k : Nat} (y : Nat) (hx : x < 2 ^ k) : x ||| (y <<< k) = x + 2 ^ k * y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.add_comm, Nat.testBit_two_pow_mul_add _ hx]
  split
  · next h => simp [show ¬ j ≥ k by omega]
  · next h =>
    have : x.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this, show j ≥ k by omega]

theorem lanes_xor {f g : Nat → Nat} {n : Nat} (hf : ∀ i < n, f i < 2 ^ 128)
    (hg : ∀ i < n, g i < 2 ^ 128) :
    lanes 128 f n ^^^ lanes 128 g n = lanes 128 (fun i => f i ^^^ g i) n := by
  refine lanes_ext (fun i hi => Nat.xor_lt_two_pow (hf i hi) (hg i hi)) fun q => ?_
  rw [Nat.testBit_xor, testBit_lanes (by norm_num) n hf q, testBit_lanes (by norm_num) n hg q,
    Nat.testBit_xor]
  by_cases h : q < 128 * n <;> simp [h]

theorem lanesT_eq (P : Nat → Nat) : ∀ (f lo len : Nat), 1 ≤ len → len ≤ 2 ^ f →
    (∀ i < len, P (lo + i) < 2 ^ 128) → lanesT P f lo len = lanes 128 (fun i => P (lo + i)) len
  | 0, lo, len, h1, h2, _ => by
    have : len = 1 := by simp at h2; omega
    subst this
    simp [lanes]
    rfl
  | f + 1, lo, len, h1, h2, hP => by
    have e : lanesT P (f + 1) lo len = Bool.rec (motive := fun _ => Nat)
        (Nat.lor (lanesT P f lo (len / 2))
          (Nat.shiftLeft (lanesT P f (lo + len / 2) (len - len / 2)) (128 * (len / 2))))
        (P lo) (Nat.ble len 1) := rfl
    rw [e, CFSG.KC.OpsK.nIf_eq]
    split
    · next h =>
      have : len = 1 := by
        have := Nat.le_of_ble_eq_true h
        omega
      subst this
      simp [lanes]
    · next h =>
      have hl : 2 ≤ len := by
        by_contra hc
        exact h (Nat.ble_eq_true_of_le (by omega))
      have hpow : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [Nat.pow_succ]; ring
      rw [lanesT_eq P f lo (len / 2) (by omega) (by omega) (fun i hi => hP i (by omega)),
        lanesT_eq P f (lo + len / 2) (len - len / 2) (by omega) (by omega)
          (fun i hi => by rw [Nat.add_assoc]; exact hP _ (by omega))]
      change lanes 128 _ (len / 2) ||| (lanes 128 _ (len - len / 2) <<< (128 * (len / 2))) = _
      rw [lor_shift _ (lanes_lt _ fun i hi => hP i (by omega))]
      conv_rhs => rw [show len = len / 2 + (len - len / 2) by omega]
      rw [lanes_split]
      simp only [Nat.add_assoc]

theorem lanesP_eq {P : Nat → Nat} {N : Nat} (h1 : 1 ≤ N) (h2 : N ≤ 65536)
    (hP : ∀ i < N, P i < 2 ^ 128) : lanesP P N = lanes 128 P N := by
  unfold lanesP
  rw [lanesT_eq P 16 0 N h1 (by norm_num; omega) (fun i hi => by rw [Nat.zero_add]; exact hP i hi)]
  simp only [Nat.zero_add]

theorem pw2_eqP (w : Nat) : pw2 w = 2 ^ w := by
  unfold pw2
  exact Nat.one_shiftLeft w

theorem onesL_mul : ∀ N, lanes 128 (fun _ => 1) N * (2 ^ 128 - 1) = 2 ^ (128 * N) - 1
  | 0 => by simp [lanes]
  | N + 1 => by
    simp only [lanes]
    rw [Nat.add_mul, onesL_mul N, Nat.mul_one, show 128 * (N + 1) = 128 * N + 128 by ring,
      Nat.pow_add]
    have ha : 1 ≤ 2 ^ (128 * N) := Nat.one_le_two_pow
    have hc : (2 : Nat) ^ 128 = (2 ^ 128 - 1) + 1 := by norm_num
    generalize 2 ^ (128 * N) = a at ha ⊢
    rw [hc, Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one]
    omega

theorem onesL_eq (N : Nat) : onesL N = lanes 128 (fun _ => 1) N := by
  unfold onesL
  rw [pw2_eqP, pw2_eqP]
  change (2 ^ (128 * N) - 1) / (2 ^ 128 - 1) = _
  exact Nat.div_eq_of_eq_mul_left (by norm_num) (onesL_mul N).symm

theorem testBit_ones (N q : Nat) : (lanes 128 (fun _ => 1) N).testBit q =
    (decide (q < 128 * N) && decide (q % 128 = 0)) := by
  rw [testBit_lanes (by norm_num) N (fun _ _ => by norm_num) q, testBit_one_eq]

theorem shift_and {P : Nat → Nat} {N j : Nat} (hj : j < 128) (hP : ∀ i < N, P i < 2 ^ 128) :
    (lanes 128 P N >>> j) &&& lanes 128 (fun _ => 1) N =
      lanes 128 (fun i => ((P i).testBit j).toNat) N := by
  refine lanes_ext (fun i _ => ?_) fun q => ?_
  · cases (P i).testBit j <;> norm_num
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, testBit_lanes (by norm_num) N hP,
    testBit_toNatB]
  by_cases hq : q % 128 = 0
  · by_cases hN : q < 128 * N
    · have e1 : (j + q) / 128 = q / 128 := by omega
      have e2 : (j + q) % 128 = j := by omega
      have e3 : j + q < 128 * N := by omega
      simp [hq, hN, e1, e2, e3]
    · simp [hN]
  · simp [hq]

@[expose] noncomputable def vmP (T v : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => if v.testBit j then rowF 80 T j ^^^ acc else acc) k

theorem vmP_lt (T v : Nat) : ∀ k, vmP T v k < 2 ^ 80
  | 0 => by simp [vmP]
  | k + 1 => by
    change (if v.testBit k then rowF 80 T k ^^^ vmP T v k else vmP T v k) < 2 ^ 80
    split
    · exact Nat.xor_lt_two_pow (rowF_lt 80 T k) (vmP_lt T v k)
    · exact vmP_lt T v k

theorem colAllR_eq {P : Nat → Nat} {N : Nat} (T : Nat) (hP : ∀ i < N, P i < 2 ^ 128) :
    ∀ k, k ≤ 128 → colAllR T (lanes 128 P N) (lanes 128 (fun _ => 1) N) k =
      lanes 128 (fun i => vmP T (P i) k) N
  | 0, _ => (lanes_zeroF 128 N).symm
  | k + 1, hk => by
    change Nat.xor (colAllR T (lanes 128 P N) (lanes 128 (fun _ => 1) N) k)
      (((lanes 128 P N >>> k) &&& lanes 128 (fun _ => 1) N) * rowF 80 T k) = _
    rw [colAllR_eq T hP k (by omega), shift_and (by omega) hP, lanes_mulR]
    change lanes 128 _ N ^^^ lanes 128 _ N = _
    rw [lanes_xor (fun i _ => lt128 (vmP_lt T (P i) k)) (fun i _ => ?_)]
    · congr 1
      funext i
      change _ = if (P i).testBit k then rowF 80 T k ^^^ vmP T (P i) k else vmP T (P i) k
      cases (P i).testBit k
      · simp
      · simp [Nat.xor_comm]
    · cases (P i).testBit k
      · simp
      · simpa using lt128 (rowF_lt 80 T k)

theorem tb80 {D : Nat} (hD : D < 2 ^ 80) : (D + (2 ^ 80 - 1)).testBit 80 = decide (D ≠ 0) := by
  by_cases h0 : D = 0
  · subst h0
    simp only [Nat.zero_add, ne_eq, not_true_eq_false, decide_false]
    exact Nat.testBit_lt_two_pow (by norm_num)
  · have e : D + (2 ^ 80 - 1) = 2 ^ 80 + (D - 1) := by omega
    rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)]
    simp [h0]

theorem xor_ne_zero {a b : Nat} : a ^^^ b ≠ 0 ↔ a ≠ b := by
  constructor
  · intro h e
    subst e
    exact h (Nat.xor_self a)
  · intro h e
    apply h
    have := congrArg (· ^^^ b) e
    simpa [Nat.xor_assoc] using this

theorem movedL_eq {P : Nat → Nat} {N : Nat} (T : Nat) (hP : ∀ i < N, P i < 2 ^ 80) :
    movedL T (lanes 128 P N) (lanes 128 (fun _ => 1) N) =
      lanes 128 (fun i => (decide (vmF 80 T (P i) ≠ P i)).toNat) N := by
  have hP' : ∀ i < N, P i < 2 ^ 128 := fun i hi => lt128 (hP i hi)
  have hV : ∀ i, vmF 80 T (P i) = vmP T (P i) 80 := fun i => vmF_rec 80 T (P i)
  have hD : ∀ i < N, vmF 80 T (P i) ^^^ P i < 2 ^ 80 := fun i hi =>
    Nat.xor_lt_two_pow (vmF_lt 80 T (P i)) (hP i hi)
  have x1 : Nat.xor (colAllR T (lanes 128 P N) (lanes 128 (fun _ => 1) N) 80) (lanes 128 P N) =
      lanes 128 (fun i => vmF 80 T (P i) ^^^ P i) N := by
    rw [colAllR_eq T hP' 80 (by norm_num)]
    change lanes 128 _ N ^^^ lanes 128 _ N = _
    rw [lanes_xor (fun i _ => lt128 (vmP_lt T (P i) 80)) hP']
    simp only [hV]
  have x2 : Nat.mul (lanes 128 (fun _ => 1) N) (maskN 80) = lanes 128 (fun _ => 2 ^ 80 - 1) N := by
    change lanes 128 _ N * maskN 80 = _
    rw [maskN_eq, lanes_mulR]
    simp only [Nat.one_mul]
  unfold movedL
  rw [x1, x2]
  change ((lanes 128 _ N + lanes 128 _ N) >>> 80) &&& lanes 128 (fun _ => 1) N = _
  rw [lanes_add]
  have hS : ∀ i < N, (vmF 80 T (P i) ^^^ P i) + (2 ^ 80 - 1) < 2 ^ 128 := fun i hi => by
    have := hD i hi
    omega
  refine lanes_ext (fun i _ => ?_) fun q => ?_
  · cases decide (vmF 80 T (P i) ≠ P i) <;> norm_num
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, testBit_lanes (by norm_num) N hS,
    testBit_toNatB]
  by_cases hq : q % 128 = 0
  · by_cases hN : q < 128 * N
    · have e1 : (80 + q) / 128 = q / 128 := by omega
      have e2 : (80 + q) % 128 = 80 := by omega
      have e3 : 80 + q < 128 * N := by omega
      have hi : q / 128 < N := by omega
      rw [e1, e2, tb80 (hD _ hi)]
      simp [hq, hN, e3, xor_ne_zero]
    · simp [hN]
  · simp [hq]

theorem testBit_xsFold (q : Nat) : ∀ (xs : List Nat) (acc : Nat),
    (xs.foldl (fun acc i => Nat.lor acc (pw2 (Nat.mul 128 i))) acc).testBit q =
      (acc.testBit q || xs.any fun x => decide (128 * x = q))
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, testBit_xsFold q xs]
    change ((acc ||| pw2 (128 * x)).testBit q || _) = _
    rw [Nat.testBit_or, pw2_eqP, Nat.testBit_two_pow, List.any_cons, Bool.or_assoc]

theorem moved_of_K {T : Nat} {P : Nat → Nat} {N : Nat} {xs : List Nat} (h1 : 1 ≤ N)
    (h2 : N ≤ 65536) (hP : ∀ i < N, P i < 2 ^ 80)
    (h : Nat.beq (Nat.lor (movedL T (lanesP P N) (onesL N)) (xsMask xs)) (onesL N) = true) :
    ∀ i < N, xs.contains i = true ∨ vmF 80 T (P i) ≠ P i := by
  intro i hi
  rw [lanesP_eq h1 h2 fun i hi => lt128 (hP i hi), onesL_eq, movedL_eq T hP] at h
  have e := congrArg (fun x => x.testBit (128 * i)) (Nat.eq_of_beq_eq_true h)
  change (Nat.testBit (_ ||| xsMask xs) _) = _ at e
  rw [Nat.testBit_or, testBit_ones, xsMask, testBit_xsFold, testBit_lanes (by norm_num) N
    (fun i _ => by cases decide (vmF 80 T (P i) ≠ P i) <;> norm_num), testBit_toNatB] at e
  have e1 : 128 * i / 128 = i := by omega
  have e2 : 128 * i % 128 = 0 := by omega
  have e3 : 128 * i < 128 * N := by omega
  simp only [e1, e2, e3, decide_true, Bool.true_and, Nat.zero_testBit, Bool.false_or] at e
  by_cases hm : vmF 80 T (P i) ≠ P i
  · exact Or.inr hm
  · left
    simp only [hm, decide_false, Bool.false_or, List.any_eq_true, decide_eq_true_eq] at e
    obtain ⟨x, hx, hxi⟩ := e
    have : x = i := by omega
    subst this
    exact List.elem_eq_true_of_mem hx

end CFSG.KC.J3Loc

end
