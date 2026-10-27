module

public import Certificates.Data.Kernel.F2Word
public import Certificates.Data.Kernel.M1F2
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.F2W

open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem maskN_eq (w : Nat) : maskN w = 2 ^ w - 1 := by
  rw [maskN, pw2]
  change (1 <<< w) - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem orN_succ (n : Nat) (f : Nat → Nat) : orN (n + 1) f = f n ||| orN n f := rfl

theorem orN_zero (f : Nat → Nat) : orN 0 f = 0 := rfl

theorem testBit_orN_fields {d n : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < 2 ^ d) (p : Nat) :
    (orN n fun i => f i <<< (d * i)).testBit p =
      (decide (p < d * n) && (f (p / d)).testBit (p % d)) := by
  induction n with
  | zero => simp [orN_zero]
  | succ n ih =>
    rw [orN_succ, Nat.testBit_or, Nat.testBit_shiftLeft, ih fun i hi => hf i (by omega),
      Nat.mul_succ]
    have hn := hf n (by omega)
    by_cases h1 : p < d * n
    · have : ¬ (p ≥ d * n) := by omega
      simp [h1, this, show p < d * n + d by omega]
    · by_cases h2 : p < d * n + d
      · have hd : 0 < d := by omega
        have hq : p / d = n := by
          rw [Nat.div_eq_iff hd]
          constructor <;> [rw [Nat.mul_comm]; rw [Nat.mul_comm]] <;> omega
        have hr : p % d = p - d * n := by
          rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]
        simp [h1, h2, hq, hr, show p ≥ d * n by omega]
      · have hb : (f n).testBit (p - d * n) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega)))
        simp [h1, h2, hb]

theorem orN_fields_lt {d n : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < 2 ^ d) :
    (orN n fun i => f i <<< (d * i)) < 2 ^ (d * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_orN_fields hf]
  simp [Nat.not_lt.2 hi]

theorem orN_fields_mul {d n c : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < 2 ^ d)
    (hfc : ∀ i < n, f i * c < 2 ^ d) :
    (orN n fun i => f i <<< (d * i)) * c = orN n fun i => (f i * c) <<< (d * i) := by
  induction n with
  | zero => simp [orN_zero]
  | succ n ih =>
    have h1 := orN_fields_lt (n := n) (d := d) (f := f) fun i hi => hf i (by omega)
    have h2 := orN_fields_lt (n := n) (d := d) (f := fun i => f i * c) fun i hi => hfc i (by omega)
    rw [orN_succ, orN_succ, ← Nat.shiftLeft_add_eq_or_of_lt h1, ← Nat.shiftLeft_add_eq_or_of_lt h2,
      ← ih (fun i hi => hf i (by omega)) (fun i hi => hfc i (by omega)), Nat.add_mul,
      Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_right_comm]

theorem testBit_one_eq (j : Nat) : (1 : Nat).testBit j = decide (j = 0) := by
  cases j with
  | zero => rfl
  | succ j => simp [Nat.testBit_succ]

theorem rep_eq {d : Nat} (hd : 0 < d) :
    Nat.div (maskN (Nat.mul d d)) (maskN d) = orN d fun i => 1 <<< (d * i) := by
  have h1 : ∀ i < d, (1 : Nat) < 2 ^ d := fun _ _ => Nat.one_lt_two_pow (by omega)
  have hm : (orN d fun i => 1 <<< (d * i)) * (2 ^ d - 1) = 2 ^ (d * d) - 1 := by
    have h := orN_fields_mul (c := 2 ^ d - 1) (f := fun _ => 1) h1
      (fun _ _ => by rw [Nat.one_mul]; exact Nat.sub_lt (Nat.two_pow_pos d) Nat.one_pos)
    simp only [Nat.one_mul] at h
    rw [h]
    apply Nat.eq_of_testBit_eq
    intro p
    rw [testBit_orN_fields (fun _ _ => Nat.sub_lt (Nat.two_pow_pos d) Nat.one_pos),
      Nat.testBit_two_pow_sub_one,
      Nat.testBit_two_pow_sub_one]
    simp [Nat.mod_lt p hd]
  have hpos : 0 < 2 ^ d - 1 := by have := Nat.one_lt_two_pow (n := d) (by omega); omega
  rw [maskN_eq, maskN_eq]
  change (2 ^ (d * d) - 1) / (2 ^ d - 1) = _
  rw [← hm, Nat.mul_div_cancel _ hpos]

theorem col_eq {d : Nat} (hd : 0 < d) (A k : Nat) :
    (A >>> k) &&& (orN d fun i => 1 <<< (d * i)) =
      orN d fun i => (A.testBit (d * i + k)).toNat <<< (d * i) := by
  have h1 : ∀ i < d, (1 : Nat) < 2 ^ d := fun _ _ => Nat.one_lt_two_pow (by omega)
  have h2 : ∀ i < d, (A.testBit (d * i + k)).toNat < 2 ^ d := fun i hi =>
    Nat.lt_of_le_of_lt (Bool.toNat_le _) (h1 i hi)
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, testBit_orN_fields h1, testBit_orN_fields h2, Nat.testBit_shiftRight,
    testBit_one_eq, Nat.add_comm k p]
  by_cases hp : p % d = 0
  · have hpd : d * (p / d) = p := by have := Nat.div_add_mod p d; omega
    rw [hp, hpd]
    cases A.testBit (p + k) <;> simp
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hp
    rw [hj]
    cases (A.testBit (d * (p / d) + k)) <;> simp [Nat.testBit_succ]

theorem toNat_mul_lt {d : Nat} (b : Bool) : b.toNat * (2 ^ d - 1) < 2 ^ d := by
  have := Nat.one_le_two_pow (n := d)
  cases b
  · simp
  · simp only [Bool.toNat_true, Nat.one_mul]
    omega

theorem testBit_term {d : Nat} (hd : 0 < d) (A B k p : Nat) :
    ((((A >>> k) &&& (orN d fun i => 1 <<< (d * i))) * (2 ^ d - 1)) &&&
      (((B >>> (d * k)) &&& (2 ^ d - 1)) * (orN d fun i => 1 <<< (d * i)))).testBit p =
      (decide (p < d * d) && (A.testBit (d * (p / d) + k) && B.testBit (d * k + p % d))) := by
  have h1 : ∀ i < d, (1 : Nat) < 2 ^ d := fun _ _ => Nat.one_lt_two_pow (by omega)
  have hrow : (B >>> (d * k)) &&& (2 ^ d - 1) < 2 ^ d := by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos d)
  rw [col_eq hd, orN_fields_mul (fun i hi => Nat.lt_of_le_of_lt (Bool.toNat_le _) (h1 i hi))
    (fun _ _ => toNat_mul_lt _), Nat.mul_comm _ (orN d _)]
  have hb := orN_fields_mul (c := (B >>> (d * k)) &&& (2 ^ d - 1)) (f := fun _ => 1) h1
    (fun _ _ => by rw [Nat.one_mul]; exact hrow)
  simp only [Nat.one_mul] at hb
  rw [hb, Nat.testBit_and, testBit_orN_fields (fun _ _ => toNat_mul_lt _),
    testBit_orN_fields (fun _ _ => hrow)]
  have hm := Nat.mod_lt p hd
  have hF : ((A.testBit (d * (p / d) + k)).toNat * (2 ^ d - 1)).testBit (p % d) =
      A.testBit (d * (p / d) + k) := by
    cases A.testBit (d * (p / d) + k) <;> simp [hm]
  rw [hF, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  cases decide (p < d * d) <;> simp [hm]

theorem testBit_xorRec (T : Nat → Nat) (p : Nat) : ∀ n : Nat,
    (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ T k) n : Nat).testBit p =
      Nat.rec (motive := fun _ => Bool) false (fun k b => b ^^ (T k).testBit p) n
  | 0 => by simp
  | n + 1 => by
    change (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ T k) n ^^^ T n).testBit p = _
    rw [Nat.testBit_xor, testBit_xorRec T p n]

theorem mulW_eq_rec (d A B : Nat) : mulW d A B =
    Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^
      ((((A >>> k) &&& (Nat.div (maskN (Nat.mul d d)) (maskN d))) * maskN d) &&&
        (((B >>> (d * k)) &&& maskN d) * Nat.div (maskN (Nat.mul d d)) (maskN d)))) d := by
  simp only [mulW, strictN_eq]
  rfl

theorem bit_eq (v k : Nat) : bit v k = v.testBit k := by
  rw [bit, Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((v >>> k) &&& 1) 1 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  cases h : Nat.beq (v / 2 ^ k % 2) 1
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · have := Nat.eq_of_beq_eq_true h
    simp [this]

theorem rec_congr {F G : Nat → Bool → Bool} (x : Bool) : ∀ n : Nat, (∀ k < n, ∀ b, F k b = G k b) →
    (Nat.rec (motive := fun _ => Bool) x F n : Bool) = Nat.rec (motive := fun _ => Bool) x G n
  | 0, _ => rfl
  | n + 1, h => by
    change F n (Nat.rec (motive := fun _ => Bool) x F n) = G n (Nat.rec (motive := fun _ => Bool) x G n)
    rw [rec_congr x n fun k hk => h k (by omega), h n (by omega)]

theorem rec_xor_false : ∀ n : Nat,
    (Nat.rec (motive := fun _ => Bool) false (fun _ b => b ^^ false) n : Bool) = false
  | 0 => rfl
  | n + 1 => by
    change (Nat.rec (motive := fun _ => Bool) false (fun _ b => b ^^ false) n ^^ false) = false
    rw [rec_xor_false n]
    rfl

theorem condRec_lt {d : Nat} (g : Nat → Nat) (c : Nat → Bool) (hg : ∀ k, g k < 2 ^ d) : ∀ n : Nat,
    (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => if c k then g k ^^^ acc else acc) n : Nat) <
      2 ^ d
  | 0 => Nat.two_pow_pos d
  | n + 1 => by
    change (if c n then g n ^^^ _ else _) < _
    split
    · exact Nat.xor_lt_two_pow (hg n) (condRec_lt g c hg n)
    · exact condRec_lt g c hg n

theorem testBit_condRec (g : Nat → Nat) (c : Nat → Bool) (j : Nat) : ∀ n : Nat,
    (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => if c k then g k ^^^ acc else acc) n : Nat).testBit j =
      Nat.rec (motive := fun _ => Bool) false (fun k b => (c k && (g k).testBit j) ^^ b) n
  | 0 => by simp
  | n + 1 => by
    change (if c n then g n ^^^ _ else _ : Nat).testBit j = ((c n && (g n).testBit j) ^^ _)
    rw [← testBit_condRec g c j n]
    cases c n <;> simp

theorem testBit_rowF (d M i j : Nat) (hj : j < d) : (rowF d M i).testBit j = M.testBit (i * d + j) := by
  rw [rowF, fget, maskN_eq]
  change ((M >>> (i * d)) &&& (2 ^ d - 1)).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  simp [hj]

theorem rowF_lt (d M i : Nat) : rowF d M i < 2 ^ d := by
  rw [rowF, fget, maskN_eq]
  change (M >>> (i * d)) &&& (2 ^ d - 1) < 2 ^ d
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos d)

theorem vmF_rec (d M v : Nat) : vmF d M v =
    Nat.rec (motive := fun _ => Nat) 0 (fun k acc => if v.testBit k then rowF d M k ^^^ acc else acc) d := by
  rw [vmF]
  congr
  funext k acc
  rw [← bit_eq]
  cases bit v k <;> rfl

theorem vmF_lt (d M v : Nat) : vmF d M v < 2 ^ d := by
  rw [vmF_rec]
  exact condRec_lt _ _ (rowF_lt d M) d

theorem testBit_vmF (d M v j : Nat) (hj : j < d) : (vmF d M v).testBit j =
    Nat.rec (motive := fun _ => Bool) false
      (fun k b => (v.testBit k && M.testBit (k * d + j)) ^^ b) d := by
  rw [vmF_rec, testBit_condRec]
  exact rec_congr false d fun k _ b => by rw [testBit_rowF d M k j hj]

theorem mulF_eq_orN (d A B : Nat) : mulF d A B = orN d fun i => vmF d B (rowF d A i) <<< (d * i) := by
  simp only [mulF, strictN_eq]
  rfl

theorem mulW_eq (d A B : Nat) : mulW d A B = mulF d A B := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [mulW_eq_rec, mulF_eq_orN]
    rfl
  apply Nat.eq_of_testBit_eq
  intro p
  rw [mulW_eq_rec, rep_eq hd, maskN_eq, testBit_xorRec, mulF_eq_orN,
    testBit_orN_fields fun i _ => vmF_lt d B (rowF d A i)]
  simp only [testBit_term hd]
  have hm := Nat.mod_lt p hd
  by_cases hp : p < d * d
  · simp only [hp, decide_true, Bool.true_and]
    rw [testBit_vmF d B _ _ hm]
    refine rec_congr false d fun k hk b => ?_
    rw [testBit_rowF d A _ _ hk, Bool.xor_comm, Nat.mul_comm (p / d), Nat.mul_comm d k]
  · simp only [hp, decide_false, Bool.false_and]
    exact rec_xor_false d

end CFSG.KC.F2W

end
