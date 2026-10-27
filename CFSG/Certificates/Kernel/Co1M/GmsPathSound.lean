module

public import Certificates.Data.Kernel.GmsPathK
public import Certificates.Data.CFSGNative.Co1.S365Coset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.GmsPath

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1M Finset

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl
theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl
theorem xorB_eq (a b : Bool) : xorB a b = (a ^^ b) := by cases a <;> cases b <;> rfl
theorem beqB_eq (a b : Bool) : beqB a b = (a == b) := by cases a <;> cases b <;> rfl

theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem bit_eq (X i : Nat) : bit X i = X.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff, Nat.beq_eq,
    decide_eq_true_iff]

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem xor_left_comm' (x y z : Nat) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  rw [← Nat.xor_assoc, Nat.xor_comm x y, Nat.xor_assoc]

@[expose] noncomputable def vmR (d M v k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => nIf(bit v k, Nat.xor (rowF d M k) acc, acc)) k

theorem vmF_eq (d M v : Nat) : vmF d M v = vmR d M v d := rfl

theorem vmR_succ (d M v k : Nat) :
    vmR d M v (k + 1) = if v.testBit k then rowF d M k ^^^ vmR d M v k else vmR d M v k := by
  change Bool.rec (motive := fun _ => Nat) _ _ (bit v k) = _
  rw [bit_eq]
  cases v.testBit k <;> rfl

theorem vmR_xor (d M a b : Nat) : ∀ k, vmR d M (a ^^^ b) k = vmR d M a k ^^^ vmR d M b k := by
  intro k
  induction k with
  | zero =>
    change (0 : Nat) = 0 ^^^ 0
    rw [Nat.xor_self]
  | succ k ih =>
    rw [vmR_succ, vmR_succ, vmR_succ, ih, Nat.testBit_xor]
    cases a.testBit k <;> cases b.testBit k <;> simp only [Bool.false_xor, Bool.true_xor,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    · ac_rfl
    · ac_rfl
    · simp only [Nat.xor_assoc]
      rw [xor_left_comm' (vmR d M a k), ← Nat.xor_assoc (rowF d M k) (rowF d M k), Nat.xor_self,
        Nat.zero_xor]

theorem vmF_xor (d M a b : Nat) : vmF d M (a ^^^ b) = vmF d M a ^^^ vmF d M b :=
  vmR_xor d M a b d

theorem rowF_lt (d M i : Nat) : rowF d M i < 2 ^ d := by
  change (M >>> (i * d)) &&& (pw2 d - 1) < 2 ^ d
  rw [pw2_eq]
  exact Nat.and_lt_two_pow _ (by have := Nat.one_le_two_pow (n := d); omega)

theorem vmR_lt (d M v : Nat) : ∀ k, vmR d M v k < 2 ^ d := by
  intro k
  induction k with
  | zero => exact Nat.two_pow_pos d
  | succ k ih =>
    rw [vmR_succ]
    split
    · exact Nat.xor_lt_two_pow (rowF_lt d M k) ih
    · exact ih

theorem vmF_lt (d M v : Nat) : vmF d M v < 2 ^ d := vmR_lt d M v d

theorem vecMulN_eq_vmF {d : Nat} {R : Array Nat} {M : Nat}
    (hR : ∀ j < d, R[j]?.getD 0 = rowF d M j) (v : Nat) :
    CFSG.Sporadic.SmallF2.Native.vecMulN d R v = vmF d M v := by
  unfold CFSG.Sporadic.SmallF2.Native.vecMulN
  rw [vmF_eq]
  have key : ∀ k, k ≤ d → (List.range k).foldl (fun acc j => if v.testBit j then
      acc ^^^ (R[j]?.getD 0) else acc) 0 = vmR d M v k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        hR k (by omega), vmR_succ]
      split
      · exact Nat.xor_comm _ _
      · rfl
  exact key d le_rfl

@[expose] noncomputable def parR (x k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => xorB (bit x k) acc) k

theorem parF_eq (x : Nat) : parF x = parR x 24 := rfl

theorem parR_succ (x k : Nat) : parR x (k + 1) = (x.testBit k ^^ parR x k) := by
  change xorB (bit x k) (parR x k) = _
  rw [xorB_eq, bit_eq]

theorem parR_xor (x y : Nat) : ∀ k, parR (x ^^^ y) k = (parR x k ^^ parR y k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [parR_succ, parR_succ, parR_succ, ih, Nat.testBit_xor]
    simp only [Bool.xor_assoc, Bool.xor_left_comm]

theorem parF_xor (x y : Nat) : parF (x ^^^ y) = (parF x ^^ parF y) := parR_xor x y 24

theorem parF_zero : parF 0 = false := rfl

theorem parity24N_eq (x : Nat) : CFSG.Sporadic.Co1.S365Native.parity24N x = parF x := by
  unfold CFSG.Sporadic.Co1.S365Native.parity24N
  rw [parF_eq]
  have key : ∀ k, (List.range k).foldl (fun acc j => acc ^^ x.testBit j) false = parR x k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, parR_succ,
        Bool.xor_comm]
  exact key 24

theorem land_eq (a b : Nat) : Nat.land a b = a &&& b := rfl

theorem qK_xor (Q a b : Nat) : qK Q (a ^^^ b) = (qK Q a ^^ qK Q b ^^ polQ Q a b) := by
  unfold qK polQ
  rw [xorB_eq, vmF_xor]
  simp only [land_eq]
  rw [Nat.and_xor_distrib_left, Nat.and_xor_distrib_right, Nat.and_xor_distrib_right, parF_xor,
    parF_xor, parF_xor]
  simp only [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

theorem polQ_xor_left (Q a c b : Nat) : polQ Q (a ^^^ c) b = (polQ Q a b ^^ polQ Q c b) := by
  unfold polQ
  rw [xorB_eq, xorB_eq, xorB_eq, vmF_xor]
  simp only [land_eq]
  rw [Nat.and_xor_distrib_right, Nat.and_xor_distrib_left, parF_xor, parF_xor]
  simp only [Bool.xor_assoc, Bool.xor_left_comm]

theorem polQ_comm (Q a b : Nat) : polQ Q a b = polQ Q b a := by
  unfold polQ
  rw [xorB_eq, xorB_eq, Bool.xor_comm]

theorem polQ_xor_right (Q a b c : Nat) : polQ Q a (b ^^^ c) = (polQ Q a b ^^ polQ Q a c) := by
  rw [polQ_comm, polQ_xor_left, polQ_comm Q b, polQ_comm Q c]

theorem qK_zero (Q : Nat) : qK Q 0 = false := by
  have h := qK_xor Q 0 0
  rw [Nat.xor_self] at h
  have h2 : polQ Q 0 0 = false := by
    unfold polQ
    rw [xorB_eq, Bool.xor_self]
  rw [h2, Bool.xor_false, Bool.xor_self] at h
  exact h

theorem xor_two_pow_of_lt {z i : Nat} (hz : z < 2 ^ i) : z ^^^ 2 ^ i = z + 2 ^ i := by
  have h := Nat.two_pow_add_eq_or_of_lt hz 1
  rw [Nat.mul_one] at h
  rw [Nat.add_comm, h]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hj : i = j
  · subst hj
    rw [Nat.testBit_lt_two_pow hz]
    simp
  · simp [hj]

theorem lt_pow_induction {P : Nat → Prop} (h0 : P 0) :
    ∀ d, (∀ i < d, ∀ z < 2 ^ i, P z → P (z ^^^ 2 ^ i)) → ∀ z < 2 ^ d, P z := by
  intro d
  induction d with
  | zero =>
    intro _ z hz
    rw [Nat.pow_zero, Nat.lt_one_iff] at hz
    rwa [hz]
  | succ d ih =>
    intro hs z hz
    by_cases hlt : z < 2 ^ d
    · exact ih (fun i hi => hs i (by omega)) z hlt
    · have hp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
      have h1 : z - 2 ^ d < 2 ^ d := by omega
      have h2 := hs d (by omega) (z - 2 ^ d) h1 (ih (fun i hi => hs i (by omega)) _ h1)
      rwa [xor_two_pow_of_lt h1, Nat.sub_add_cancel (by omega)] at h2

theorem add_agree {f g : Nat → Bool} (hf : ∀ a b, f (a ^^^ b) = (f a ^^ f b))
    (hg : ∀ a b, g (a ^^^ b) = (g a ^^ g b)) {d : Nat} (h : ∀ i < d, f (2 ^ i) = g (2 ^ i)) :
    ∀ z < 2 ^ d, f z = g z := by
  have z0 : ∀ {k : Nat → Bool}, (∀ a b, k (a ^^^ b) = (k a ^^ k b)) → k 0 = false := by
    intro k hk
    have := hk 0 0
    rwa [Nat.xor_self, Bool.xor_self] at this
  refine lt_pow_induction (by rw [z0 hf, z0 hg]) d ?_
  intro i hi z _ hz
  rw [hf, hg, hz, h i hi]

theorem addN_agree {f g : Nat → Nat} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) {d : Nat} (h : ∀ i < d, f (2 ^ i) = g (2 ^ i)) :
    ∀ z < 2 ^ d, f z = g z := by
  have z0 : ∀ {k : Nat → Nat}, (∀ a b, k (a ^^^ b) = k a ^^^ k b) → k 0 = 0 := by
    intro k hk
    have := hk 0 0
    rwa [Nat.xor_self, Nat.xor_self] at this
  refine lt_pow_induction (by rw [z0 hf, z0 hg]) d ?_
  intro i hi z _ hz
  rw [hf, hg, hz, h i hi]

@[expose] def pol (f : Nat → Bool) (a b : Nat) : Bool := f (a ^^^ b) ^^ f a ^^ f b

theorem pol_def (f : Nat → Bool) (a b : Nat) : f (a ^^^ b) = (pol f a b ^^ f a ^^ f b) := by
  unfold pol
  generalize f (a ^^^ b) = A
  generalize f a = B
  generalize f b = C
  cases A <;> cases B <;> cases C <;> rfl

theorem quad_agree {f g : Nat → Bool}
    (hf : ∀ a c b, pol f (a ^^^ c) b = (pol f a b ^^ pol f c b))
    (hg : ∀ a c b, pol g (a ^^^ c) b = (pol g a b ^^ pol g c b)) {d : Nat}
    (h1 : ∀ i < d, f (2 ^ i) = g (2 ^ i))
    (h2 : ∀ i < d, ∀ j < d, pol f (2 ^ i) (2 ^ j) = pol g (2 ^ i) (2 ^ j)) :
    ∀ z < 2 ^ d, f z = g z := by
  have z0 : ∀ {k : Nat → Bool}, (∀ a c b, pol k (a ^^^ c) b = (pol k a b ^^ pol k c b)) →
      k 0 = false := by
    intro k hk
    have e : pol k 0 0 = k 0 := by
      unfold pol
      rw [Nat.xor_self, Bool.xor_self, Bool.false_xor]
    have := hk 0 0 0
    rwa [Nat.xor_self, Bool.xor_self, e] at this
  have hB : ∀ j < d, ∀ z < 2 ^ d, pol f z (2 ^ j) = pol g z (2 ^ j) := fun j hj =>
    add_agree (f := fun z => pol f z (2 ^ j)) (g := fun z => pol g z (2 ^ j))
      (fun a b => hf a b _) (fun a b => hg a b _) (fun i hi => h2 i hi j hj)
  refine lt_pow_induction (by rw [z0 hf, z0 hg]) d ?_
  intro i hi z hz ih
  have hzd : z < 2 ^ d := lt_of_lt_of_le hz (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [pol_def f, pol_def g, ih, h1 i hi, hB i hi z hzd]

theorem hypR_zero (z : Nat) : hypR 0 z = false := rfl

theorem hypR_succ (m z : Nat) : hypR (m + 1) z = (hd z ^^ hypR m (z / 4)) := by
  change xorB (hd z) (hypR m (Nat.div z 4)) = _
  rw [xorB_eq]
  rfl

theorem hd_eq (z : Nat) : hd z = decide (z % 4 = 3) := by
  change Nat.beq (z % 4) 3 = _
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

theorem hd_mod (z : Nat) : hd (z % 4) = hd z := by
  rw [hd_eq, hd_eq, Nat.mod_mod]

theorem xor_mod4 (a b : Nat) : (a ^^^ b) % 4 = a % 4 ^^^ b % 4 := by
  have := Nat.xor_mod_two_pow (a := a) (b := b) (n := 2)
  simpa using this

theorem xor_div4 (a b : Nat) : (a ^^^ b) / 4 = a / 4 ^^^ b / 4 := by
  have := Nat.xor_div_two_pow (a := a) (b := b) (n := 2)
  simpa using this

theorem hd_pol_add (a c b : Nat) : pol hd (a ^^^ c) b = (pol hd a b ^^ pol hd c b) := by
  unfold pol
  simp only [hd_eq, xor_mod4]
  have ha : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hc : c % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize a % 4 = A at *
  generalize b % 4 = B at *
  generalize c % 4 = C at *
  revert A B C
  decide

theorem pol_hypR_succ (m a b : Nat) :
    pol (hypR (m + 1)) a b = (pol hd a b ^^ pol (hypR m) (a / 4) (b / 4)) := by
  unfold pol
  rw [hypR_succ, hypR_succ, hypR_succ, xor_div4]
  simp only [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

theorem hypR_pol_add (m : Nat) :
    ∀ a c b, pol (hypR m) (a ^^^ c) b = (pol (hypR m) a b ^^ pol (hypR m) c b) := by
  induction m with
  | zero =>
    intro a c b
    simp [pol, hypR_zero]
  | succ m ih =>
    intro a c b
    rw [pol_hypR_succ, pol_hypR_succ, pol_hypR_succ, xor_div4, ih, hd_pol_add]
    simp only [Bool.xor_assoc, Bool.xor_left_comm]

theorem card_split (k N : Nat) (hk : 0 < k) (F : Nat → Nat → Bool) :
    ((range (k * N)).filter fun z => F (z % k) (z / k) = true).card =
      ∑ a ∈ range k, ((range N).filter fun w => F a w = true).card := by
  have e1 : ((range (k * N)).filter fun z => F (z % k) (z / k) = true).card =
      ((range k ×ˢ range N).filter fun p => F p.1 p.2 = true).card := by
    apply Finset.card_nbij' (fun z => (z % k, z / k)) (fun p => p.1 + k * p.2)
    · intro z hz
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_product] at hz ⊢
      refine ⟨⟨Nat.mod_lt _ hk, ?_⟩, hz.2⟩
      exact (Nat.div_lt_iff_lt_mul hk).2 (by rw [Nat.mul_comm]; exact hz.1)
    · intro p hp
      simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      refine ⟨by nlinarith, ?_⟩
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.add_mul_div_left _ _ hk,
        Nat.div_eq_of_lt h1, Nat.zero_add]
      exact h3
    · intro z _
      exact Nat.mod_add_div z k
    · intro p hp
      simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp
      obtain ⟨⟨h1, _⟩, _⟩ := hp
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.add_mul_div_left _ _ hk,
        Nat.div_eq_of_lt h1, Nat.zero_add]
  rw [e1, Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl fun a _ => (Finset.card_filter _ _).symm

@[expose] noncomputable def cnt (m : Nat) : Nat :=
  ((range (4 ^ m)).filter fun z => (!hypR m z) = true).card

theorem cnt_succ (m : Nat) : cnt (m + 1) = 2 * cnt m + 4 ^ m := by
  unfold cnt
  have e : range (4 ^ (m + 1)) = range (4 * 4 ^ m) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hz : ∀ z, (!hypR (m + 1) z) = (!(hd (z % 4) ^^ hypR m (z / 4))) := by
    intro z
    rw [hypR_succ, hd_mod]
  simp only [e, hz]
  rw [card_split 4 (4 ^ m) (by norm_num) (fun a w => !(hd a ^^ hypR m w))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  have h0 : hd 0 = false := rfl
  have h1 : hd 1 = false := rfl
  have h2 : hd 2 = false := rfl
  have h3 : hd 3 = true := rfl
  simp only [h0, h1, h2, h3, Bool.false_xor, Bool.true_xor, Bool.not_not]
  have hsum := Finset.card_filter_add_card_filter_not (s := range (4 ^ m))
    (fun w => hypR m w = true)
  have e3 : ((range (4 ^ m)).filter fun w => ¬ hypR m w = true) =
      (range (4 ^ m)).filter fun w => (!hypR m w) = true :=
    Finset.filter_congr fun w _ => by cases hypR m w <;> simp
  rw [e3, card_range] at hsum
  omega

def cF : Nat → Nat
  | 0 => 1
  | m + 1 => 2 * cF m + 4 ^ m

theorem cnt_eq_cF (m : Nat) : cnt m = cF m := by
  induction m with
  | zero => decide
  | succ m ih => rw [cnt_succ, ih, cF]

theorem cnt_ten : cnt 10 = 524800 := by
  rw [cnt_eq_cF]
  decide

@[expose] noncomputable def Zc (z : Nat) : Bool :=
  !hypR 12 z && !hypR 12 (z ^^^ 1) && !hypR 12 (z ^^^ 4) && !hypR 12 (z ^^^ 5)

theorem hypR_twelve (y : Nat) : hypR 12 y = (hypR 2 (y % 16) ^^ hypR 10 (y / 16)) := by
  rw [hypR_succ 11 y, hypR_succ 10 (y / 4), hypR_succ 1 (y % 16), hypR_succ 0 (y % 16 / 4),
    hypR_zero, hd_eq, hd_eq, hd_eq, hd_eq]
  have e1 : y % 16 % 4 = y % 4 := by omega
  have e2 : y % 16 / 4 % 4 = y / 4 % 4 := by omega
  have e3 : y / 4 / 4 = y / 16 := by omega
  rw [e1, e2, e3, Bool.xor_false, Bool.xor_assoc]

theorem xor_mod16 {y c : Nat} (hc : c < 16) : (y ^^^ c) % 16 = y % 16 ^^^ c := by
  have := Nat.xor_mod_two_pow (a := y) (b := c) (n := 4)
  rw [show (2 : Nat) ^ 4 = 16 by norm_num, Nat.mod_eq_of_lt hc] at this
  exact this

theorem xor_div16 {y c : Nat} (hc : c < 16) : (y ^^^ c) / 16 = y / 16 := by
  have := Nat.xor_div_two_pow (a := y) (b := c) (n := 4)
  rw [show (2 : Nat) ^ 4 = 16 by norm_num, Nat.div_eq_of_lt hc, Nat.xor_zero] at this
  exact this

@[expose] noncomputable def Zc' (a : Nat) (h : Bool) : Bool :=
  !(hypR 2 a ^^ h) && !(hypR 2 (a ^^^ 1) ^^ h) && !(hypR 2 (a ^^^ 4) ^^ h) &&
    !(hypR 2 (a ^^^ 5) ^^ h)

theorem Zc_eq (z : Nat) : Zc z = Zc' (z % 16) (hypR 10 (z / 16)) := by
  unfold Zc Zc'
  rw [hypR_twelve, hypR_twelve (z ^^^ 1), hypR_twelve (z ^^^ 4), hypR_twelve (z ^^^ 5),
    xor_mod16 (by norm_num), xor_mod16 (by norm_num), xor_mod16 (by norm_num),
    xor_div16 (by norm_num), xor_div16 (by norm_num), xor_div16 (by norm_num)]

@[expose] def zc0 (a : Nat) : Bool := a == 0 || a == 1 || a == 4 || a == 5

theorem Zc'_eq : ∀ a < 16, ∀ h : Bool, Zc' a h = (zc0 a && !h) := by
  decide

theorem card_hyp : ((range (2 ^ 24)).filter fun z => Zc z = true).card = 2099200 := by
  have e : range (2 ^ 24) = range (16 * 4 ^ 10) := by norm_num
  simp only [e, Zc_eq]
  rw [card_split 16 (4 ^ 10) (by norm_num) (fun a w => Zc' a (hypR 10 w))]
  have hterm : ∀ a ∈ range 16, ((range (4 ^ 10)).filter fun w => Zc' a (hypR 10 w) = true).card =
      if zc0 a = true then cnt 10 else 0 := by
    intro a ha
    have hfun : ∀ w, Zc' a (hypR 10 w) = (zc0 a && !hypR 10 w) := fun w =>
      Zc'_eq a (mem_range.1 ha) _
    simp only [hfun]
    by_cases h : zc0 a = true
    · simp only [h, Bool.true_and, ite_true]
      rfl
    · simp [h]
  rw [Finset.sum_congr rfl hterm, cnt_ten]
  decide

theorem card_filter_bij {f g : Nat → Nat} {n : Nat} (hf : ∀ z < n, f z < n) (hg : ∀ z < n, g z < n)
    (hgf : ∀ z < n, g (f z) = z) (hfg : ∀ z < n, f (g z) = z) (Z : Nat → Bool) :
    ((range n).filter fun v => Z v = true).card =
      ((range n).filter fun z => Z (f z) = true).card := by
  symm
  apply Finset.card_nbij' f g
  · intro z hz
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hz ⊢
    exact ⟨hf z hz.1, hz.2⟩
  · intro v hv
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hv ⊢
    exact ⟨hg v hv.1, by rw [hfg v hv.1]; exact hv.2⟩
  · intro z hz
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hz
    exact hgf z hz.1
  · intro v hv
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hv
    exact hfg v hv.1

theorem orbBsK_zero (n : Nat) (S : Nat → Nat) (w k : Nat) : orbBsK n S w 0 k = k := rfl

theorem orbBsK_succ (n : Nat) (S : Nat → Nat) (w i k : Nat) :
    orbBsK n S w (i + 1) k =
      orbBsK n S w i (if k + 2 ^ i < n ∧ S (k + 2 ^ i) ≤ w then k + 2 ^ i else k) := by
  change orbBsK n S w i (Bool.rec (motive := fun _ => Nat) k (Nat.add k (pw2 i))
    (andB (Nat.blt (Nat.add k (pw2 i)) n) (Nat.ble (S (Nat.add k (pw2 i))) w))) = _
  congr 1
  simp only [pw2_eq, andB_eq, Nat.add_eq]
  by_cases h : k + 2 ^ i < n ∧ S (k + 2 ^ i) ≤ w
  · have e : (Nat.blt (k + 2 ^ i) n && Nat.ble (S (k + 2 ^ i)) w) = true := by
      rw [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
      exact h
    rw [e, ite_eq_left h]
  · have e : (Nat.blt (k + 2 ^ i) n && Nat.ble (S (k + 2 ^ i)) w) = false := by
      rw [Bool.eq_false_iff, ne_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
      exact h
    rw [e, ite_eq_right h]

theorem orbBsK_lt {n : Nat} (S : Nat → Nat) (w : Nat) :
    ∀ b k, k < n → orbBsK n S w b k < n := by
  intro b
  induction b with
  | zero => intro k hk; exact hk
  | succ b ih =>
    intro k hk
    rw [orbBsK_succ]
    apply ih
    split
    · next h => exact h.1
    · exact hk

theorem strict_of_succ {S : Nat → Nat} {n : Nat} (h : ∀ i, i + 1 < n → S i < S (i + 1)) :
    ∀ i j, i < j → j < n → S i < S j := by
  intro i j hij hjn
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact lt_trans (ih h' (by omega)) (h j hjn)
    · rw [h']
      exact h j hjn

theorem orbBsK_find {n : Nat} {S : Nat → Nat} (hS : ∀ i j, i < j → j < n → S i < S j) {j : Nat}
    (hj : j < n) : ∀ b k, k ≤ j → j < k + 2 ^ b → orbBsK n S (S j) b k = j := by
  intro b
  induction b with
  | zero => intro k h1 h2; rw [orbBsK_zero]; omega
  | succ b ih =>
    intro k h1 h2
    rw [orbBsK_succ]
    by_cases hk : k + 2 ^ b ≤ j
    · have hle : S (k + 2 ^ b) ≤ S j := by
        rcases Nat.lt_or_eq_of_le hk with h | h
        · exact le_of_lt (hS _ _ h hj)
        · rw [h]
      rw [ite_eq_left ⟨by omega, hle⟩]
      exact ih _ hk (by rw [Nat.pow_succ] at h2; omega)
    · have hne : ¬ (k + 2 ^ b < n ∧ S (k + 2 ^ b) ≤ S j) := by
        rintro ⟨h3, h4⟩
        have := hS j (k + 2 ^ b) (by omega) h3
        omega
      rw [ite_eq_right hne]
      exact ih k h1 (by omega)

theorem orbMemK_of_lt {n b : Nat} {S : Nat → Nat} (hS : ∀ i j, i < j → j < n → S i < S j)
    (hnb : n ≤ 2 ^ b) {j : Nat} (hj : j < n) : orbMemK n S b (S j) = true := by
  change Nat.beq (S (orbBsK n S (S j) b 0)) (S j) = true
  rw [orbBsK_find hS hj b 0 (Nat.zero_le _) (by omega)]
  exact Nat.beq_refl _

theorem exists_of_orbMemK {n b w : Nat} {S : Nat → Nat} (hn : 0 < n)
    (h : orbMemK n S b w = true) : ∃ j < n, S j = w :=
  ⟨orbBsK n S w b 0, orbBsK_lt S w b 0 hn, Nat.eq_of_beq_eq_true h⟩

@[expose] def allK (g : Nat → Bool) (v : Nat) : Bool :=
  g v && g (v ^^^ 2) && g (v ^^^ 4) && g (v ^^^ 6)

theorem allK_xor (g : Nat → Bool) (w : Nat) {t : Nat} (ht : t < 4) :
    allK g (w ^^^ 2 * t) = allK g w := by
  unfold allK
  interval_cases t <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.xor_zero, Nat.xor_assoc,
    Nat.reduceMul, Nat.reduceXor, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

theorem allK_and (g h : Nat → Bool) (v : Nat) :
    allK (fun w => g w && h w) v = (allK g v && allK h v) := by
  unfold allK
  simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

theorem allK_iff (g : Nat → Bool) (v : Nat) :
    allK g v = true ↔ ∀ t < 4, g (v ^^^ 2 * t) = true := by
  unfold allK
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ t ht
    interval_cases t
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  · intro h
    have h0 := h 0 (by norm_num)
    have h1 := h 1 (by norm_num)
    have h2 := h 2 (by norm_num)
    have h3 := h 3 (by norm_num)
    simp only [Nat.mul_zero, Nat.xor_zero, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3
    exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩

@[expose] noncomputable def cM (qf O : Nat → Bool) (p : Nat) : Nat :=
  if p < 2 ^ 24 ∧ allK (fun w => !qf w) p = true ∧ allK (fun w => !(w == 0)) p = true then
    cnt3 (O (p ^^^ 2)) (O (p ^^^ 4)) (O (p ^^^ 6)) else 0

@[expose] def good (qf O : Nat → Bool) (p t : Nat) : Prop :=
  p < 2 ^ 24 ∧ allK (fun w => !qf w) p = true ∧ allK (fun w => !(w == 0)) p = true ∧
    ∀ s < t, O (p ^^^ 2 * t ^^^ 2 * s) = false

instance (qf O : Nat → Bool) (p t : Nat) : Decidable (good qf O p t) := by
  unfold good
  infer_instance

theorem forall_lt_one' (P : Nat → Prop) : (∀ s < 1, P s) ↔ P 0 := by
  constructor
  · intro h
    exact h 0 (by norm_num)
  · intro h s hs
    interval_cases s
    exact h

theorem forall_lt_two' (P : Nat → Prop) : (∀ s < 2, P s) ↔ P 0 ∧ P 1 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ s hs
    interval_cases s
    · exact h0
    · exact h1

theorem forall_lt_three' (P : Nat → Prop) : (∀ s < 3, P s) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num)⟩
  · rintro ⟨h0, h1, h2⟩ s hs
    interval_cases s
    · exact h0
    · exact h1
    · exact h2

theorem cnt3_eq (a b c : Bool) :
    cnt3 a b c = (1 + (if a = false then 1 else 0) + (if b = false ∧ c = false then 1 else 0) +
      (if c = false ∧ b = false ∧ a = false then 1 else 0)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem cM_eq_sum (qf O : Nat → Bool) (p : Nat) :
    cM qf O p = ∑ t ∈ range 4, if good qf O p t then 1 else 0 := by
  unfold cM
  by_cases hc : p < 2 ^ 24 ∧ allK (fun w => !qf w) p = true ∧ allK (fun w => !(w == 0)) p = true
  · rw [ite_eq_left hc]
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, good, h1, h2, h3, true_and,
      forall_lt_one', forall_lt_two', forall_lt_three', Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true, ite_true, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.xor_zero,
      Nat.xor_assoc, Nat.reduceXor, cnt3_eq]
  · rw [ite_eq_right hc]
    have hn : ∀ t, ¬ good qf O p t := fun t h => hc ⟨h.1, h.2.1, h.2.2.1⟩
    simp [hn]

theorem census_count (qf O : Nat → Bool) (Sf : Nat → Nat) (n : Nat)
    (hO1 : ∀ w, O w = true → ∃ j < n, Sf j = w) (hO2 : ∀ j < n, O (Sf j) = true)
    (hinj : ∀ i < n, ∀ j < n, Sf i = Sf j → i = j) :
    ∑ j ∈ range n, cM qf O (Sf j) = ((range (2 ^ 24)).filter fun v =>
      (allK (fun w => !qf w) v && allK (fun w => !(w == 0)) v && !allK (fun w => !O w) v) =
        true).card := by
  simp only [cM_eq_sum]
  rw [← Finset.sum_product (f := fun x : Nat × Nat => if good qf O (Sf x.1) x.2 then 1 else 0),
    ← Finset.card_filter]
  have h6 : ∀ t < 4, 2 * t < 2 ^ 24 := fun t ht => lt_of_lt_of_le (by omega : 2 * t < 8)
    (by norm_num)
  have hnoO : ∀ j < n, allK (fun w => !O w) (Sf j) = false := by
    intro j hj
    rw [Bool.eq_false_iff, ne_eq, allK_iff]
    intro h
    have := h 0 (by norm_num)
    rw [Nat.mul_zero, Nat.xor_zero, hO2 j hj] at this
    exact Bool.noConfusion this
  have memL : ∀ x : Nat × Nat, x ∈ (range n ×ˢ range 4).filter (fun x => good qf O (Sf x.1) x.2) ↔
      (x.1 < n ∧ x.2 < 4) ∧ good qf O (Sf x.1) x.2 := by
    intro x
    rw [mem_filter, mem_product, mem_range, mem_range]
  have memR : ∀ v, v ∈ (range (2 ^ 24)).filter (fun v => (allK (fun w => !qf w) v &&
      allK (fun w => !(w == 0)) v && !allK (fun w => !O w) v) = true) ↔
      v < 2 ^ 24 ∧ (allK (fun w => !qf w) v = true ∧ allK (fun w => !(w == 0)) v = true) ∧
        allK (fun w => !O w) v = false := by
    intro v
    rw [mem_filter, mem_range, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  apply Finset.card_bij (fun x _ => Sf x.1 ^^^ 2 * x.2)
  · intro x hx
    obtain ⟨⟨hj, ht⟩, hlt, hZ, hN, _⟩ := (memL x).1 hx
    refine (memR _).2 ⟨Nat.xor_lt_two_pow hlt (h6 x.2 ht), ?_, ?_⟩
    · rw [allK_xor _ _ ht, allK_xor _ _ ht]
      exact ⟨hZ, hN⟩
    · rw [allK_xor _ _ ht]
      exact hnoO x.1 hj
  · intro x hx x' hx' heq
    have h1 := (memL x).1 hx
    have h2 := (memL x').1 hx'
    have htt : x.2 = x'.2 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := h2.2.2.2.2 x.2 h
        rw [← heq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, hO2 x.1 h1.1.1] at this
        exact Bool.noConfusion this
      · have := h1.2.2.2.2 x'.2 h
        rw [heq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, hO2 x'.1 h2.1.1] at this
        exact Bool.noConfusion this
    have e : Sf x.1 = Sf x'.1 := by
      have := congrArg (· ^^^ 2 * x.2) heq
      simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
      rw [this, htt, Nat.xor_self, Nat.xor_zero]
    exact Prod.ext (hinj x.1 h1.1.1 x'.1 h2.1.1 e) htt
  · intro v hv
    obtain ⟨hv24, ⟨hZ, hN⟩, hH⟩ := (memR v).1 hv
    have hex : ∃ t, t < 4 ∧ O (v ^^^ 2 * t) = true := by
      by_contra hno
      have : allK (fun w => !O w) v = true := (allK_iff _ _).2 fun t ht => by
        cases h : O (v ^^^ 2 * t)
        · rfl
        · exact absurd ⟨t, ht, h⟩ hno
      rw [this] at hH
      exact Bool.noConfusion hH
    classical
    have ht : Nat.find hex < 4 ∧ O (v ^^^ 2 * Nat.find hex) = true := Nat.find_spec hex
    obtain ⟨j, hj, hSj⟩ := hO1 _ ht.2
    have hmem : (j, Nat.find hex) ∈
        (range n ×ˢ range 4).filter (fun x => good qf O (Sf x.1) x.2) := by
      refine (memL _).2 ⟨⟨hj, ht.1⟩, ?_, ?_, ?_, ?_⟩
      · rw [hSj]
        exact Nat.xor_lt_two_pow hv24 (h6 _ ht.1)
      · rw [hSj, allK_xor _ _ ht.1]
        exact hZ
      · rw [hSj, allK_xor _ _ ht.1]
        exact hN
      · intro s hs
        dsimp only at hs ⊢
        rw [hSj, Nat.xor_assoc v, Nat.xor_self, Nat.xor_zero]
        have hmin := Nat.find_min hex hs
        cases h : O (v ^^^ 2 * s)
        · rfl
        · exact absurd ⟨by omega, h⟩ hmin
    refine ⟨(j, Nat.find hex), hmem, ?_⟩
    rw [hSj, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

@[expose] def lab1 (qf O : Nat → Bool) (w : Nat) : Bool := !(w == 0) && !qf w && !O w

theorem xor_eq_zero_iff' (p c : Nat) : p ^^^ c = 0 ↔ p = c := by
  constructor
  · intro h
    have := congrArg (· ^^^ c) h
    simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using this
  · intro h
    rw [h, Nat.xor_self]

theorem nz_iff (p : Nat) : allK (fun w => !(w == 0)) p = false ↔ p = 0 ∨ p = 2 ∨ p = 4 ∨ p = 6 := by
  unfold allK
  simp only [Bool.and_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq,
    xor_eq_zero_iff']
  tauto

theorem pattern_count (qf O : Nat → Bool)
    (hK : qf 0 = false ∧ qf 2 = false ∧ qf 4 = false ∧ qf 6 = false) :
    ((range (2 ^ 24)).filter fun v => allK (lab1 qf O) v = true).card + 4 +
      ((range (2 ^ 24)).filter fun v =>
        (allK (fun w => !qf w) v && allK (fun w => !(w == 0)) v && !allK (fun w => !O w) v) =
          true).card =
      ((range (2 ^ 24)).filter fun v => allK (fun w => !qf w) v = true).card := by
  set s := (range (2 ^ 24)).filter fun v => allK (fun w => !qf w) v = true
  have e1 := Finset.card_filter_add_card_filter_not (s := s)
    (fun v => allK (fun w => !(w == 0)) v = true)
  have e2 := Finset.card_filter_add_card_filter_not
    (s := s.filter fun v => allK (fun w => !(w == 0)) v = true)
    (fun v => allK (fun w => !O w) v = true)
  have hlab : ∀ v, allK (lab1 qf O) v =
      (allK (fun w => !qf w) v && allK (fun w => !(w == 0)) v && allK (fun w => !O w) v) := by
    intro v
    have : lab1 qf O = fun w => ((!(w == 0)) && !qf w) && !O w := rfl
    rw [this, allK_and, allK_and]
    simp only [Bool.and_comm, Bool.and_left_comm]
  have hA : ((range (2 ^ 24)).filter fun v => allK (lab1 qf O) v = true) =
      (s.filter fun v => allK (fun w => !(w == 0)) v = true).filter
        fun v => allK (fun w => !O w) v = true := by
    ext v
    simp only [s, mem_filter, hlab, Bool.and_eq_true, and_assoc]
  have hB : ((range (2 ^ 24)).filter fun v =>
      (allK (fun w => !qf w) v && allK (fun w => !(w == 0)) v && !allK (fun w => !O w) v) =
        true) = (s.filter fun v => allK (fun w => !(w == 0)) v = true).filter
        fun v => ¬ allK (fun w => !O w) v = true := by
    ext v
    simp only [s, mem_filter, Bool.and_eq_true, Bool.not_eq_true', and_assoc, Bool.not_eq_true]
  have hC : (s.filter fun v => ¬ allK (fun w => !(w == 0)) v = true) = {0, 2, 4, 6} := by
    ext v
    simp only [s, mem_filter, mem_range, Bool.not_eq_true, nz_iff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      obtain ⟨h0, h2, h4, h6⟩ := hK
      have hz : allK (fun w => !qf w) v = true := by
        rcases h with rfl | rfl | rfl | rfl <;>
          simp [allK, h0, h2, h4, h6]
      refine ⟨⟨?_, hz⟩, h⟩
      rcases h with rfl | rfl | rfl | rfl <;> norm_num
  rw [hC] at e1
  rw [hA, hB]
  have h4 : ({0, 2, 4, 6} : Finset Nat).card = 4 := rfl
  omega

theorem sumN_eq (n : Nat) (f : Nat → Nat) : sumN n f = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f n + sumN n f = _
    rw [ih, Finset.sum_range_succ, Nat.add_comm]

theorem basisK_spec {Q P PI MX MY : Nat} (h : basisK Q P PI MX MY = true) :
    (∀ z < 2 ^ 24, qK Q (vmF 24 P z) = hypR 12 z) ∧
    (∀ z < 2 ^ 24, vmF 24 PI (vmF 24 P z) = z) ∧ (∀ z < 2 ^ 24, vmF 24 P (vmF 24 PI z) = z) ∧
    (∀ p < 2 ^ 24, polQ Q p 2 = parF (p &&& MX)) ∧ (∀ p < 2 ^ 24, polQ Q p 4 = parF (p &&& MY)) ∧
    vmF 24 P 1 = 2 ∧ vmF 24 P 4 = 4 ∧ qK Q 2 = false ∧ qK Q 4 = false ∧ qK Q 6 = false := by
  unfold basisK at h
  simp only [andB_eq, notB_eq, beqB_eq, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    Nat.beq_eq, allN_iff, pw2_eq, land_eq] at h
  obtain ⟨hall, hP1, hP4, hq2, hq4, hq6⟩ := h
  have hq := fun i hi => (hall i hi).1
  have hpol := fun i hi => (hall i hi).2.1
  have hinv := fun i hi => (hall i hi).2.2.1
  have hinv' := fun i hi => (hall i hi).2.2.2.1
  have hmx := fun i hi => (hall i hi).2.2.2.2.1
  have hmy := fun i hi => (hall i hi).2.2.2.2.2
  have hPx : ∀ a b, vmF 24 P (a ^^^ b) = vmF 24 P a ^^^ vmF 24 P b := vmF_xor 24 P
  have hpf : ∀ a b, pol (fun z => qK Q (vmF 24 P z)) a b = polQ Q (vmF 24 P a) (vmF 24 P b) := by
    intro a b
    simp only [pol]
    rw [hPx, qK_xor]
    generalize qK Q (vmF 24 P a) = A
    generalize qK Q (vmF 24 P b) = B
    generalize polQ Q (vmF 24 P a) (vmF 24 P b) = C
    cases A <;> cases B <;> cases C <;> rfl
  have hpH : ∀ a b, pol (hypR 12) a b = polH 12 a b := by
    intro a b
    unfold pol polH
    rw [xorB_eq, xorB_eq, Bool.xor_assoc]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, hP1, hP4, hq2, hq4, hq6⟩
  · refine quad_agree (fun a c b => ?_) (hypR_pol_add 12) hq (fun i hi j hj => ?_)
    · rw [hpf, hpf, hpf, hPx, polQ_xor_left]
    · rw [hpf, hpH]
      exact hpol i hi j hj
  · exact addN_agree (f := fun z => vmF 24 PI (vmF 24 P z)) (g := id)
      (fun a b => by simp only [hPx, vmF_xor]) (fun _ _ => rfl) hinv
  · exact addN_agree (f := fun z => vmF 24 P (vmF 24 PI z)) (g := id)
      (fun a b => by simp only [hPx, vmF_xor]) (fun _ _ => rfl) hinv'
  · exact add_agree (f := fun p => polQ Q p 2) (g := fun p => parF (p &&& MX))
      (fun a b => polQ_xor_left Q a b 2)
      (fun a b => by simp only [Nat.and_xor_distrib_right, parF_xor]) hmx
  · exact add_agree (f := fun p => polQ Q p 4) (g := fun p => parF (p &&& MY))
      (fun a b => polQ_xor_left Q a b 4)
      (fun a b => by simp only [Nat.and_xor_distrib_right, parF_xor]) hmy

theorem card_singular {Q P PI MX MY : Nat} (h : basisK Q P PI MX MY = true) :
    ((range (2 ^ 24)).filter fun v => allK (fun w => !qK Q w) v = true).card = 2099200 := by
  obtain ⟨hq, hinv, hinv', -, -, hP1, hP4, -⟩ := basisK_spec h
  rw [card_filter_bij (f := vmF 24 P) (g := vmF 24 PI) (fun z _ => vmF_lt 24 P z)
    (fun z _ => vmF_lt 24 PI z) hinv hinv', ← card_hyp]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro z hz
  have hz' : z < 2 ^ 24 := mem_range.1 hz
  have hx : ∀ c, c < 16 → z ^^^ c < 2 ^ 24 := fun c hc =>
    Nat.xor_lt_two_pow hz' (lt_of_lt_of_le hc (by norm_num))
  have e2 : vmF 24 P z ^^^ 2 = vmF 24 P (z ^^^ 1) := by rw [vmF_xor, hP1]
  have e4 : vmF 24 P z ^^^ 4 = vmF 24 P (z ^^^ 4) := by rw [vmF_xor, hP4]
  have hP5 : vmF 24 P 5 = 6 := by
    have h5 : (5 : Nat) = 1 ^^^ 4 := by norm_num
    rw [h5, vmF_xor, hP1, hP4]
    norm_num
  have e6 : vmF 24 P z ^^^ 6 = vmF 24 P (z ^^^ 5) := by rw [vmF_xor, hP5]
  simp only [allK, Zc]
  rw [e2, e4, e6, hq z hz', hq _ (hx 1 (by norm_num)), hq _ (hx 4 (by norm_num)),
    hq _ (hx 5 (by norm_num))]

theorem filtK_iff {Q P PI MX MY : Nat} (h : basisK Q P PI MX MY = true) (p : Nat) :
    filtK Q MX MY p = true ↔ (p < 2 ^ 24 ∧ allK (fun w => !qK Q w) p = true ∧
      allK (fun w => !(w == 0)) p = true) := by
  obtain ⟨-, -, -, hmx, hmy, -, -, hq2, hq4, hq6⟩ := basisK_spec h
  have hblt : Nat.blt p (pw2 24) = decide (p < 2 ^ 24) := by
    rw [pw2_eq, Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]
  have hbeq : ∀ c, Nat.beq p c = decide (p = c) := fun c => by
    rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
  have hK : inKb p = decide (p = 0 ∨ p = 2 ∨ p = 4 ∨ p = 6) := by
    unfold inKb
    simp only [orB_eq, hbeq, Bool.decide_or]
  have hN : allK (fun w => !(w == 0)) p = !decide (p = 0 ∨ p = 2 ∨ p = 4 ∨ p = 6) := by
    cases hc : allK (fun w => !(w == 0)) p
    · rw [decide_eq_true ((nz_iff p).1 hc)]
      rfl
    · have h' : ¬ (p = 0 ∨ p = 2 ∨ p = 4 ∨ p = 6) := fun h' => by
        rw [(nz_iff p).2 h'] at hc
        exact Bool.noConfusion hc
      rw [decide_eq_false h']
      rfl
  have hF : filtK Q MX MY p = (decide (p < 2 ^ 24) && !parF (p &&& MX) && !parF (p &&& MY) &&
      !decide (p = 0 ∨ p = 2 ∨ p = 4 ∨ p = 6) && !qK Q p) := by
    unfold filtK
    rw [hblt, hK]
    simp only [andB_eq, notB_eq, land_eq, Bool.and_assoc]
  rw [hF, hN]
  by_cases hp : p < 2 ^ 24
  · have e2 : qK Q (p ^^^ 2) = (qK Q p ^^ parF (p &&& MX)) := by
      rw [qK_xor, hq2, hmx p hp, Bool.xor_false]
    have e4 : qK Q (p ^^^ 4) = (qK Q p ^^ parF (p &&& MY)) := by
      rw [qK_xor, hq4, hmy p hp, Bool.xor_false]
    have e6 : qK Q (p ^^^ 6) = (qK Q p ^^ (parF (p &&& MX) ^^ parF (p &&& MY))) := by
      have h6 : (6 : Nat) = 2 ^^^ 4 := by norm_num
      rw [qK_xor, hq6, h6, polQ_xor_right, hmx p hp, hmy p hp, Bool.xor_false]
    simp only [allK]
    rw [e2, e4, e6]
    generalize qK Q p = A
    generalize parF (p &&& MX) = B
    generalize parF (p &&& MY) = C
    generalize decide (p = 0 ∨ p = 2 ∨ p = 4 ∨ p = 6) = D
    rw [decide_eq_true hp]
    simp only [hp, true_and]
    cases A <;> cases B <;> cases C <;> cases D <;> decide
  · rw [decide_eq_false hp]
    simp only [Bool.false_and, Bool.false_eq_true, false_iff, not_and]
    intro h'
    exact absurd h' hp

theorem cenAt_eq {Q P PI MX MY : Nat} (h : basisK Q P PI MX MY = true) (Sf : Nat → Nat)
    (n b j : Nat) : cenAt Q MX MY Sf n b j = cM (qK Q) (orbMemK n Sf b) (Sf j) := by
  unfold cenAt cM
  rw [strictN_eq]
  by_cases hc : filtK Q MX MY (Sf j) = true
  · rw [hc, ite_eq_left ((filtK_iff h _).1 hc)]
    rfl
  · rw [Bool.not_eq_true] at hc
    rw [hc, ite_eq_right fun h' => by
      rw [(filtK_iff h _).2 h'] at hc
      exact Bool.noConfusion hc]

theorem count_of_checks {Q P PI MX MY : Nat} (h : basisK Q P PI MX MY = true) (Sf : Nat → Nat)
    {n b C : Nat} (hn : 0 < n) (hnb : n ≤ 2 ^ b) (hS : ∀ i, i + 1 < n → Sf i < Sf (i + 1))
    (hC : sumN n (cenAt Q MX MY Sf n b) = C) :
    ((range (2 ^ 24)).filter fun v => allK (lab1 (qK Q) (orbMemK n Sf b)) v = true).card + 4 +
      C = 2099200 := by
  have hS' := strict_of_succ hS
  obtain ⟨-, -, -, -, -, -, -, hq2, hq4, hq6⟩ := basisK_spec h
  have hcen := census_count (qK Q) (orbMemK n Sf b) Sf n
    (fun w hw => exists_of_orbMemK hn hw) (fun j hj => orbMemK_of_lt hS' hnb hj)
    (fun i hi j hj e => by
      rcases Nat.lt_trichotomy i j with h' | h' | h'
      · exact absurd e (ne_of_lt (hS' i j h' hj))
      · exact h'
      · exact absurd e.symm (ne_of_lt (hS' j i h' hi)))
  rw [sumN_eq] at hC
  simp only [cenAt_eq h] at hC
  rw [hC] at hcen
  rw [hcen, ← card_singular h]
  exact pattern_count (qK Q) (orbMemK n Sf b) ⟨qK_zero Q, hq2, hq4, hq6⟩

end CFSG.KC.GmsPath

end
