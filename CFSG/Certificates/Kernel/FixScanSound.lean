module

public import Certificates.Data.Kernel.FixScan
public import CFSG.Certificates.Kernel.Co1BMulSound
public import CFSG.Certificates.Kernel.Co1FixCount

public section

namespace CFSG.KC.FixScan

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KS.SporSch.VOrb
  CFSG.Sporadic.Co1.OddNative

theorem fixScanK_eq (T : Nat → Nat) (Ms : List Nat) (lo len acc : Nat) :
    fixScanK T Ms lo len acc = countBelow (fun j => allFixK Ms (ptK T (lo + j))) len acc := by
  induction len generalizing acc with
  | zero => rfl
  | succ n ih =>
    change strictN (Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
      (allFixK Ms (ptK T (Nat.add lo n)))) (fixScanK T Ms lo n) = _
    rw [CFSG.KC.F2W.strictN_eq, ih]
    change _ = countBelow _ n (if allFixK Ms (ptK T (lo + n)) then acc + 1 else acc)
    congr 1
    cases allFixK Ms (ptK T (lo + n)) <;> rfl

theorem allFixK_eq (Ms : List Nat) (x : Nat) :
    allFixK Ms x = (Ms.map (unpackR 24)).all fun Mt => isFixedN Mt x := by
  induction Ms with
  | nil => rfl
  | cons Mt Ms ih =>
    change andB (Nat.beq (vmF 24 Mt x) x) (allFixK Ms x) = _
    rw [ih, List.map_cons, List.all_cons, isFixedN, CFSG.KC.F2W.vecMulN_unpackR]
    cases h : Nat.beq (vmF 24 Mt x) x
    · have := Nat.ne_of_beq_eq_false h
      simp [andB, this]
    · have := Nat.eq_of_beq_eq_true h
      simp [andB, this]

theorem countBelow_congr {p q : Nat → Bool} {n : Nat} (h : ∀ i < n, p i = q i) (acc : Nat) :
    countBelow p n acc = countBelow q n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    change countBelow p n (if p n then acc + 1 else acc) = countBelow q n (if q n then acc + 1 else acc)
    rw [h n (Nat.lt_succ_self n), ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]

theorem countBelow_add_acc (p : Nat → Bool) (n acc : Nat) :
    countBelow p n acc = acc + countBelow p n 0 := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    change countBelow p n (if p n then acc + 1 else acc) =
      acc + countBelow p n (if p n then 0 + 1 else 0)
    rw [ih, ih (if p n then 0 + 1 else 0)]
    cases p n <;> simp
    omega

theorem countBelow_split (p : Nat → Bool) (a b acc : Nat) :
    countBelow p (a + b) acc = countBelow p a (countBelow (fun j => p (a + j)) b acc) := by
  induction b generalizing acc with
  | zero => rfl
  | succ b ih =>
    change countBelow p (a + b) (if p (a + b) then acc + 1 else acc) =
      countBelow p a (countBelow (fun j => p (a + j)) b (if p (a + b) then acc + 1 else acc))
    exact ih _

theorem countBelow_slices {p : Nat → Bool} {L NS : Nat} {C : Nat → Nat} (h0 : C 0 = 0)
    (hs : ∀ s < NS, countBelow (fun j => p (s * L + j)) L (C s) = C (s + 1)) :
    countBelow p (NS * L) 0 = C NS := by
  have key : ∀ s ≤ NS, countBelow p (s * L) 0 = C s := by
    intro s
    induction s with
    | zero =>
      intro _
      rw [Nat.zero_mul, h0]
      rfl
    | succ s ih =>
      intro hs'
      have h1 := hs s (by omega)
      rw [countBelow_add_acc] at h1
      rw [Nat.succ_mul, countBelow_split, countBelow_add_acc, ih (by omega), ← h1, Nat.add_comm]
  exact key NS le_rfl

theorem vmF_xorT (d M a b : Nat) : vmF d M (a ^^^ b) = vmF d M a ^^^ vmF d M b := by
  rw [CFSG.KC.F2W.vmF_rec, CFSG.KC.F2W.vmF_rec, CFSG.KC.F2W.vmF_rec]
  suffices h : ∀ n, (Nat.rec (motive := fun _ => Nat) 0
      (fun k acc => if (a ^^^ b).testBit k then rowF d M k ^^^ acc else acc) n : Nat) =
      (Nat.rec (motive := fun _ => Nat) 0
        (fun k acc => if a.testBit k then rowF d M k ^^^ acc else acc) n : Nat) ^^^
      (Nat.rec (motive := fun _ => Nat) 0
        (fun k acc => if b.testBit k then rowF d M k ^^^ acc else acc) n : Nat) from h d
  have hl : ∀ r A B : Nat, r ^^^ (A ^^^ B) = A ^^^ (r ^^^ B) := by
    intro r A B
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases r.testBit i <;> cases A.testBit i <;> cases B.testBit i <;> rfl
  have hc : ∀ r A B : Nat, A ^^^ B = r ^^^ A ^^^ (r ^^^ B) := by
    intro r A B
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases r.testBit i <;> cases A.testBit i <;> cases B.testBit i <;> rfl
  intro n
  induction n with
  | zero => exact (Nat.xor_self 0).symm
  | succ k ih =>
    have e : ∀ c : Nat → Bool, (Nat.rec (motive := fun _ => Nat) 0
        (fun k acc => if c k then rowF d M k ^^^ acc else acc) (k + 1) : Nat) =
        if c k then rowF d M k ^^^ (Nat.rec (motive := fun _ => Nat) 0
          (fun k acc => if c k then rowF d M k ^^^ acc else acc) k : Nat)
        else (Nat.rec (motive := fun _ => Nat) 0
          (fun k acc => if c k then rowF d M k ^^^ acc else acc) k : Nat) := fun _ => rfl
    rw [e (Nat.testBit (a ^^^ b)), e (Nat.testBit a), e (Nat.testBit b), ih, Nat.testBit_xor]
    cases a.testBit k <;> cases b.testBit k <;> simp only [Bool.false_xor, Bool.true_xor,
      Bool.not_false, Bool.false_eq_true, ↓reduceIte, Bool.xor_self] <;>
      first
      | rfl
      | exact (Nat.xor_assoc _ _ _).symm
      | exact hl _ _ _
      | exact hc _ _ _

theorem split24 {x : Nat} (hx : x < 2 ^ 24) :
    x = (x &&& 255) ^^^ ((((x >>> 8) &&& 255) <<< 8) ^^^ (((x >>> 16) &&& 255) <<< 16)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h255 : (255 : Nat) = 2 ^ 8 - 1 := rfl
  rw [h255]
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, ge_iff_le]
  by_cases h1 : i < 8
  · have a : ¬ 8 ≤ i := by omega
    have b : ¬ 16 ≤ i := by omega
    simp [h1, a, b]
  by_cases h2 : i < 16
  · have a : 8 ≤ i := by omega
    have b : ¬ 16 ≤ i := by omega
    have c : i - 8 < 8 := by omega
    have e : 8 + (i - 8) = i := by omega
    simp [h1, a, b, c, e]
  by_cases h3 : i < 24
  · have a : 8 ≤ i := by omega
    have b : 16 ≤ i := by omega
    have c : ¬ i - 8 < 8 := by omega
    have d : i - 16 < 8 := by omega
    have e : 16 + (i - 16) = i := by omega
    simp [h1, a, b, c, d, e]
  · have a : 8 ≤ i := by omega
    have b : 16 ≤ i := by omega
    have c : ¬ i - 8 < 8 := by omega
    have d : ¬ i - 16 < 8 := by omega
    have hx' : x < 2 ^ i := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))
    simp [h1, a, b, c, d, Nat.testBit_lt_two_pow hx']

theorem tabOK_sound {t o Mt : Nat} (h : tabOK t o Mt = true) :
    ∀ j < 768, fget t (o + j) 24 = vmF 24 Mt ((j % 256) <<< (8 * (j / 256))) := by
  have key : ∀ (f : Nat → Bool) (n : Nat), allN n f = true → ∀ j < n, f j = true := by
    intro f n
    induction n with
    | zero => intro _ j hj; omega
    | succ n ih =>
      intro hn j hj
      change andB (f n) (allN n f) = true at hn
      have hb : f n = true ∧ allN n f = true := by
        revert hn
        cases f n <;> cases allN n f <;> simp [andB]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · exact ih hb.2 j hj
      · rw [hj]
        exact hb.1
  intro j hj
  exact Nat.eq_of_beq_eq_true (key _ 768 h j hj)

theorem vmT_eq {t o Mt : Nat} (h : tabOK t o Mt = true) {x : Nat} (hx : x < 2 ^ 24) :
    vmT t o x = vmF 24 Mt x := by
  have b0 : x &&& 255 < 256 := Nat.lt_succ_of_le Nat.and_le_right
  have b1 : (x >>> 8) &&& 255 < 256 := Nat.lt_succ_of_le Nat.and_le_right
  have b2 : (x >>> 16) &&& 255 < 256 := Nat.lt_succ_of_le Nat.and_le_right
  have e0 := tabOK_sound h (x &&& 255) (by omega)
  have e1 := tabOK_sound h (256 + ((x >>> 8) &&& 255)) (by omega)
  have e2 := tabOK_sound h (512 + ((x >>> 16) &&& 255)) (by omega)
  have m0 : (x &&& 255) % 256 = x &&& 255 := by omega
  have d0 : 8 * ((x &&& 255) / 256) = 0 := by omega
  have m1 : (256 + ((x >>> 8) &&& 255)) % 256 = (x >>> 8) &&& 255 := by omega
  have d1 : 8 * ((256 + ((x >>> 8) &&& 255)) / 256) = 8 := by omega
  have m2 : (512 + ((x >>> 16) &&& 255)) % 256 = (x >>> 16) &&& 255 := by omega
  have d2 : 8 * ((512 + ((x >>> 16) &&& 255)) / 256) = 16 := by omega
  rw [m0, d0, Nat.shiftLeft_zero] at e0
  rw [m1, d1] at e1
  rw [m2, d2] at e2
  change fget t (o + (x &&& 255)) 24 ^^^ (fget t (o + (256 + ((x >>> 8) &&& 255))) 24 ^^^
    fget t (o + (512 + ((x >>> 16) &&& 255))) 24) = _
  rw [e0, e1, e2, ← vmF_xorT, ← vmF_xorT, ← split24 hx]

theorem ptK_lt24 (T : Nat → Nat) (k : Nat) : ptK T k < 2 ^ 24 := by
  have e : ptK T k = recK T k &&& 16777215 := rfl
  rw [e]
  exact Nat.and_lt_two_pow _ (by decide)

theorem allFixT_eq {t : Nat} {os Ms : List Nat}
    (h : List.Forall₂ (fun o Mt => tabOK t o Mt = true) os Ms) {x : Nat} (hx : x < 2 ^ 24) :
    allFixT t os x = allFixK Ms x := by
  induction h with
  | nil => rfl
  | @cons o Mt os Ms hOM _ ih =>
    change andB (Nat.beq (vmT t o x) x) (allFixT t os x) =
      andB (Nat.beq (vmF 24 Mt x) x) (allFixK Ms x)
    rw [vmT_eq hOM hx, ih]

theorem fixScanT_eq (T : Nat → Nat) {t : Nat} {os Ms : List Nat}
    (h : List.Forall₂ (fun o Mt => tabOK t o Mt = true) os Ms) (lo len acc : Nat) :
    fixScanT T t os lo len acc = fixScanK T Ms lo len acc := by
  induction len generalizing acc with
  | zero => rfl
  | succ n ih =>
    change strictN (Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
      (allFixT t os (ptK T (Nat.add lo n)))) (fixScanT T t os lo n) =
      strictN (Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
      (allFixK Ms (ptK T (Nat.add lo n)))) (fixScanK T Ms lo n)
    rw [allFixT_eq h (ptK_lt24 T _), CFSG.KC.F2W.strictN_eq, CFSG.KC.F2W.strictN_eq, ih]

theorem fqXor_eq (a b : Bool) : fqXor a b = (a ^^ b) := by
  cases a <;> cases b <;> rfl

theorem dotK_succT (d x y : Nat) :
    dotK (d + 1) x y = (dotK d x y ^^ (x.testBit d && y.testBit d)) := by
  change Bool.rec (motive := fun _ => Bool) (dotK d x y) (notB (dotK d x y))
    (andB (bit x d) (bit y d)) = _
  rw [CFSG.KC.Co1Fix.bit_eq', CFSG.KC.Co1Fix.bit_eq']
  cases x.testBit d <;> cases y.testBit d <;> cases dotK d x y <;> rfl

theorem dotK_xorL (a b y : Nat) : ∀ d, dotK d (a ^^^ b) y = (dotK d a y ^^ dotK d b y)
  | 0 => rfl
  | d + 1 => by
    rw [dotK_succT, dotK_succT, dotK_succT, dotK_xorL a b y d, Nat.testBit_xor]
    cases a.testBit d <;> cases b.testBit d <;> cases y.testBit d <;> cases dotK d a y <;>
      cases dotK d b y <;> rfl

theorem dotK_xorR (x a b : Nat) : ∀ d, dotK d x (a ^^^ b) = (dotK d x a ^^ dotK d x b)
  | 0 => rfl
  | d + 1 => by
    rw [dotK_succT, dotK_succT, dotK_succT, dotK_xorR x a b d, Nat.testBit_xor]
    cases a.testBit d <;> cases b.testBit d <;> cases x.testBit d <;> cases dotK d x a <;>
      cases dotK d x b <;> rfl

theorem dotK_zeroL (y : Nat) : ∀ d, dotK d 0 y = false
  | 0 => rfl
  | d + 1 => by
    rw [dotK_succT, dotK_zeroL y d, Nat.zero_testBit]
    rfl

theorem dotK_zeroR (x : Nat) : ∀ d, dotK d x 0 = false
  | 0 => rfl
  | d + 1 => by
    rw [dotK_succT, dotK_zeroR x d, Nat.zero_testBit]
    cases x.testBit d <;> rfl

theorem vmF_zeroT (d M : Nat) : vmF d M 0 = 0 := by
  have h := vmF_xorT d M 0 0
  rw [Nat.xor_self, Nat.xor_self] at h
  exact h

theorem fqVal_xor (Qt a b : Nat) :
    fqVal Qt (a ^^^ b) = (fqVal Qt a ^^ fqVal Qt b ^^ fqPol Qt a b) := by
  have e : ∀ p q r s : Bool, ((p ^^ q) ^^ (r ^^ s)) = ((p ^^ s) ^^ (q ^^ r)) := by decide
  unfold fqVal fqPol vecK
  rw [vmF_xorT, dotK_xorL, dotK_xorR, dotK_xorR, fqXor_eq]
  exact e _ _ _ _

theorem fqPol_xorL (Qt a b y : Nat) : fqPol Qt (a ^^^ b) y = (fqPol Qt a y ^^ fqPol Qt b y) := by
  have e : ∀ p q r s : Bool, ((p ^^ q) ^^ (r ^^ s)) = ((p ^^ r) ^^ (q ^^ s)) := by decide
  unfold fqPol vecK
  rw [dotK_xorL, vmF_xorT, dotK_xorR]
  simp only [fqXor_eq]
  exact e _ _ _ _

theorem fqVal_zero (Qt : Nat) : fqVal Qt 0 = false := by
  unfold fqVal
  exact dotK_zeroL _ _

theorem fqPol_zeroL (Qt y : Nat) : fqPol Qt 0 y = false := by
  unfold fqPol vecK
  rw [vmF_zeroT, dotK_zeroL, dotK_zeroR]
  rfl

theorem testBit_bitQ_zero (c : Bool) (r : Nat) :
    (Bool.rec (motive := fun _ => Nat) 0 1 c + 2 * r).testBit 0 = c := by
  cases c <;> simp [Nat.testBit_zero]

theorem testBit_bitQ_succ (c : Bool) (r j : Nat) :
    (Bool.rec (motive := fun _ => Nat) 0 1 c + 2 * r).testBit (j + 1) = r.testBit j := by
  rw [Nat.testBit_succ]
  congr 1
  cases c <;> simp only <;> omega

theorem fqRow_bit (Qt f : Nat) : ∀ (G : List Nat) (j : Nat) (h : j < G.length),
    (fqRow Qt f G).testBit j = fqPol Qt f G[j]
  | g :: G, 0, _ => testBit_bitQ_zero _ (fqRow Qt f G)
  | g :: G, j + 1, h =>
    (testBit_bitQ_succ _ (fqRow Qt f G) j).trans (fqRow_bit Qt f G j (by simp at h; omega))

theorem fqCount_cons (m : Nat) (E : List Nat) (qa : Bool) (l : Nat) :
    fqCount (m :: E) qa l = fqCount E qa (l >>> 1) +
      fqCount E (fqXor qa (bit (l ^^^ m) 0)) ((l ^^^ m) >>> 1) := by
  change strictN (fqCount E qa (l >>> 1)) (fun a => strictN
    (fqCount E (fqXor qa (bit (l ^^^ m) 0)) ((l ^^^ m) >>> 1)) fun b => Nat.add a b) = _
  rw [CFSG.KC.F2W.strictN_eq, CFSG.KC.F2W.strictN_eq]
  rfl

theorem fqCount_eq (Qt : Nat) : ∀ (F : List Nat) (acc : Nat) (l : Nat),
    (∀ j (h : j < F.length), l.testBit j = fqPol Qt acc F[j]) →
      fqCount (fqGram Qt F) (fqVal Qt acc) l = qCountK 24 Qt F acc
  | [], _, _, _ => rfl
  | f :: G, acc, l, hl => by
    have e3 : ∀ p q r : Bool, (p ^^ (q ^^ r)) = ((p ^^ r) ^^ q) := by decide
    have hm0 := testBit_bitQ_zero (fqVal Qt f) (fqRow Qt f G)
    have h1 : ∀ j (h : j < G.length), (l >>> 1).testBit j = fqPol Qt acc G[j] := by
      intro j h
      rw [Nat.testBit_shiftRight, Nat.add_comm]
      exact hl (j + 1) (by simp; omega)
    have h2 : fqXor (fqVal Qt acc) (bit (l ^^^ (Bool.rec (motive := fun _ => Nat) 0 1 (fqVal Qt f) +
        2 * fqRow Qt f G)) 0) = fqVal Qt (acc ^^^ f) := by
      rw [CFSG.KC.Co1Fix.bit_eq', Nat.testBit_xor, hm0, hl 0 (by simp), fqXor_eq, fqVal_xor]
      exact e3 _ _ _
    have h3 : ∀ j (h : j < G.length), ((l ^^^ (Bool.rec (motive := fun _ => Nat) 0 1 (fqVal Qt f) +
        2 * fqRow Qt f G)) >>> 1).testBit j = fqPol Qt (acc ^^^ f) G[j] := by
      intro j h
      rw [Nat.testBit_shiftRight, Nat.testBit_xor, Nat.add_comm, testBit_bitQ_succ,
        fqRow_bit Qt f G j h, hl (j + 1) (by simp; omega), fqPol_xorL]
      rfl
    change fqCount ((Bool.rec (motive := fun _ => Nat) 0 1 (fqVal Qt f) + 2 * fqRow Qt f G) ::
      fqGram Qt G) (fqVal Qt acc) l = _
    rw [fqCount_cons, CFSG.KC.Co1Fix.qCountK_cons, fqCount_eq Qt G acc _ h1, h2,
      fqCount_eq Qt G (acc ^^^ f) _ h3]

theorem qCountK_fqGram (Qt : Nat) (F : List Nat) :
    qCountK 24 Qt F 0 = fqCount (fqGram Qt F) false 0 := by
  rw [← fqVal_zero Qt]
  exact (fqCount_eq Qt F 0 0 fun j _ => by rw [Nat.zero_testBit, fqPol_zeroL]).symm

theorem fixK_of_fixKQ {Mt Qt k a b : Nat} {F Y : List Nat} (h : fixKQ 24 Mt Qt F Y k a b = true) :
    fixK 24 Mt Qt F Y k a b = true := by
  unfold fixKQ at h
  unfold fixK
  rw [qCountK_fqGram]
  exact h

end CFSG.KC.FixScan

end
