module

public import Certificates.Data.Kernel.Spor.ONKW
public import CFSG.Certificates.Kernel.Spor.ONVecLib
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option exponentiation.threshold 600

namespace CFSG.KS.ONW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

def encF : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => 2 ^ 512 * encF n (fun i => f (i + 1)) + f 0

theorem op_lt {op : Nat → Nat → Nat} {g : Bool → Bool → Bool} (hg : g false false = false)
    (hop : ∀ a b k, (op a b).testBit k = g (a.testBit k) (b.testBit k)) {a b : Nat}
    (ha : a < 2 ^ 512) (hb : b < 2 ^ 512) : op a b < 2 ^ 512 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [hop, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hi)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hi)), hg]

theorem split_op {op : Nat → Nat → Nat} {g : Bool → Bool → Bool} (hg : g false false = false)
    (hop : ∀ a b k, (op a b).testBit k = g (a.testBit k) (b.testBit k)) {a b : Nat}
    (ha : a < 2 ^ 512) (hb : b < 2 ^ 512) (x y : Nat) :
    op (2 ^ 512 * x + a) (2 ^ 512 * y + b) = 2 ^ 512 * op x y + op a b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [hop, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ (op_lt hg hop ha hb)]
  split <;> simp [hop]

theorem enc_op {op : Nat → Nat → Nat} {g : Bool → Bool → Bool} (hg : g false false = false)
    (hop : ∀ a b k, (op a b).testBit k = g (a.testBit k) (b.testBit k)) :
    ∀ (n : Nat) (f h : Nat → Nat), (∀ i < n, f i < 2 ^ 512) → (∀ i < n, h i < 2 ^ 512) →
      op (encF n f) (encF n h) = encF n (fun i => op (f i) (h i))
  | 0, _, _, _, _ => by
    apply Nat.eq_of_testBit_eq
    intro k
    simp [encF, hop, hg]
  | n + 1, f, h, hf, hh => by
    simp only [encF]
    rw [split_op hg hop (hf 0 (by omega)) (hh 0 (by omega)),
      enc_op hg hop n _ _ (fun i hi => hf _ (by omega)) (fun i hi => hh _ (by omega))]

theorem enc_mul : ∀ (n : Nat) (f : Nat → Nat) (c : Nat), encF n f * c = encF n (fun i => f i * c)
  | 0, _, _ => by simp [encF]
  | n + 1, f, c => by
    simp only [encF]
    rw [Nat.add_mul, Nat.mul_assoc, enc_mul n _ c]

theorem enc_zero : ∀ n : Nat, encF n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by rw [encF, enc_zero n, Nat.mul_zero]

theorem enc_congr : ∀ (n : Nat) (f h : Nat → Nat), (∀ i < n, f i = h i) → encF n f = encF n h
  | 0, _, _, _ => rfl
  | n + 1, f, h, e => by
    simp only [encF]
    rw [enc_congr n (fun i => f (i + 1)) (fun i => h (i + 1)) (fun i hi => e _ (by omega)),
      e 0 (by omega)]

theorem allBlk_of {b : Nat} {f : Nat → Bool} : ∀ {len : Nat}, (∀ l < len, f (b + l) = true) →
    allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    exact (bAnd_iff _ _).2 ⟨h len (by omega), allBlk_of fun l hl => h l (by omega)⟩

theorem split_sel {M j : Nat} (hM : M < 2 ^ (512 - j)) {a : Nat} (ha : a < 2 ^ 512) (x E : Nat) :
    ((2 ^ 512 * x + a) >>> j) &&& (2 ^ 512 * E + M) =
      2 ^ 512 * ((x >>> j) &&& E) + ((a >>> j) &&& M) := by
  have hM' : M < 2 ^ 512 := Nat.lt_of_lt_of_le hM (Nat.pow_le_pow_right (by omega) (by omega))
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_mul_add _ ha,
    Nat.testBit_two_pow_mul_add _ hM', Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hM')]
  by_cases hk : k < 512
  · rw [if_pos hk, if_pos hk, Nat.testBit_and, Nat.testBit_shiftRight]
    by_cases hjk : j + k < 512
    · rw [if_pos hjk]
    · rw [if_neg hjk, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hM
        (Nat.pow_le_pow_right (by omega) (by omega))), Bool.and_false, Bool.and_false]
  · rw [if_neg hk, if_neg hk, if_neg (by omega), Nat.testBit_and, Nat.testBit_shiftRight,
      show j + k - 512 = j + (k - 512) by omega]

theorem enc_sel {M j : Nat} (hM : M < 2 ^ (512 - j)) :
    ∀ (n : Nat) (f : Nat → Nat), (∀ i < n, f i < 2 ^ 512) →
      (encF n f >>> j) &&& encF n (fun _ => M) = encF n (fun i => (f i >>> j) &&& M)
  | 0, _, _ => by simp [encF]
  | n + 1, f, hf => by
    simp only [encF]
    rw [split_sel hM (hf 0 (by omega)), enc_sel hM n _ (fun i hi => hf _ (by omega))]

theorem enc_inj : ∀ (n : Nat) (f h : Nat → Nat), (∀ i < n, f i < 2 ^ 512) → (∀ i < n, h i < 2 ^ 512) →
    encF n f = encF n h → ∀ i < n, f i = h i
  | 0, _, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, f, h, hf, hh, e, i, hi => by
    simp only [encF] at e
    have h0 : f 0 = h 0 := by
      have := congrArg (· % 2 ^ 512) e
      simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt (hf 0 (by omega)),
        Nat.mod_eq_of_lt (hh 0 (by omega))] at this
      exact this
    rw [h0] at e
    have e' := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos 512) (Nat.add_right_cancel e)
    rcases i with _ | i
    · exact h0
    · exact enc_inj n _ _ (fun i hi => hf _ (by omega)) (fun i hi => hh _ (by omega)) e' i (by omega)

theorem enc_top : ∀ (n : Nat) (f : Nat → Nat), encF (n + 1) f = encF n f + 2 ^ (512 * n) * f n
  | 0, f => by simp [encF]
  | n + 1, f => by
    rw [encF, enc_top n (fun i => f (i + 1)), encF]
    rw [show 512 * (n + 1) = 512 + 512 * n by omega, Nat.pow_add]
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega

theorem rep_eq (M : Nat) : ∀ n : Nat, rep M n = encF n (fun _ => M)
  | 0 => rfl
  | n + 1 => by
    change Nat.add M (Nat.shiftLeft (rep M n) 512) = _
    rw [rep_eq M n, PackFld.shl_eq, encF]
    simp only [Nat.add_eq]
    rw [Nat.mul_comm, Nat.add_comm]

@[expose] def Bd (n : Nat) (f : Nat → Nat) : Prop := ∀ i < n, f i < 2 ^ 512

theorem hop_and (a b k : Nat) : (Nat.land a b).testBit k = (a.testBit k && b.testBit k) :=
  Nat.testBit_and a b k

theorem hop_or (a b k : Nat) : (Nat.lor a b).testBit k = (a.testBit k || b.testBit k) :=
  Nat.testBit_or a b k

theorem hop_xor (a b k : Nat) : (Nat.xor a b).testBit k = (a.testBit k ^^ b.testBit k) :=
  Nat.testBit_xor a b k

theorem enc_and {n : Nat} {f h : Nat → Nat} (hf : Bd n f) (hh : Bd n h) :
    Nat.land (encF n f) (encF n h) = encF n (fun i => Nat.land (f i) (h i)) :=
  enc_op (g := fun x y => x && y) rfl hop_and n f h hf hh

theorem enc_or {n : Nat} {f h : Nat → Nat} (hf : Bd n f) (hh : Bd n h) :
    Nat.lor (encF n f) (encF n h) = encF n (fun i => Nat.lor (f i) (h i)) :=
  enc_op (g := fun x y => x || y) rfl hop_or n f h hf hh

theorem enc_xor {n : Nat} {f h : Nat → Nat} (hf : Bd n f) (hh : Bd n h) :
    Nat.xor (encF n f) (encF n h) = encF n (fun i => Nat.xor (f i) (h i)) :=
  enc_op (g := fun x y => x ^^ y) rfl hop_xor n f h hf hh

theorem Bd.and {n : Nat} {f h : Nat → Nat} (hf : Bd n f) (hh : Bd n h) :
    Bd n (fun i => Nat.land (f i) (h i)) := fun i hi =>
  op_lt (g := fun x y => x && y) rfl hop_and (hf i hi) (hh i hi)

theorem Bd.or {n : Nat} {f h : Nat → Nat} (hf : Bd n f) (hh : Bd n h) :
    Bd n (fun i => Nat.lor (f i) (h i)) := fun i hi =>
  op_lt (g := fun x y => x || y) rfl hop_or (hf i hi) (hh i hi)

theorem Bd.xor {n : Nat} {f h : Nat → Nat} (hf : Bd n f) (hh : Bd n h) :
    Bd n (fun i => Nat.xor (f i) (h i)) := fun i hi =>
  op_lt (g := fun x y => x ^^ y) rfl hop_xor (hf i hi) (hh i hi)

theorem enc_addP {n : Nat} {a b c d : Nat → Nat} (ha : Bd n a) (hb : Bd n b) (hc : Bd n c)
    (hd : Bd n d) : addP (encF n a) (encF n b) (encF n c) (encF n d) =
      encF n (fun i => addP (a i) (b i) (c i) (d i)) := by
  unfold addP
  rw [enc_or hc hd, enc_and ha (hc.or hd), enc_xor ha (ha.and (hc.or hd)), enc_or ha hb,
    enc_and hc (ha.or hb), enc_xor hc (hc.and (ha.or hb)),
    enc_or (ha.xor (ha.and (hc.or hd))) (hc.xor (hc.and (ha.or hb))), enc_and hb hd,
    enc_or ((ha.xor (ha.and (hc.or hd))).or (hc.xor (hc.and (ha.or hb)))) (hb.and hd)]

theorem Bd.addP {n : Nat} {a b c d : Nat → Nat} (ha : Bd n a) (hb : Bd n b) (hc : Bd n c)
    (hd : Bd n d) : Bd n (fun i => addP (a i) (b i) (c i) (d i)) :=
  ((ha.xor (ha.and (hc.or hd))).or (hc.xor (hc.and (ha.or hb)))).or (hb.and hd)

theorem enc_addM {n : Nat} {a b c d : Nat → Nat} (ha : Bd n a) (hb : Bd n b) (hc : Bd n c)
    (hd : Bd n d) : addM (encF n a) (encF n b) (encF n c) (encF n d) =
      encF n (fun i => addM (a i) (b i) (c i) (d i)) := by
  unfold addM
  rw [enc_or hc hd, enc_and hb (hc.or hd), enc_xor hb (hb.and (hc.or hd)), enc_or ha hb,
    enc_and hd (ha.or hb), enc_xor hd (hd.and (ha.or hb)),
    enc_or (hb.xor (hb.and (hc.or hd))) (hd.xor (hd.and (ha.or hb))), enc_and ha hc,
    enc_or ((hb.xor (hb.and (hc.or hd))).or (hd.xor (hd.and (ha.or hb)))) (ha.and hc)]

theorem Bd.addM {n : Nat} {a b c d : Nat → Nat} (ha : Bd n a) (hb : Bd n b) (hc : Bd n c)
    (hd : Bd n d) : Bd n (fun i => addM (a i) (b i) (c i) (d i)) :=
  ((hb.xor (hb.and (hc.or hd))).or (hd.xor (hd.and (ha.or hb)))).or (ha.and hc)

private theorem nIfE (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem land_one_beq (y : Nat) : Nat.beq (Nat.land y 1) 1 = y.testBit 0 := by
  change Nat.beq (y &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> rw [h] <;> rfl

theorem mvL_cons (c : Nat) (L : List Nat) (xp xm ap am : Nat) : mvL (c :: L) xp xm ap am =
    if xp.testBit 0 = true then
      mvL L (xp >>> 1) (xm >>> 1) (addP ap am (vP c) (vM c)) (addM ap am (vP c) (vM c))
    else if xm.testBit 0 = true then
      mvL L (xp >>> 1) (xm >>> 1) (addP ap am (vM c) (vP c)) (addM ap am (vM c) (vP c))
    else mvL L (xp >>> 1) (xm >>> 1) ap am := by
  have e : mvL (c :: L) xp xm ap am = strictN (vP c) fun cp => strictN (vM c) fun cm =>
      nIf(Nat.beq (Nat.land xp (nat_lit 1)) (nat_lit 1),
        strictN (addP ap am cp cm) fun ap' => strictN (addM ap am cp cm) fun am' =>
          mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap' am',
        nIf(Nat.beq (Nat.land xm (nat_lit 1)) (nat_lit 1),
          strictN (addP ap am cm cp) fun ap' => strictN (addM ap am cm cp) fun am' =>
            mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap' am',
          mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap am)) := rfl
  rw [e]
  simp only [PackFld.strictN_eqP, nIfE, land_one_beq]
  rfl

theorem addP_zero (ap am : Nat) : addP ap am 0 0 = ap := by
  unfold addP
  apply Nat.eq_of_testBit_eq
  intro k
  change ((ap ^^^ (ap &&& (0 ||| 0))) ||| (0 ^^^ (0 &&& (ap ||| am))) ||| (am &&& 0)).testBit k = _
  simp

theorem addM_zero (ap am : Nat) : addM ap am 0 0 = am := by
  unfold addM
  apply Nat.eq_of_testBit_eq
  intro k
  change ((am ^^^ (am &&& (0 ||| 0))) ||| (0 ^^^ (0 &&& (ap ||| am))) ||| (ap &&& 0)).testBit k = _
  simp

theorem step_field {L : List Nat} {xp xm j c ap am : Nat} (hd : xp &&& xm = 0) :
    (if (xp >>> j).testBit 0 = true then
      mvL L ((xp >>> j) >>> 1) ((xm >>> j) >>> 1) (addP ap am (vP c) (vM c)) (addM ap am (vP c) (vM c))
    else if (xm >>> j).testBit 0 = true then
      mvL L ((xp >>> j) >>> 1) ((xm >>> j) >>> 1) (addP ap am (vM c) (vP c)) (addM ap am (vM c) (vP c))
    else mvL L ((xp >>> j) >>> 1) ((xm >>> j) >>> 1) ap am) =
    mvL L (xp >>> (j + 1)) (xm >>> (j + 1))
      (addP ap am (Nat.lor (Nat.land (xp >>> j) 1 * vP c) (Nat.land (xm >>> j) 1 * vM c))
        (Nat.lor (Nat.land (xp >>> j) 1 * vM c) (Nat.land (xm >>> j) 1 * vP c)))
      (addM ap am (Nat.lor (Nat.land (xp >>> j) 1 * vP c) (Nat.land (xm >>> j) 1 * vM c))
        (Nat.lor (Nat.land (xp >>> j) 1 * vM c) (Nat.land (xm >>> j) 1 * vP c))) := by
  have hb : ∀ y, Nat.land (y >>> j) 1 = if (y >>> j).testBit 0 = true then 1 else 0 := by
    intro y
    change (y >>> j) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one (y >>> j) with h | h <;> simp [h]
  have hdj : ¬ ((xp >>> j).testBit 0 = true ∧ (xm >>> j).testBit 0 = true) := by
    intro ⟨h1, h2⟩
    have := congrArg (fun z => z.testBit j) hd
    simp only [Nat.testBit_and, Nat.zero_testBit] at this
    rw [Nat.testBit_shiftRight] at h1 h2
    simp_all
  simp only [Nat.shiftRight_add, hb]
  have e1 : ∀ a b : Nat, Nat.lor a 0 = a := fun a b => Nat.or_zero a
  by_cases h1 : (xp >>> j).testBit 0 = true
  · have h2 : (xm >>> j).testBit 0 = false := by simpa [h1] using hdj
    simp only [h1, h2, if_true, Bool.false_eq_true, if_false, Nat.one_mul, Nat.zero_mul]
    change _ = mvL L _ _ (addP ap am (vP c ||| 0) (vM c ||| 0)) (addM ap am (vP c ||| 0) (vM c ||| 0))
    simp only [Nat.or_zero]
  · by_cases h2 : (xm >>> j).testBit 0 = true
    · simp only [h1, h2, if_true, Bool.false_eq_true, if_false, Nat.one_mul, Nat.zero_mul]
      change _ = mvL L _ _ (addP ap am (0 ||| vM c) (0 ||| vP c)) (addM ap am (0 ||| vM c) (0 ||| vP c))
      simp only [Nat.zero_or]
    · simp only [h1, h2, Bool.false_eq_true, if_false, Nat.zero_mul]
      change _ = mvL L _ _ (addP ap am (0 ||| 0) (0 ||| 0)) (addM ap am (0 ||| 0) (0 ||| 0))
      simp only [Nat.zero_or, addP_zero, addM_zero]

theorem lt512_of_lt256 {x : Nat} (h : x < 2 ^ 256) : x < 2 ^ 512 :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega))

theorem sel_le (y j : Nat) : Nat.land (y >>> j) 1 ≤ 1 := by
  change (y >>> j) &&& 1 ≤ 1
  rw [Nat.and_one_is_mod]
  have := Nat.mod_lt (y >>> j) (by omega : 2 > 0)
  omega

theorem sel_mul_lt (y j : Nat) {c : Nat} (hc : c < 2 ^ 512) : Nat.land (y >>> j) 1 * c < 2 ^ 512 :=
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul_right c (sel_le y j)) (by omega)) hc

theorem vP_lt (c : Nat) : vP c < 2 ^ 256 := by
  change c &&& mask 256 < 2 ^ 256
  rw [PackFld.mask_eq]
  exact Nat.and_lt_two_pow _ (by omega)

theorem vM_lt {c : Nat} (h : c < 2 ^ 512) : vM c < 2 ^ 256 := by
  change c >>> 256 < 2 ^ 256
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact h)

theorem wmvL_spec {n : Nat} {xp xm gp gm : Nat → Nat} (hxp : Bd n xp) (hxm : Bd n xm)
    (hgp : Bd n gp) (hgm : Bd n gm) (hd : ∀ i < n, xp i &&& xm i = 0) :
    ∀ (L : List Nat) (j : Nat) (ap am : Nat → Nat), Bd n ap → Bd n am →
      wmvL (encF n (fun _ => 1)) (encF n xp) (encF n xm) (encF n gp) (encF n gm) L j
        (encF n ap) (encF n am) = true →
      ∀ i < n, mvL L (xp i >>> j) (xm i >>> j) (ap i) (am i) = vmk (gp i) (gm i)
  | [], j, ap, am, hap, ham, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false (Nat.beq (encF n am) (encF n gm))
      (Nat.beq (encF n ap) (encF n gp)) = true at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rw [enc_inj n _ _ hap hgp (Nat.eq_of_beq_eq_true h1) i hi,
      enc_inj n _ _ ham hgm (Nat.eq_of_beq_eq_true h2) i hi]
    rfl
  | c :: L, j, ap, am, hap, ham, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (strictB (vP c) fun cp => strictB (vM c) fun cm =>
        strictB (selW (encF n xp) (encF n (fun _ => 1)) j) fun sp =>
        strictB (selW (encF n xm) (encF n (fun _ => 1)) j) fun sm =>
        strictB (Nat.lor (Nat.mul sp cp) (Nat.mul sm cm)) fun tp =>
        strictB (Nat.lor (Nat.mul sp cm) (Nat.mul sm cp)) fun tm =>
        strictB (addP (encF n ap) (encF n am) tp tm) fun ap' =>
        strictB (addM (encF n ap) (encF n am) tp tm) fun am' =>
          wmvL (encF n (fun _ => 1)) (encF n xp) (encF n xm) (encF n gp) (encF n gm) L
            (Nat.succ j) ap' am')
      (Nat.blt j 512)) (Nat.blt c (Nat.shiftLeft 1 512)) = true at h
    obtain ⟨hc, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hj, h⟩ := (bAnd_iff _ _).1 h
    have hc : c < 2 ^ 512 := by
      have := Nat.blt_eq.mp hc
      rwa [PackFld.shl_eq, Nat.one_mul] at this
    have hj : j < 512 := Nat.blt_eq.mp hj
    simp only [PackFld.strictB_eqP] at h
    have h1 : (1 : Nat) < 2 ^ (512 - j) := Nat.one_lt_two_pow (by omega)
    have esp : selW (encF n xp) (encF n (fun _ => 1)) j = encF n (fun i => Nat.land (xp i >>> j) 1) :=
      enc_sel h1 n xp hxp
    have esm : selW (encF n xm) (encF n (fun _ => 1)) j = encF n (fun i => Nat.land (xm i >>> j) 1) :=
      enc_sel h1 n xm hxm
    rw [esp, esm] at h
    have hcp : vP c < 2 ^ 512 := lt512_of_lt256 (vP_lt c)
    have hcm : vM c < 2 ^ 512 := lt512_of_lt256 (vM_lt hc)
    have b1 : Bd n (fun i => Nat.land (xp i >>> j) 1 * vP c) := fun i _ => sel_mul_lt _ _ hcp
    have b2 : Bd n (fun i => Nat.land (xm i >>> j) 1 * vM c) := fun i _ => sel_mul_lt _ _ hcm
    have b3 : Bd n (fun i => Nat.land (xp i >>> j) 1 * vM c) := fun i _ => sel_mul_lt _ _ hcm
    have b4 : Bd n (fun i => Nat.land (xm i >>> j) 1 * vP c) := fun i _ => sel_mul_lt _ _ hcp
    have etp : Nat.lor (Nat.mul (encF n (fun i => Nat.land (xp i >>> j) 1)) (vP c))
        (Nat.mul (encF n (fun i => Nat.land (xm i >>> j) 1)) (vM c)) =
        encF n (fun i => Nat.lor (Nat.land (xp i >>> j) 1 * vP c) (Nat.land (xm i >>> j) 1 * vM c)) := by
      rw [Nat.mul_eq, Nat.mul_eq, enc_mul, enc_mul, enc_or b1 b2]
    have etm : Nat.lor (Nat.mul (encF n (fun i => Nat.land (xp i >>> j) 1)) (vM c))
        (Nat.mul (encF n (fun i => Nat.land (xm i >>> j) 1)) (vP c)) =
        encF n (fun i => Nat.lor (Nat.land (xp i >>> j) 1 * vM c) (Nat.land (xm i >>> j) 1 * vP c)) := by
      rw [Nat.mul_eq, Nat.mul_eq, enc_mul, enc_mul, enc_or b3 b4]
    rw [etp, etm, enc_addP hap ham (b1.or b2) (b3.or b4), enc_addM hap ham (b1.or b2) (b3.or b4)] at h
    have ih := wmvL_spec hxp hxm hgp hgm hd L (Nat.succ j) _ _ (hap.addP ham (b1.or b2) (b3.or b4))
      (hap.addM ham (b1.or b2) (b3.or b4)) h i hi
    rw [mvL_cons, step_field (hd i hi)]
    exact ih

theorem lo_eq : mask 256 < 2 ^ (512 - 0) ∧ mask 256 < 2 ^ (512 - 256) := by
  rw [PackFld.mask_eq]
  constructor <;> omega

theorem field_lo (x : Nat) : (x >>> 0) &&& mask 256 = vP x := by
  rw [Nat.shiftRight_zero]
  rfl

theorem field_hi {x : Nat} (h : x < 2 ^ 512) : (x >>> 256) &&& mask 256 = vM x := by
  have e : vM x = x >>> 256 := rfl
  rw [e, PackFld.mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (a := x >>> 256) (vM_lt h)]

theorem finW_spec {LA LB : List Nat} {cnt : Nat} {fK fA fB : Nat → Nat} (hK : Bd cnt fK)
    (hA : Bd cnt fA) (hB : Bd cnt fB) (hc : ∀ i < cnt, canon (fK i) = true)
    (h : finW LA LB cnt (encF cnt fK) (encF cnt fA) (encF cnt fB) = true) :
    ∀ i < cnt, mv LA (fK i) = fA i ∧ mv LB (fK i) = fB i := by
  unfold finW at h
  simp only [PackFld.strictB_eqP, rep_eq] at h
  have hP : ∀ {f : Nat → Nat}, Bd cnt f →
      Nat.land (encF cnt f) (encF cnt (fun _ => mask 256)) = encF cnt (fun i => vP (f i)) := by
    intro f hf
    have := enc_sel lo_eq.1 cnt f hf
    rw [Nat.shiftRight_zero] at this
    change (encF cnt f &&& encF cnt (fun _ => mask 256)) = _
    rw [this]
    simp only [Nat.shiftRight_zero]
    rfl
  have hM : ∀ {f : Nat → Nat}, Bd cnt f →
      Nat.land (Nat.shiftRight (encF cnt f) 256) (encF cnt (fun _ => mask 256)) =
        encF cnt (fun i => vM (f i)) := by
    intro f hf
    have := enc_sel lo_eq.2 cnt f hf
    change (encF cnt f >>> 256) &&& encF cnt (fun _ => mask 256) = _
    rw [this]
    exact enc_congr cnt _ _ fun i hi => field_hi (hf i hi)
  rw [hP hK, hM hK, hP hA, hM hA, hP hB, hM hB] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have bP : ∀ {f : Nat → Nat}, Bd cnt (fun i => vP (f i)) := fun _ _ => lt512_of_lt256 (vP_lt _)
  have bM : ∀ {f : Nat → Nat}, Bd cnt f → Bd cnt (fun i => vM (f i)) :=
    fun hf i hi => lt512_of_lt256 (vM_lt (hf i hi))
  have hd : ∀ i < cnt, vP (fK i) &&& vM (fK i) = 0 := fun i hi => (canon_bits (hc i hi)).1
  have b0 : Bd cnt (fun _ => 0) := fun _ _ => Nat.two_pow_pos 512
  have sA := wmvL_spec bP (bM hK) bP (bM hA) hd LA 0 _ _ b0 b0 (by rw [enc_zero]; exact h1)
  have sB := wmvL_spec bP (bM hK) bP (bM hB) hd LB 0 _ _ b0 b0 (by rw [enc_zero]; exact h2)
  intro i hi
  have e : ∀ L, mv L (fK i) = mvL L (vP (fK i) >>> 0) (vM (fK i) >>> 0) 0 0 := by
    intro L
    simp only [mv, PackFld.strictN_eqP, Nat.shiftRight_zero]
  rw [e, e, sA i hi, sB i hi, vmk_vP_vM, vmk_vP_vM]
  exact ⟨rfl, rfl⟩

theorem ptsW_spec {K A B : Nat → Nat} {n lo : Nat} {fin : Nat → Nat → Nat → Bool} :
    ∀ (k xk xa xb : Nat), ptsW K A B n lo fin k xk xa xb = true →
      (∀ i < k, canon (key K (lo + i)) = true ∧ tab A (lo + i) < n ∧ tab B (lo + i) < n) ∧
      fin (encF k (fun i => key K (lo + i)) + 2 ^ (512 * k) * xk)
        (encF k (fun i => key K (tab A (lo + i))) + 2 ^ (512 * k) * xa)
        (encF k (fun i => key K (tab B (lo + i))) + 2 ^ (512 * k) * xb) = true
  | 0, xk, xa, xb, h => by
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    change fin xk xa xb = true at h
    simpa [encF] using h
  | k + 1, xk, xa, xb, h => by
    change (strictB (Nat.add lo k) fun h =>
      strictB (key K h) fun x => strictB (tab A h) fun a => strictB (tab B h) fun b =>
        bAnd(canon x, bAnd(Nat.blt a n, bAnd(Nat.blt b n,
          strictB (Nat.add x (Nat.shiftLeft xk 512)) fun xk' =>
          strictB (Nat.add (key K a) (Nat.shiftLeft xa 512)) fun xa' =>
          strictB (Nat.add (key K b) (Nat.shiftLeft xb 512)) fun xb' =>
            ptsW K A B n lo fin k xk' xa' xb')))) = true at h
    simp only [PackFld.strictB_eqP] at h
    obtain ⟨hc, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨ha, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨hb, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨ih1, ih2⟩ := ptsW_spec k _ _ _ h
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases Nat.lt_or_ge i k with hik | hik
      · exact ih1 i hik
      · have : i = k := by omega
        subst this
        exact ⟨hc, Nat.blt_eq.mp ha, Nat.blt_eq.mp hb⟩
    · have e : ∀ (f : Nat → Nat) (x : Nat), encF k f + 2 ^ (512 * k) * Nat.add (f k) (Nat.shiftLeft x 512) =
          encF (k + 1) f + 2 ^ (512 * (k + 1)) * x := by
        intro f x
        rw [enc_top, PackFld.shl_eq, Nat.add_eq, show 512 * (k + 1) = 512 * k + 512 by omega,
          Nat.pow_add]
        simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm x]
        omega
      have e1 := e (fun i => key K (lo + i)) xk
      have e2 := e (fun i => key K (tab A (lo + i))) xa
      have e3 := e (fun i => key K (tab B (lo + i))) xb
      simp only [Nat.add_eq] at e1 e2 e3 ih2
      rw [e1, e2, e3] at ih2
      exact ih2

theorem key_lt (K : Nat → Nat) (i : Nat) : key K i < 2 ^ 512 := by
  have e : key K i = rget K 4 15 512 (mask 512) i := rfl
  rw [e]
  unfold rget
  rw [PackFld.strictN_eqP]
  change _ &&& mask 512 < _
  rw [PackFld.mask_eq]
  exact Nat.and_lt_two_pow _ (by omega)

theorem mvRangeW_imp {K : Nat → Nat} {LA LB : List Nat} {A B : Nat → Nat} {n lo cnt : Nat}
    (h : mvRangeW K LA LB A B n lo cnt = true) : mvRange K LA LB A B n lo cnt = true := by
  obtain ⟨h1, h2⟩ := ptsW_spec cnt 0 0 0 h
  simp only [Nat.mul_zero, Nat.add_zero] at h2
  have hf := finW_spec (fun i _ => key_lt K _) (fun i _ => key_lt K _) (fun i _ => key_lt K _)
    (fun i hi => (h1 i hi).1) h2
  refine allBlk_of fun l hl => ?_
  obtain ⟨hc, ha, hb⟩ := h1 l hl
  obtain ⟨eA, eB⟩ := hf l hl
  unfold mvAt
  simp only [PackFld.strictB_eqP, Nat.add_eq]
  rw [hc, Nat.blt_eq.mpr ha, Nat.blt_eq.mpr hb, eA, eB]
  simp [Nat.beq_refl]

end CFSG.KS.ONW

end
