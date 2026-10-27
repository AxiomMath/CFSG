module

public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.CFSGNative.Co1.CoverCheck
public import Certificates.Data.CFSGNative.Co1.Odd
import CFSG.Certificates.Kernel.SporSch.PairJ3FaithSound
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.Co1F2

open CFSG.KC.M1F2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.CoverNative CFSG.Sporadic.Co1.OddNative
open CFSG.KS.SporSch.PF2 (unpackP mulRows_unpack idF_unpack mulF_row fget_orN rowF_lt pw2_eq
  bit_eq)

@[expose] def unpackR (d M : Nat) : Array Nat := Array.ofFn (n := d) fun i => M / 2 ^ (d * i.val) % 2 ^ d

theorem validRows_unpackR (M : Nat) : CFSG.Sporadic.Co1.InvNative.validRows (unpackR 24 M) = true := by
  simp only [CFSG.Sporadic.Co1.InvNative.validRows, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [unpackR], fun i hi => ?_⟩
  simp only [unpackR, Array.getElem_ofFn]
  exact (Nat.mod_lt _ (by norm_num)).trans_eq (by norm_num)

private theorem m1StrictB_eq (y : Nat) (k : Nat → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

private theorem m1Run_cons (d M : Nat) (ch : Char) (cs : List Char) (ph k acc : Nat) :
    m1Run d M (ch :: cs) ph k acc =
      bIf(Nat.beq ph (nat_lit 0),
        bIf(Nat.beq (Char.toNat ch) (nat_lit 10), m1Run d M cs (nat_lit 1) k acc,
          m1Run d M cs (nat_lit 0) k acc),
        bIf(wsC (Char.toNat ch), m1Run d M cs ph k acc,
          bIf(Nat.blt k (Nat.mul d d),
            bIf(Nat.beq (Nat.succ (Nat.mod k d)) d,
              CFSG.KLie.CT.andB (Nat.beq (Nat.lor (Nat.shiftRight acc (nat_lit 64))
                  (Nat.shiftLeft (ebit (Char.toNat ch)) (Nat.mod k d)))
                (CFSG.KLie.CT.fget M (Nat.div k d) d)) (m1Run d M cs ph (Nat.succ k) (nat_lit 0)),
              m1Run d M cs ph (Nat.succ k) (Nat.lor (Nat.shiftLeft (Nat.lor
                (Nat.shiftRight acc (nat_lit 64))
                  (Nat.shiftLeft (ebit (Char.toNat ch)) (Nat.mod k d)))
                  (nat_lit 64)) (Nat.land (Nat.succ k) (nat_lit 18446744073709551615)))),
            m1Run d M cs ph (Nat.succ k) acc))) := by
  change CFSG.KC.M1F2.strictB k (fun k => CFSG.KC.M1F2.strictB acc fun acc =>
    CFSG.KC.M1F2.strictB (Char.toNat ch) fun c =>
      bIf(Nat.beq ph (nat_lit 0),
        bIf(Nat.beq c (nat_lit 10), m1Run d M cs (nat_lit 1) k acc, m1Run d M cs (nat_lit 0) k acc),
        bIf(wsC c, m1Run d M cs ph k acc,
          bIf(Nat.blt k (Nat.mul d d),
            CFSG.KC.M1F2.strictB (Nat.lor (Nat.shiftRight acc (nat_lit 64))
              (Nat.shiftLeft (ebit c) (Nat.mod k d))) fun r =>
              bIf(Nat.beq (Nat.succ (Nat.mod k d)) d,
                CFSG.KLie.CT.andB (Nat.beq r (CFSG.KLie.CT.fget M (Nat.div k d) d))
                  (m1Run d M cs ph (Nat.succ k) (nat_lit 0)),
                m1Run d M cs ph (Nat.succ k) (Nat.lor (Nat.shiftLeft r (nat_lit 64))
                  (Nat.land (Nat.succ k) (nat_lit 18446744073709551615)))),
            m1Run d M cs ph (Nat.succ k) acc)))) = _
  simp only [m1StrictB_eq]

private theorem m1Run_header {d M : Nat} : ∀ cs : List Char,
    m1Run d M cs (nat_lit 0) (nat_lit 0) (nat_lit 0) = true →
    m1Run d M ((cs.dropWhile (· != '\n')).drop 1) (nat_lit 1) (nat_lit 0) (nat_lit 0) = true
  | [], h => absurd h Bool.false_ne_true
  | ch :: cs, h => by
    rw [m1Run_cons] at h
    have e0 : Nat.beq (nat_lit 0) (nat_lit 0) = true := rfl
    rw [e0] at h
    by_cases hc : ch = '\n'
    · subst hc
      exact h
    · have h10 : Nat.beq (Char.toNat ch) 10 = false := by
        cases hb : Nat.beq (Char.toNat ch) 10
        · rfl
        · exfalso
          apply hc
          have := Nat.eq_of_beq_eq_true hb
          exact Char.ext (UInt32.toNat_inj.mp (by simpa using this))
      rw [h10] at h
      have hne : (ch != '\n') = true := by simpa using hc
      rw [List.dropWhile_cons_of_pos (p := fun x => x != '\n') hne]
      exact m1Run_header cs h

private noncomputable def dg (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

private noncomputable def ents (B : List Char) : List Nat :=
  (B.filter fun c => !CFSG.Sporadic.Th.Native.wsChar c).map dg

private noncomputable def gE (d : Nat) (E : List Nat) (i j : Nat) : Bool :=
  (E[i * d + j]?.getD 0) % 2 == 1

private theorem char_beq (c d : Char) : (c == d) = (c.toNat == d.toNat) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Char.ext (UInt32.toNat_inj.mp h)

private theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e
  subst e
  rw [Nat.beq_refl] at h
  exact Bool.noConfusion h

private theorem char_le (c d : Char) : (c ≤ d) ↔ c.toNat ≤ d.toNat := UInt32.le_iff_toNat_le

private theorem wsC_eq (c : Char) : wsC c.toNat = CFSG.Sporadic.Th.Native.wsChar c := by
  unfold wsC CFSG.Sporadic.Th.Native.wsChar
  rw [char_beq, char_beq, char_beq, char_beq]
  have e1 : (' ' : Char).toNat = 32 := rfl
  have e2 : ('\t' : Char).toNat = 9 := rfl
  have e3 : ('\n' : Char).toNat = 10 := rfl
  have e4 : ('\r' : Char).toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  generalize c.toNat = x
  unfold CFSG.KLie.CT.orB CFSG.KLie.CT.andB
  apply Bool.eq_iff_iff.mpr
  cases h1 : Nat.beq x 32
  · have h1' := ne_of_beq_false h1
    cases h2 : Nat.ble 9 x
    · have h2' : ¬ 9 ≤ x := fun h' => by
        have := Nat.ble_eq.mpr h'
        rw [h2] at this
        exact Bool.false_ne_true this
      simp only [Bool.false_eq_true, false_iff, Bool.or_eq_true, beq_iff_eq, not_or]
      omega
    · have h2' : 9 ≤ x := Nat.le_of_ble_eq_true h2
      cases h3 : Nat.ble x 13
      · have h3' : ¬ x ≤ 13 := fun h' => by
          have := Nat.ble_eq.mpr h'
          rw [h3] at this
          exact Bool.false_ne_true this
        simp only [Bool.false_eq_true, false_iff, Bool.or_eq_true, beq_iff_eq, not_or]
        omega
      · have h3' : x ≤ 13 := Nat.le_of_ble_eq_true h3
        simp only [true_iff, Bool.or_eq_true, beq_iff_eq]
        omega
  · have h1' : x = 32 := Nat.eq_of_beq_eq_true h1
    simp [h1']

private theorem ebit_eq (c : Char) : ebit c.toNat = dg c % 2 := by
  unfold ebit dg
  have e0 : ('0' : Char).toNat = 48 := rfl
  have e9 : ('9' : Char).toNat = 57 := rfl
  rw [e0]
  unfold CFSG.KLie.CT.andB
  have hd : ('0' ≤ c && c ≤ '9') = (Nat.ble 48 c.toNat && Nat.ble c.toNat 57) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq, char_le, e0, e9]
  rw [hd]
  cases Nat.ble 48 c.toNat <;> cases Nat.ble c.toNat 57 <;>
    simp [Nat.and_one_is_mod]

private theorem ofBits_succ (m : Nat) (f : Nat → Bool) :
    ofBits (m + 1) f = ofBits m f ||| (if f m then 1 <<< m else 0) := by
  unfold ofBits
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  split <;> simp

private theorem ofBits_congr {f f' : Nat → Bool} : ∀ m, (∀ j < m, f j = f' j) →
    ofBits m f = ofBits m f'
  | 0, _ => rfl
  | m + 1, h => by
    rw [ofBits_succ, ofBits_succ, ofBits_congr m (fun j hj => h j (by omega)), h m (by omega)]

private theorem shr_or64 (r x : Nat) (hx : x < 2 ^ 64) :
    Nat.shiftRight (Nat.lor (Nat.shiftLeft r (nat_lit 64)) x) (nat_lit 64) = r := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((r <<< 64 ||| x) >>> 64).testBit i = r.testBit i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))]
  simp

private theorem bit_shl (x m : Nat) :
    Nat.shiftLeft (x % 2) m = if (x % 2 == 1) then 1 <<< m else 0 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h]
  · simp
  · rfl

private theorem getD_append_left {pre X : List Nat} {n : Nat} (h : n < pre.length) :
    (pre ++ X)[n]?.getD 0 = pre[n]?.getD 0 := by
  rw [List.getElem?_append_left h]

private theorem divmod {k d q m : Nat} (hk : k = q * d + m) (hm : m < d) :
    k / d = q ∧ k % d = m := by
  have hd : 0 < d := by omega
  exact (Nat.div_mod_unique hd).2 ⟨by rw [hk, Nat.mul_comm]; omega, hm⟩

private theorem m1Run_body {d M : Nat} : ∀ (B : List Char) (k acc : Nat) (pre : List Nat),
    pre.length = k → (k < d * d → Nat.shiftRight acc 64 = ofBits (k % d) (gE d pre (k / d))) →
    m1Run d M B (nat_lit 1) k acc = true →
    ∀ i < d, k / d ≤ i → ofBits d (gE d (pre ++ ents B) i) = CFSG.KLie.CT.fget M i d
  | [], k, acc, pre, _, _, h, i, hi, hki => by
    change CFSG.KLie.CT.andB (Nat.beq (nat_lit 1) (nat_lit 1)) (Nat.ble (Nat.mul d d) k) = true
      at h
    have hk : d * d ≤ k := Nat.le_of_ble_eq_true h
    have : d ≤ k / d := (Nat.le_div_iff_mul_le (by omega)).2 hk
    omega
  | ch :: B, k, acc, pre, hl, hinv, h, i, hi, hki => by
    rw [m1Run_cons] at h
    have e10 : Nat.beq (nat_lit 1) (nat_lit 0) = false := rfl
    rw [e10] at h
    dsimp only at h
    have hd : 0 < d := by omega
    by_cases hws : CFSG.Sporadic.Th.Native.wsChar ch = true
    · rw [wsC_eq, hws] at h
      have he : ents (ch :: B) = ents B := by
        simp [ents, hws]
      rw [he]
      exact m1Run_body B k acc pre hl hinv h i hi hki
    · have hws' : CFSG.Sporadic.Th.Native.wsChar ch = false := by simpa using hws
      rw [wsC_eq, hws'] at h
      dsimp only at h
      have he : ents (ch :: B) = dg ch :: ents B := by
        simp [ents, hws']
      rw [he, show pre ++ dg ch :: ents B = (pre ++ [dg ch]) ++ ents B by simp]
      have hl' : (pre ++ [dg ch]).length = k + 1 := by simp [hl]
      cases hkd : Nat.blt k (Nat.mul d d) <;> rw [hkd] at h <;> dsimp only at h
      ·
        have hk : d * d ≤ k := by
          apply Nat.le_of_not_lt
          intro h'
          have h2 : Nat.blt k (Nat.mul d d) = true := Nat.blt_eq.mpr h'
          rw [hkd] at h2
          exact Bool.false_ne_true h2
        have : d ≤ k / d := (Nat.le_div_iff_mul_le hd).2 hk
        omega
      · have hk : k < d * d := Nat.blt_eq.mp hkd
        have hdm := Nat.div_add_mod' k d
        have hmd := Nat.mod_lt k hd
        have hr : Nat.lor (Nat.shiftRight acc 64)
            (Nat.shiftLeft (ebit (Char.toNat ch)) (Nat.mod k d)) =
              ofBits (k % d + 1) (gE d (pre ++ [dg ch]) (k / d)) := by
          rw [hinv hk, ebit_eq, ofBits_succ]
          have e1 : ∀ j < k % d, gE d pre (k / d) j = gE d (pre ++ [dg ch]) (k / d) j := by
            intro j hj
            unfold gE
            rw [getD_append_left (by rw [hl]; omega)]
          rw [ofBits_congr _ e1]
          have e2 : gE d (pre ++ [dg ch]) (k / d) (k % d) = (dg ch % 2 == 1) := by
            unfold gE
            have : k / d * d + k % d = pre.length := by rw [hl]; omega
            rw [this, List.getElem?_concat_length]
            rfl
          rw [e2, bit_shl]
          rfl
        cases hlast : Nat.beq (Nat.succ (Nat.mod k d)) d <;> rw [hlast] at h <;> dsimp only at h
        ·
          have hlast' : k % d + 1 ≠ d := ne_of_beq_false hlast
          obtain ⟨q1, m1⟩ := divmod (k := k + 1) (d := d) (q := k / d) (m := k % d + 1)
            (by omega) (by omega)
          refine m1Run_body B (k + 1) _ (pre ++ [dg ch]) hl' (fun _ => ?_) h i hi (by omega)
          rw [hr, shr_or64 _ (Nat.land (Nat.succ k) (nat_lit 18446744073709551615))
            (Nat.and_lt_two_pow _ (by decide)), q1, m1]
        ·
          have hlast' : k % d + 1 = d := Nat.eq_of_beq_eq_true hlast
          unfold CFSG.KLie.CT.andB at h
          cases hrow : Nat.beq (Nat.lor (Nat.shiftRight acc 64)
              (Nat.shiftLeft (ebit (Char.toNat ch)) (Nat.mod k d)))
              (CFSG.KLie.CT.fget M (Nat.div k d) d) <;> rw [hrow] at h
          · exact absurd h Bool.false_ne_true
          have hrow' := Nat.eq_of_beq_eq_true hrow
          have hdiv : Nat.div k d = k / d := rfl
          rw [hr, hlast', hdiv] at hrow'
          obtain ⟨q1, m1⟩ := divmod (k := k + 1) (d := d) (q := k / d + 1) (m := 0)
            (by rw [Nat.succ_mul]; omega) hd
          by_cases hiq : i = k / d
          · subst hiq
            rw [← hrow']
            apply ofBits_congr
            intro j hj
            unfold gE
            rw [getD_append_left (by rw [hl']; omega)]
          · refine m1Run_body B (k + 1) 0 (pre ++ [dg ch]) hl' (fun _ => ?_) h i hi (by omega)
            rw [m1]
            rfl

theorem bind_sound {cs : List Char} {d M : Nat} (h : m1Bind cs d M = true) :
    rowsOfPayload d (String.ofList cs) = unpackR d M := by
  have hb := m1Run_body (d := d) (M := M) _ 0 0 [] rfl (fun _ => rfl) (m1Run_header cs h)
  unfold rowsOfPayload unpackR
  dsimp only
  congr 1
  funext i
  have hdec : (CFSG.Sporadic.Th.Native.decodeEntries (String.ofList cs)) =
      ents ((cs.dropWhile (· != '\n')).drop 1) := by
    unfold CFSG.Sporadic.Th.Native.decodeEntries ents
    rw [String.toList_ofList]
    rfl
  have hi := hb i.val i.isLt (by rw [Nat.zero_div]; exact Nat.zero_le _)
  rw [List.nil_append] at hi
  rw [hdec]
  unfold gE at hi
  simp only [List.getElem?_toArray]
  rw [hi]
  unfold CFSG.KLie.CT.fget CFSG.KLie.CT.maskN CFSG.KLie.CT.pw2
  change (M >>> (i.val * d)) &&& ((1 <<< d) - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mul_comm]

private theorem fget_eq (M i d : Nat) : CFSG.KLie.CT.fget M i d = M / 2 ^ (d * i) % 2 ^ d := by
  unfold CFSG.KLie.CT.fget CFSG.KLie.CT.maskN CFSG.KLie.CT.pw2
  change (M >>> (i * d)) &&& ((1 <<< d) - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mul_comm]

private theorem andB_true' {a b : Bool} (h : CFSG.KLie.CT.andB a b = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KLie.CT.andB]

private theorem packAt_sound {d M : Nat} : ∀ (L : List Nat) (i : Nat), packAt d M L i = true →
    i + L.length = d ∧ ∀ k (hk : k < L.length), L[k] = CFSG.KLie.CT.fget M (i + k) d
  | [], i, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun k hk => absurd hk (by simp)⟩
  | r :: L, i, h => by
    change CFSG.KC.M1F2.strictB i (fun i => CFSG.KLie.CT.andB (Nat.blt r (CFSG.KLie.CT.pw2 d))
      (CFSG.KLie.CT.andB (Nat.beq r (CFSG.KLie.CT.fget M i d)) (packAt d M L (Nat.succ i)))) = true
      at h
    rw [m1StrictB_eq] at h
    obtain ⟨_, h⟩ := andB_true' h
    obtain ⟨h1, h2⟩ := andB_true' h
    obtain ⟨a, b⟩ := packAt_sound L (i + 1) h2
    refine ⟨by simp; omega, fun k hk => ?_⟩
    cases k with
    | zero => simpa using Nat.eq_of_beq_eq_true h1
    | succ k =>
      rw [List.getElem_cons_succ, b k (by simpa using hk)]
      congr 1
      omega

theorem packB_sound {d M : Nat} {L : List Nat} (h : packB d L M = true) : L.toArray = unpackR d M := by
  obtain ⟨hl, he⟩ := packAt_sound L 0 h
  rw [Nat.zero_add] at hl
  apply Array.ext
  · simp [unpackR, hl]
  · intro k h1 _
    simp only [List.getElem_toArray, unpackR, Array.getElem_ofFn]
    rw [he k (by simpa using h1), Nat.zero_add, fget_eq]

private theorem unpackR_eq (d M : Nat) : unpackR d M = CFSG.KS.SporSch.PF2.unpackP d M := by
  unfold unpackR CFSG.KS.SporSch.PF2.unpackP
  congr 1
  funext i
  rw [rowF, fget_eq]

theorem mul_sound {d A B C : Nat} (h : Nat.beq (mulF d A B) C = true) :
    mulRows d (unpackR d A) (unpackR d B) = unpackR d C := by
  rw [unpackR_eq, unpackR_eq, unpackR_eq]
  exact CFSG.KS.SporSch.PF2.mulF_sound h

private theorem strictN_eqC (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem powK_succ (d M e : Nat) : powK d M (e + 1) = mulF d (powK d M e) M := by
  change CFSG.KC.Loop.strictN (powK d M e) (fun a => mulF d a M) = _
  exact strictN_eqC _ _

private theorem powK_unpack (d M : Nat) : ∀ e, unpackP d (powK d M e) = powRows d (unpackP d M) e
  | 0 => idF_unpack d
  | e + 1 => by
    rw [powK_succ, ← mulRows_unpack, powK_unpack d M e]
    rfl

private theorem orN_congr {f g : Nat → Nat} : ∀ n, (∀ i < n, f i = g i) →
    CFSG.KLie.CT.orN n f = CFSG.KLie.CT.orN n g
  | 0, _ => rfl
  | n + 1, h => by
    change Nat.lor (f n) (CFSG.KLie.CT.orN n f) = Nat.lor (g n) (CFSG.KLie.CT.orN n g)
    rw [h n (by omega), orN_congr n (fun i hi => h i (by omega))]

private theorem idF_row (d i : Nat) (hi : i < d) : rowF d (idF d) i = CFSG.KLie.CT.pw2 i := by
  rw [rowF, idF]
  exact fget_orN d d CFSG.KLie.CT.pw2
    (fun j hj => by rw [pw2_eq]; exact Nat.pow_lt_pow_right (by norm_num) hj) i hi

private theorem powK_pack (d M : Nat) : ∀ e, powK d M e =
    CFSG.KLie.CT.orN d fun i => Nat.shiftLeft (rowF d (powK d M e) i) (Nat.mul d i)
  | 0 => by
    change idF d = _
    exact orN_congr (f := fun i => Nat.shiftLeft (CFSG.KLie.CT.pw2 i) (Nat.mul d i)) d
      (fun i hi => by rw [show powK d M 0 = idF d from rfl, idF_row d i hi])
  | e + 1 => by
    rw [powK_succ]
    have e' : (CFSG.KLie.CT.orN d fun i =>
        Nat.shiftLeft (rowF d (mulF d (powK d M e) M) i) (Nat.mul d i)) =
        CFSG.KLie.CT.orN d fun i => Nat.shiftLeft (vmF d M (rowF d (powK d M e) i)) (Nat.mul d i) :=
      orN_congr d (fun i hi => by rw [mulF_row d _ M i hi])
    rw [e']
    unfold mulF
    rw [strictN_eqC, strictN_eqC]

private theorem getL_eq (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L[i]?.getD x
  | [], _ => rfl
  | a :: L, 0 => rfl
  | a :: L, i + 1 => by
    change getL x L i = _
    rw [getL_eq x L i]
    rfl

private theorem lenL_eq : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenL L) = _
    rw [lenL_eq L]
    rfl

private theorem facBelow_sound {t : Nat} : ∀ {fac : List (Nat × Nat)}, facBelow fac t = true →
    ∀ p ∈ fac, p.1 < t
  | [], _, p, hp => absurd hp (by simp)
  | q :: fac, h, p, hp => by
    obtain ⟨h1, h2⟩ := andB_true' h
    rcases List.mem_cons.mp hp with e | e
    · subst e
      exact Nat.blt_eq.mp h1
    · exact facBelow_sound h2 p e

private theorem lineK_run (R : List Nat) {t : Nat} (ht : t ≤ R.length) :
    ∀ (fac : List (Nat × Nat)) (acc : Nat), (∀ p ∈ fac, p.1 < t) →
    unpackP 24 (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun p _ ih acc => CFSG.KC.Loop.strictN (Prod.rec (motive := fun _ => Nat)
        (fun i e => mulF 24 acc (powK 24 (getL (idF 24) R i) e)) p) ih) fac acc) =
      fac.foldl (fun A p => mulRows 24 A (powRows 24
        ((((R.take t).map (unpackR 24)).toArray)[p.1]?.getD (idRows 24)) p.2)) (unpackP 24 acc)
  | [], _, _ => rfl
  | (i, e) :: fac, acc, hf => by
    change unpackP 24 (CFSG.KC.Loop.strictN _ _) = _
    rw [strictN_eqC, lineK_run R ht fac _ (fun p hp => hf p (List.mem_cons_of_mem _ hp)),
      List.foldl_cons]
    have hi : i < t := hf (i, e) (by simp)
    have hreg : (((R.take t).map (unpackR 24)).toArray)[i]?.getD (idRows 24) =
        unpackP 24 (getL (idF 24) R i) := by
      rw [getL_eq, List.getElem?_eq_getElem (by omega), Option.getD_some,
        Array.getElem?_eq_getElem (by simp; omega), Option.getD_some, List.getElem_toArray,
        List.getElem_map, List.getElem_take, unpackR_eq]
    change List.foldl _ (unpackP 24 (mulF 24 acc (powK 24 (getL (idF 24) R i) e))) fac = _
    rw [hreg, ← mulRows_unpack, powK_unpack]

private theorem progK_run (R : List Nat) : ∀ (prog : List (List (Nat × Nat))) (t : Nat),
    progK 24 R prog t = true →
    t + prog.length = R.length ∧
      runRows ((R.take t).map (unpackR 24)).toArray prog = (R.map (unpackR 24)).toArray
  | [], t, h => by
    have e : R.length = t := by
      rw [← lenL_eq]
      exact Nat.eq_of_beq_eq_true h
    refine ⟨by simp [e], ?_⟩
    rw [← e, List.take_length]
    rfl
  | fac :: prog, t, h => by
    change CFSG.KC.M1F2.strictB t (fun t => CFSG.KLie.CT.andB (facBelow fac t)
      (CFSG.KLie.CT.andB (Nat.beq (getL (nat_lit 0) R t) (lineK 24 R fac))
        (progK 24 R prog (Nat.succ t)))) = true at h
    rw [m1StrictB_eq] at h
    obtain ⟨h1, h⟩ := andB_true' h
    obtain ⟨h2, h3⟩ := andB_true' h
    obtain ⟨hl, hrun⟩ := progK_run R prog (t + 1) h3
    refine ⟨by simp; omega, ?_⟩
    have ht : t < R.length := by omega
    rw [← hrun]
    change runRows ((((R.take t).map (unpackR 24)).toArray).push
      (lineRows ((R.take t).map (unpackR 24)).toArray fac)) prog = _
    congr 1
    have hline : lineRows ((R.take t).map (unpackR 24)).toArray fac = unpackR 24 R[t] := by
      unfold lineRows
      have hk := lineK_run R (Nat.le_of_lt ht) fac (idF 24) (facBelow_sound h1)
      rw [idF_unpack] at hk
      rw [← hk]
      change unpackP 24 (lineK 24 R fac) = _
      rw [← Nat.eq_of_beq_eq_true h2, getL_eq, List.getElem?_eq_getElem ht, Option.getD_some,
        unpackR_eq]
    rw [hline, List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.map_append,
      List.push_toArray]
    rfl

theorem prog_sound {R : List Nat} {prog : List (List (Nat × Nat))} {t : Nat}
    (h : progK 24 R prog t = true) :
    runRows ((R.take t).map (unpackR 24)).toArray prog = (R.map (unpackR 24)).toArray :=
  (progK_run R prog t h).2

private def Canon (d X : Nat) : Prop :=
  CFSG.KLie.CT.orN d (fun i => Nat.shiftLeft (rowF d X i) (Nat.mul d i)) = X

private theorem mulF_canon (d A B : Nat) : Canon d (mulF d A B) := by
  unfold Canon
  have e' : (CFSG.KLie.CT.orN d fun i =>
      Nat.shiftLeft (rowF d (mulF d A B) i) (Nat.mul d i)) =
      CFSG.KLie.CT.orN d fun i => Nat.shiftLeft (vmF d B (rowF d A i)) (Nat.mul d i) :=
    orN_congr d (fun i hi => by rw [mulF_row d A B i hi])
  rw [e']
  unfold mulF
  rw [strictN_eqC, strictN_eqC]

private theorem idF_canon (d : Nat) : Canon d (idF d) :=
  (powK_pack d 0 0).symm

private theorem canon_inj {d X Y : Nat} (hX : Canon d X) (hY : Canon d Y)
    (h : unpackP d X = unpackP d Y) : X = Y := by
  unfold Canon at hX hY
  rw [← hX, ← hY]
  refine orN_congr d (fun i hi => ?_)
  rw [← CFSG.KS.SporSch.PF2.unpackP_get d X i hi, ← CFSG.KS.SporSch.PF2.unpackP_get d Y i hi, h]

private theorem rowF_zero (d i : Nat) : rowF d 0 i = 0 := by
  change (0 >>> (i * d)) &&& CFSG.KLie.CT.maskN d = 0
  rw [Nat.zero_shiftRight, Nat.zero_and]

private theorem vmF_zero (d M : Nat) : vmF d M 0 = 0 := by
  unfold vmF
  have key : ∀ n, Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Bool.rec (motive := fun _ => Nat)
      acc (Nat.xor (rowF d M k) acc) (CFSG.KLie.CT.bit 0 k)) n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change Bool.rec (motive := fun _ => Nat) _ _ (CFSG.KLie.CT.bit 0 n) = 0
      rw [bit_eq, Nat.zero_testBit]
      exact ih
  exact key d

private theorem orN_zero : ∀ n, CFSG.KLie.CT.orN n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by
    change Nat.lor 0 (CFSG.KLie.CT.orN n fun _ => 0) = 0
    rw [orN_zero n]
    rfl

private theorem mulF_zero (d M : Nat) : mulF d 0 M = 0 := by
  unfold mulF
  rw [strictN_eqC, strictN_eqC,
    orN_congr (g := fun _ => 0) d (fun i _ => by rw [rowF_zero, vmF_zero]; exact Nat.zero_shiftLeft _)]
  exact orN_zero d

private theorem idF_ne_zero : idF 24 ≠ 0 := by
  intro h
  have h1 := idF_row 24 0 (by norm_num)
  rw [h, rowF_zero] at h1
  exact absurd h1 (by decide)

private theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

private theorem nrec_beq (a b t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t (Nat.beq a b) = if a = b then t else e := by
  by_cases h : a = b
  · subst h
    rw [Nat.beq_refl, ite_eq_left rfl]
  · rw [beq_false h, ite_eq_right h]

private theorem ctAllN_spec {n : Nat} {f : Nat → Bool} :
    CFSG.KLie.CT.allN n f = true → ∀ i < n, f i = true := by
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    obtain ⟨h1, h2⟩ := andB_true' h
    rcases Nat.lt_or_ge i n with hl | hl
    · exact ih h2 i hl
    · have : i = n := by omega
      subst this
      exact h1

private noncomputable def invC (M : Nat) (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) M (fun _ acc => CFSG.KC.Loop.strictN acc fun c =>
    CFSG.KC.Loop.strictN (mulF 24 c M) fun nx => nIf(Nat.beq nx (idF 24), 0, nx)) j

private theorem invC_succ (M j : Nat) : invC M (j + 1) =
    if mulF 24 (invC M j) M = idF 24 then 0 else mulF 24 (invC M j) M := by
  change CFSG.KC.Loop.strictN (invC M j) (fun c => CFSG.KC.Loop.strictN (mulF 24 c M) fun nx =>
    nIf(Nat.beq nx (idF 24), 0, nx)) = _
  rw [strictN_eqC, strictN_eqC, nrec_beq]

theorem inv_sound {M MI k : Nat} (h : invK 24 M MI k = true) : invRows (unpackR 24 M) = unpackR 24 MI := by
  unfold invK at h
  obtain ⟨-, h⟩ := andB_true' h
  obtain ⟨hk1, h⟩ := andB_true' h
  obtain ⟨hMI, hc⟩ := andB_true' h
  have hk1 : k ≤ 100000 := Nat.le_of_ble_eq_true hk1
  have hMI : mulF 24 MI M = idF 24 := Nat.eq_of_beq_eq_true hMI
  have hc : invC M (k - 1) = MI := Nat.eq_of_beq_eq_true hc
  have hz0 : ∀ j, invC M j = 0 → ∀ i, invC M (j + i) = 0 := by
    intro j hj i
    induction i with
    | zero => exact hj
    | succ i ih =>
      rw [← Nat.add_assoc, invC_succ, ih, mulF_zero, ite_eq_right (Ne.symm idF_ne_zero)]
  have hz : ∀ j ≤ k - 1, invC M j ≠ 0 := by
    intro j hj h0
    have h1 := hz0 j h0 (k - 1 - j)
    rw [Nat.add_sub_cancel' hj, hc] at h1
    rw [h1, mulF_zero] at hMI
    exact idF_ne_zero hMI.symm
  have hne : ∀ j < k - 1, mulF 24 (invC M j) M ≠ idF 24 := by
    intro j hj he
    have h1 := invC_succ M j
    rw [ite_eq_left he] at h1
    exact hz (j + 1) (by omega) h1
  have hloop : ∀ fuel j, j ≤ k - 1 → k - 1 - j < fuel →
      invRowsLoop (unpackP 24 M) fuel (unpackP 24 (invC M j)) = unpackP 24 MI := by
    intro fuel
    induction fuel with
    | zero => intro j _ h; omega
    | succ fuel ih =>
      intro j hj hf
      simp only [invRowsLoop]
      rw [mulRows_unpack]
      rcases Nat.lt_or_ge j (k - 1) with hjk | hjk
      · have hn : (unpackP 24 (mulF 24 (invC M j) M) == idRows 24) = false := by
          rw [beq_eq_false_iff_ne]
          intro he
          apply hne j hjk
          apply canon_inj (mulF_canon _ _ _) (idF_canon 24)
          rw [he, idF_unpack]
        rw [hn]
        simp only [Bool.false_eq_true, ite_false]
        have hs : mulF 24 (invC M j) M = invC M (j + 1) := by rw [invC_succ, ite_eq_right (hne j hjk)]
        rw [hs]
        exact ih (j + 1) (by omega) (by omega)
      · have hj' : j = k - 1 := by omega
        subst hj'
        rw [hc, hMI, idF_unpack]
        simp
  rw [unpackR_eq, unpackR_eq]
  exact hloop 100000 0 (Nat.zero_le _) (by omega)

private theorem letK_unpack (d A B AI BI : Nat) (l : Nat × Bool) :
    unpackP d (letK A B AI BI l) =
      letterRows (unpackP d A) (unpackP d B) (unpackP d AI) (unpackP d BI) l := by
  obtain ⟨i, s⟩ := l
  cases i <;> cases s <;> rfl

private theorem wordK_run (d A B AI BI : Nat) : ∀ (w : List (Nat × Bool)) (acc : Nat),
    unpackP d (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun l _ ih acc => CFSG.KC.Loop.strictN (mulF d acc (letK A B AI BI l)) ih) w acc) =
      w.foldl (fun acc l => mulRows d acc (letterRows (unpackP d A) (unpackP d B) (unpackP d AI)
        (unpackP d BI) l)) (unpackP d acc)
  | [], _ => rfl
  | l :: w, acc => by
    change unpackP d (CFSG.KC.Loop.strictN (mulF d acc (letK A B AI BI l)) _) = _
    rw [strictN_eqC, wordK_run d A B AI BI w, List.foldl_cons, ← mulRows_unpack, letK_unpack]

theorem relCheck_sound {d A B AI BI : Nat} {rels : List (List (Nat × Bool))}
    (h : relCheckK d A B AI BI rels = true) :
    relCheckAB d (unpackR d A) (unpackR d B) (unpackR d AI) (unpackR d BI) rels = true := by
  unfold relCheckK at h
  obtain ⟨hA, h⟩ := andB_true' h
  obtain ⟨hB, h⟩ := andB_true' h
  have hall : ∀ (rs : List (List (Nat × Bool))), List.rec (motive := fun _ => Bool) true
      (fun w _ ih => CFSG.KLie.CT.andB (Nat.beq (wordK d A B AI BI w) (idF d)) ih) rs = true →
      ∀ w ∈ rs, wordK d A B AI BI w = idF d := by
    intro rs
    induction rs with
    | nil => intro _ w hw; exact absurd hw (by simp)
    | cons r rs ih =>
      intro h w hw
      obtain ⟨h1, h2⟩ := andB_true' h
      rcases List.mem_cons.mp hw with e | e
      · rw [e]
        exact Nat.eq_of_beq_eq_true h1
      · exact ih h2 w e
  rw [unpackR_eq, unpackR_eq, unpackR_eq, unpackR_eq]
  unfold relCheckAB
  rw [CFSG.KS.SporSch.PF2.mulF_id_sound hA, CFSG.KS.SporSch.PF2.mulF_id_sound hB]
  simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro w hw
  have e1 : wordRowsAB d (unpackP d A) (unpackP d B) (unpackP d AI) (unpackP d BI) w =
      unpackP d (wordK d A B AI BI w) := by
    unfold wordRowsAB wordK
    rw [wordK_run, idF_unpack]
  rw [e1, hall rels h w hw, idF_unpack]
  simp

private theorem eprod_run (E : List Nat) (x : Nat) : ∀ k ≤ 11, ∀ acc,
    unpackP 24 (Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun i ih acc => CFSG.KC.Loop.strictN (nIf(CFSG.KLie.CT.bit x (Nat.sub (nat_lit 10) i),
        mulF (nat_lit 24) acc (getL (nat_lit 0) E (Nat.sub (nat_lit 10) i)), acc)) ih) k acc) =
      (List.range' (11 - k) k).foldl (fun A i => if x.testBit i then
        mulRows 24 A (unpackP 24 (getL 0 E i)) else A) (unpackP 24 acc) := by
  intro k
  induction k with
  | zero => intro _ acc; rfl
  | succ k ih =>
    intro hk acc
    change unpackP 24 (CFSG.KC.Loop.strictN _ _) = _
    rw [strictN_eqC, ih (by omega)]
    have e : 11 - (k + 1) = 10 - k := by omega
    rw [e, List.range'_succ, List.foldl_cons, show 10 - k + 1 = 11 - k by omega]
    have hs : unpackP 24 (Bool.rec (motive := fun _ => Nat) acc
        (mulF (nat_lit 24) acc (getL (nat_lit 0) E (Nat.sub (nat_lit 10) k)))
        (CFSG.KLie.CT.bit x (Nat.sub (nat_lit 10) k))) =
        (if x.testBit (10 - k) then mulRows 24 (unpackP 24 acc) (unpackP 24 (getL 0 E (10 - k)))
          else unpackP 24 acc) := by
      have hb := bit_eq x (10 - k)
      change unpackP 24 (Bool.rec (motive := fun _ => Nat) acc
        (mulF 24 acc (getL 0 E (10 - k))) (CFSG.KLie.CT.bit x (10 - k))) = _
      rw [hb]
      cases x.testBit (10 - k)
      · rfl
      · exact (mulRows_unpack 24 acc _).symm
    rw [hs]

theorem eprod_sound {E : List Nat} {x C : Nat} (hE : lenL E = 11) (h : Nat.beq (eprodK E x) C = true) :
    eprodRows (E.map (unpackR 24)).toArray x = unpackR 24 C := by
  rw [← Nat.eq_of_beq_eq_true h, unpackR_eq]
  unfold eprodK
  rw [eprod_run E x (nat_lit 11) (Nat.le_refl 11), idF_unpack, Nat.sub_self,
    ← List.range_eq_range']
  unfold eprodRows
  rw [lenL_eq] at hE
  apply List.foldl_ext
  intro A i hi
  have hi' : i < 11 := List.mem_range.mp hi
  have hg : (E.map (unpackR 24)).toArray[i]! = unpackP 24 (getL 0 E i) := by
    rw [getL_eq, getElem!_pos _ i (by simp [hE, hi']), List.getElem_toArray, List.getElem_map,
      unpackR_eq, List.getElem?_eq_getElem (by omega)]
    rfl
  rw [hg]

private theorem eps_get {E : List Nat} (hE : E.length = 11) {i : Nat} (hi : i < 11) :
    (E.map (unpackR 24)).toArray[i]! = unpackR 24 (getL 0 E i) := by
  rw [getL_eq, getElem!_pos _ i (by simp [hE, hi]), List.getElem_toArray, List.getElem_map,
    List.getElem?_eq_getElem (by omega)]
  rfl

theorem epsBasic_sound {E : List Nat} (h : epsBasicK E = true) :
    epsBasicOK (E.map (unpackR 24)).toArray = true := by
  unfold epsBasicK at h
  obtain ⟨hl, h⟩ := andB_true' h
  have hE : E.length = 11 := by rw [← lenL_eq]; exact Nat.eq_of_beq_eq_true hl
  have hall := ctAllN_spec h
  unfold epsBasicOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨by simp [hE], fun i hi => ?_⟩
  have hi' := hall i hi
  rw [m1StrictB_eq] at hi'
  obtain ⟨hsq, hcomm⟩ := andB_true' hi'
  have hc := ctAllN_spec hcomm
  rw [eps_get hE hi]
  refine ⟨⟨validRows_unpackR _, ?_⟩, fun j hj => ?_⟩
  · rw [mul_sound hsq, unpackR_eq, idF_unpack]
  · have hj' := hc j hj
    rw [m1StrictB_eq] at hj'
    rw [eps_get hE hj, mul_sound hj', mul_sound (Nat.beq_refl _)]

private noncomputable def eP (E : List Nat) : Nat → Nat → Nat
  | 0, _ => idF 24
  | n + 1, x => if x.testBit n then mulF 24 (eP E n x) (getL 0 E n) else eP E n x

private theorem eP_canon (E : List Nat) : ∀ n x, Canon 24 (eP E n x)
  | 0, _ => idF_canon 24
  | n + 1, x => by
    simp only [eP]
    split
    · exact mulF_canon _ _ _
    · exact eP_canon E n x

private theorem eP_zero (E : List Nat) : ∀ n, eP E n 0 = idF 24
  | 0 => rfl
  | n + 1 => by
    simp only [eP, Nat.zero_testBit, Bool.false_eq_true, ite_false]
    exact eP_zero E n

private theorem eP_congr (E : List Nat) : ∀ n x y, (∀ i < n, x.testBit i = y.testBit i) →
    eP E n x = eP E n y
  | 0, _, _, _ => rfl
  | n + 1, x, y, h => by
    simp only [eP]
    rw [h n (by omega), eP_congr E n x y (fun i hi => h i (by omega))]

private theorem eprodK_eq (E : List Nat) (x : Nat) : eprodK E x = eP E 11 x := by
  have key : ∀ k, k ≤ 11 → Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun i ih acc => CFSG.KC.Loop.strictN (nIf(CFSG.KLie.CT.bit x (Nat.sub 10 i),
        mulF 24 acc (getL 0 E (Nat.sub 10 i)), acc)) ih) k
        (eP E (11 - k) x) = eP E 11 x := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      change CFSG.KC.Loop.strictN _ _ = _
      rw [strictN_eqC]
      have hs : nIf(CFSG.KLie.CT.bit x (Nat.sub 10 k),
          mulF 24 (eP E (11 - (k + 1)) x) (getL 0 E (Nat.sub 10 k)),
          eP E (11 - (k + 1)) x) = eP E (11 - k) x := by
        have e : 11 - k = (Nat.sub 10 k) + 1 := by change 11 - k = (10 - k) + 1; omega
        have e2 : 11 - (k + 1) = Nat.sub 10 k := by change 11 - (k + 1) = 10 - k; omega
        rw [e, e2, bit_eq]
        simp only [eP]
        cases x.testBit (Nat.sub 10 k) <;> rfl
      rw [hs]
      exact ih (by omega)
  have := key 11 le_rfl
  rw [Nat.sub_self] at this
  exact this

private theorem extK_rev (g : Nat) : ∀ (L acc : List Nat),
    List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun a _ ih acc => ih (List.cons (mulF 24 a g) acc)) L acc =
      (L.map fun a => mulF 24 a g).reverse ++ acc
  | [], _ => rfl
  | a :: L, acc => by
    change List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun a _ ih acc => ih (List.cons (mulF 24 a g) acc)) L (mulF 24 a g :: acc) = _
    rw [extK_rev g L]
    simp

private theorem copyL : ∀ L : List Nat,
    List.rec (motive := fun _ => List Nat) List.nil (fun a _ ih => List.cons a ih) L = L
  | [] => rfl
  | a :: L => by
    change a :: List.rec (motive := fun _ => List Nat) List.nil (fun a _ ih => List.cons a ih) L = _
    rw [copyL L]

private theorem extK_eq (g : Nat) (L : List Nat) :
    extK g L = (L.map fun a => mulF 24 a g).reverse ++ L := by
  unfold extK
  rw [extK_rev, copyL]

private theorem prodsK_perm (E : List Nat) : ∀ n,
    (prodsK E n).Perm ((List.range (2 ^ n)).map (eP E n))
  | 0 => by
    change [idF 24].Perm _
    simp [eP]
  | n + 1 => by
    change (extK (getL 0 E n) (prodsK E n)).Perm _
    rw [extK_eq]
    have hr : List.range (2 ^ (n + 1)) =
        List.range (2 ^ n) ++ (List.range (2 ^ n)).map (2 ^ n + ·) := by
      rw [pow_succ, mul_two, List.range_add]
    have h1 : (List.range (2 ^ n)).map (eP E (n + 1)) = (List.range (2 ^ n)).map (eP E n) := by
      apply List.map_congr_left
      intro x hx
      have hx' : x < 2 ^ n := List.mem_range.mp hx
      simp only [eP, Nat.testBit_lt_two_pow hx', Bool.false_eq_true, ite_false]
    have h2 : ((List.range (2 ^ n)).map (2 ^ n + ·)).map (eP E (n + 1)) =
        ((List.range (2 ^ n)).map (eP E n)).map (fun a => mulF 24 a (getL 0 E n)) := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro y hy
      have hy' : y < 2 ^ n := List.mem_range.mp hy
      have hb : (2 ^ n + y).testBit n = true := by
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy']
        rfl
      simp only [Function.comp, eP, hb, ite_true]
      rw [eP_congr E n (2 ^ n + y) y (fun i hi => Nat.testBit_two_pow_add_gt hi y)]
    rw [hr, List.map_append, h1, h2]
    exact (List.perm_append_comm.trans
      (List.Perm.append_left _ (List.reverse_perm _))).trans
      ((prodsK_perm E n).append ((prodsK_perm E n).map _))

private theorem countId_eq : ∀ L : List Nat, countId L = L.count (idF 24)
  | [] => rfl
  | a :: L => by
    change nIf(Nat.beq a (idF 24), Nat.succ (countId L), countId L) = _
    rw [nrec_beq, List.count_cons, countId_eq L]
    by_cases e : a = idF 24
    · simp [e]
    · simp [e]

theorem epsInj_sound {E : List Nat} (h : epsInjK E = true) :
    epsInjOK (E.map (unpackR 24)).toArray = true := by
  unfold epsInjK at h
  obtain ⟨hl, hc⟩ := andB_true' h
  have hE : lenL E = 11 := Nat.eq_of_beq_eq_true hl
  have hcnt : ((List.range (2 ^ 11)).map (eP E 11)).count (idF 24) = 1 := by
    rw [← (prodsK_perm E 11).count_eq, ← countId_eq]
    exact Nat.eq_of_beq_eq_true hc
  have hne : ∀ k < 2047, eP E 11 (k + 1) ≠ idF 24 := by
    have e : List.range (2 ^ 11) = 0 :: (List.range 2047).map (· + 1) := by
      rw [show (2 : Nat) ^ 11 = 2047 + 1 by norm_num, List.range_succ_eq_map]
    rw [e, List.map_cons, List.count_cons, eP_zero] at hcnt
    have hz : ((List.range 2047).map (· + 1) |>.map (eP E 11)).count (idF 24) = 0 := by
      simpa using hcnt
    intro k hk he
    refine (List.count_eq_zero.mp hz) ?_
    exact List.mem_map.mpr ⟨k + 1, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, he⟩
  unfold epsInjOK
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq]
  intro k hk
  rw [eprod_sound hE (Nat.beq_refl _)]
  refine ⟨validRows_unpackR _, fun he => hne k hk ?_⟩
  rw [← eprodK_eq]
  apply canon_inj (by rw [eprodK_eq]; exact eP_canon E 11 _) (idF_canon 24)
  rw [idF_unpack, ← unpackR_eq]
  exact he

theorem norm_sound {E : List Nat} {g C : Nat} (hE : lenL E = 11) (h : normK E g C = true) :
    normOK (E.map (unpackR 24)).toArray (unpackR 24 g) (unpackR 11 C) = true := by
  have hall := ctAllN_spec h
  have hE' : E.length = 11 := by rw [← lenL_eq]; exact hE
  unfold normOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨by simp [unpackR], fun i hi => ?_⟩
  have hc : (unpackR 11 C)[i]! = CFSG.KLie.CT.fget C i 11 := by
    rw [fget_eq, getElem!_pos _ i (by simp [unpackR, hi])]
    simp [unpackR]
  rw [eps_get hE' hi, hc, eprod_sound hE (Nat.beq_refl _), mul_sound (hall i hi),
    mul_sound (Nat.beq_refl _)]

private theorem powK_eq_id {M e : Nat} (h : neqId (unpackP 24 (powK 24 M e)) = false) :
    powK 24 M e = idF 24 := by
  have hrow : ∀ i < 24, rowF 24 (powK 24 M e) i = CFSG.KLie.CT.pw2 i := by
    intro i hi
    simp only [neqId, List.any_eq_false, List.mem_range, Bool.not_eq_true,
      bne_eq_false_iff_eq] at h
    apply Nat.eq_of_testBit_eq
    intro j
    have hg : (unpackP 24 (powK 24 M e))[i]?.getD 0 = rowF 24 (powK 24 M e) i := by
      simp [unpackP, hi]
    rw [pw2_eq, Nat.testBit_two_pow]
    by_cases hj : j < 24
    · have := h i hi j hj
      rw [hg] at this
      rw [this]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (rowF_lt 24 _ i)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp only [Bool.false_eq, decide_eq_false_iff_not]
      omega
  rw [powK_pack 24 M e]
  change _ = CFSG.KLie.CT.orN 24 fun i => Nat.shiftLeft (CFSG.KLie.CT.pw2 i) (Nat.mul 24 i)
  exact orN_congr 24 (fun i hi => by rw [hrow i hi])

theorem orderIs_sound {M n : Nat} (h : orderIsK 24 M n = true) : orderIs (unpackR 24 M) n = true := by
  unfold orderIsK at h
  obtain ⟨h1, h2⟩ := andB_true' h
  have hall := ctAllN_spec h2
  rw [unpackR_eq]
  unfold orderIs
  rw [← powK_unpack, Nat.eq_of_beq_eq_true h1, idF_unpack]
  simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq]
  intro m hm
  by_cases hm0 : m = 0
  · exact Or.inl hm0
  · right
    rw [← powK_unpack]
    cases hq : neqId (unpackP 24 (powK 24 M m))
    · have he := powK_eq_id hq
      have := hall m hm
      unfold CFSG.KLie.CT.orB CFSG.KLie.CT.notB at this
      have h0 : Nat.beq m 0 = false := by
        cases e : Nat.beq m 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hm0
      rw [h0, he, Nat.beq_refl] at this
      exact absurd this Bool.false_ne_true
    · rfl

private theorem trK_col (d X j : Nat) (hj : j < d) :
    CFSG.KLie.CT.orN d (fun i => nIf(CFSG.KLie.CT.bit X (Nat.add (Nat.mul d i) j),
      CFSG.KLie.CT.pw2 i, nat_lit 0)) = CFSG.KS.SporSch.PF2.colB d X j := by
  unfold CFSG.KS.SporSch.PF2.colB
  apply orN_congr
  intro i _
  have e : CFSG.KLie.CT.bit (rowF d X i) j = CFSG.KLie.CT.bit X (Nat.add (Nat.mul d i) j) := by
    rw [CFSG.KS.SporSch.PF2.bit_eq, CFSG.KS.SporSch.PF2.bit_eq, rowF, fget_eq,
      Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [hj, decide_true, Bool.true_and]
    congr 1
    change j + d * i = d * i + j
    omega
  rw [e]
  cases CFSG.KLie.CT.bit X (Nat.add (Nat.mul d i) j)
  · change 0 = 0 <<< i
    rw [Nat.zero_shiftLeft]
  · rfl

theorem tr_sound {d X T : Nat} (h : Nat.beq (trK d X) T = true) :
    transposeRows d (unpackR d X) = unpackR d T := by
  rw [← Nat.eq_of_beq_eq_true h, unpackR_eq, unpackR_eq]
  apply Array.ext (by simp [CFSG.KS.SporSch.PF2.unpackP, transposeRows])
  intro j h1 h2
  have hj : j < d := by simpa [CFSG.KS.SporSch.PF2.unpackP] using h2
  have hR : (CFSG.KS.SporSch.PF2.unpackP d (trK d X))[j] = rowF d (trK d X) j := by
    simp [CFSG.KS.SporSch.PF2.unpackP]
  simp only [transposeRows, Array.getElem_ofFn]
  rw [hR, CFSG.KS.SporSch.PF2.ofBits_eq]
  have e : rowF d (trK d X) j = CFSG.KS.SporSch.PF2.colB d X j := by
    unfold trK
    rw [rowF, CFSG.KS.SporSch.PF2.fget_orN d d _ (fun i hi => by
      rw [trK_col d X i hi]; exact CFSG.KS.SporSch.PF2.colB_lt d X i) j hj, trK_col d X j hj]
  rw [e]

end CFSG.KC.Co1F2

end
