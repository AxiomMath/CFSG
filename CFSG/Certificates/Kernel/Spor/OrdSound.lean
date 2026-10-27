module

public import CFSG.Certificates.Kernel.Orders.Cert
public import Certificates.Data.Kernel.Spor.Bytes
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.Ord

open CFSG.KC.Ord

@[expose] noncomputable def ordMat (p d w S M : Nat) : Matrix (Fin d) (Fin d) (ZMod p) :=
  fun i j => ((M / 2 ^ (S * i.val + w * j.val) % 2 ^ w : Nat) : ZMod p)

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem rawAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem strictN_eqO (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem char_beqO (c d : Char) : (c == d) = (c.toNat == d.toNat) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Char.ext (UInt32.toNat_inj.mp h)

private theorem char_leO (c d : Char) : (c ≤ d) ↔ c.toNat ≤ d.toNat := UInt32.le_iff_toNat_le

private noncomputable def dgv (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

private noncomputable def entsL (B : List Char) : List Nat :=
  (B.filter fun c => !CFSG.Blueprint.NativeSporadic.asciiWhitespace c).map dgv

private theorem ws_eq (c : Char) :
    ws c.toNat = CFSG.Blueprint.NativeSporadic.asciiWhitespace c := by
  unfold ws CFSG.Blueprint.NativeSporadic.asciiWhitespace
  rw [char_beqO, char_beqO, char_beqO, char_beqO]
  have e1 : (' ' : Char).toNat = 32 := rfl
  have e2 : ('\t' : Char).toNat = 9 := rfl
  have e3 : ('\n' : Char).toNat = 10 := rfl
  have e4 : ('\r' : Char).toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  generalize c.toNat = x
  unfold andB
  apply Bool.eq_iff_iff.mpr
  by_cases h9 : 9 ≤ x ∧ x ≤ 13
  · have h2 : Nat.ble 9 x = true := Nat.ble_eq.mpr h9.1
    have h3 : Nat.ble x 13 = true := Nat.ble_eq.mpr h9.2
    rw [h2, h3]
    simp only [true_iff, Bool.or_eq_true, beq_iff_eq]
    omega
  · have hb : Bool.rec (motive := fun _ => Bool) false (Nat.ble x 13) (Nat.ble 9 x) = false := by
      cases h2 : Nat.ble 9 x
      · rfl
      · cases h3 : Nat.ble x 13
        · rfl
        · exact absurd ⟨Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3⟩ h9
    rw [hb]
    change Nat.beq x 32 = true ↔ _
    simp only [Nat.beq_eq, Bool.or_eq_true, beq_iff_eq]
    omega

private theorem ent_eq (p : Nat) (c : Char) : ent p c.toNat = dgv c % p := by
  unfold ent dgv
  have e0 : ('0' : Char).toNat = 48 := rfl
  have e9 : ('9' : Char).toNat = 57 := rfl
  rw [e0]
  unfold andB
  have hd : ('0' ≤ c && c ≤ '9') = (Nat.ble 48 c.toNat && Nat.ble c.toNat 57) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq, char_leO, e0, e9]
  rw [hd]
  cases Nat.ble 48 c.toNat <;> cases Nat.ble c.toNat 57 <;> simp
  rfl

private noncomputable def byt (F : Nat → Nat) (lb i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (F (Nat.div i lb)) (Nat.mul 8 (Nat.mod i lb))) 255

private theorem bytes_run {F : Nat → Nat} {lb len : Nat} : ∀ (cs : List Char) (i : Nat),
    CFSG.KS.Bytes.run F lb len cs i = true →
    i + cs.length = len ∧ ∀ k < cs.length, (cs[k]!).toNat < 128 ∧ (cs[k]!).toNat = byt F lb (i + k)
  | [], i, h => ⟨by have := Nat.eq_of_beq_eq_true h; simpa using this, fun k hk => by simp at hk⟩
  | ch :: cs, i, h => by
    change bAnd(Nat.blt (Char.toNat ch) (nat_lit 128), bAnd(Nat.blt i len,
      bAnd(Nat.beq (Char.toNat ch) (byt F lb i),
        CFSG.KS.Bytes.run F lb len cs (Nat.succ i)))) = true at h
    obtain ⟨h1, h⟩ := rawAnd_true h
    obtain ⟨_, h⟩ := rawAnd_true h
    obtain ⟨h3, h4⟩ := rawAnd_true h
    obtain ⟨a, b⟩ := bytes_run cs (i + 1) h4
    refine ⟨by simp; omega, fun k hk => ?_⟩
    cases k with
    | zero =>
      simp only [List.getElem!_cons_zero, Nat.add_zero]
      exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h3⟩
    | succ k =>
      simp only [List.getElem!_cons_succ]
      have := b k (by simp at hk; omega)
      rw [show i + (k + 1) = i + 1 + k by omega]
      exact this

section Run

variable (F : Nat → Nat) (lb len p d w S RM M : Nat)

private noncomputable def gstep (St idx : Nat) : Nat :=
  if idx < len then decByte p d w S RM M St (byt F lb idx) else St

private theorem leafRun (leaf : Nat) (hlb : 0 < lb) : ∀ n ≤ lb, ∀ St,
    Nat.rec (motive := fun _ => Nat → Nat) (fun St => St)
      (fun q ih2 St => (fun idx => CFSG.KC.Loop.strictN
          (Bool.rec (motive := fun _ => Nat) St
            (decByte p d w S RM M St (Nat.land (Nat.shiftRight (F leaf)
              (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub lb (nat_lit 1)) q))) (nat_lit 255)))
            (Nat.blt idx len))
          ih2) (Nat.add (Nat.mul leaf lb) (Nat.sub (Nat.sub lb (nat_lit 1)) q))) n St =
      (List.range' (lb - n) n).foldl
        (fun St off => gstep F lb len p d w S RM M St (leaf * lb + off)) St := by
  intro n
  induction n with
  | zero => intro _ St; rfl
  | succ n ih =>
    intro hn St
    change CFSG.KC.Loop.strictN _ _ = _
    rw [strictN_eqO, ih (by omega)]
    have e : lb - (n + 1) = lb - 1 - n := by omega
    rw [e, List.range'_succ, List.foldl_cons]
    have e2 : lb - 1 - n + 1 = lb - n := by omega
    rw [e2]
    congr 1
    unfold gstep byt
    have hoff : lb - 1 - n < lb := by omega
    have hdiv : Nat.div (leaf * lb + (lb - 1 - n)) lb = leaf := by
      change (leaf * lb + (lb - 1 - n)) / lb = leaf
      rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hlb, Nat.div_eq_of_lt hoff,
        Nat.zero_add]
    have hmod : Nat.mod (leaf * lb + (lb - 1 - n)) lb = lb - 1 - n := by
      change (leaf * lb + (lb - 1 - n)) % lb = lb - 1 - n
      rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hoff]
    rw [hdiv, hmod]
    change Bool.rec (motive := fun _ => Nat) St _ (Nat.blt (leaf * lb + (lb - 1 - n)) len) = _
    cases hb : Nat.blt (leaf * lb + (lb - 1 - n)) len
    · have : ¬ leaf * lb + (lb - 1 - n) < len := fun h' => by
        rw [Nat.blt_eq.mpr h'] at hb
        exact Bool.noConfusion hb
      simp only [this, ↓reduceIte]
    · have h' : leaf * lb + (lb - 1 - n) < len := Nat.blt_eq.mp hb
      simp only [h', ↓reduceIte]
      rfl

private theorem decRun_cons (leaf : Nat) (Cs : List Nat) (St : Nat) :
    decRun F lb len p d w S RM M (leaf :: Cs) St = decRun F lb len p d w S RM M Cs
      (Nat.rec (motive := fun _ => Nat → Nat) (fun St => St)
        (fun q ih2 St => (fun idx => CFSG.KC.Loop.strictN
            (Bool.rec (motive := fun _ => Nat) St
              (decByte p d w S RM M St (Nat.land (Nat.shiftRight (F leaf)
                (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub lb (nat_lit 1)) q))) (nat_lit 255)))
              (Nat.blt idx len))
            ih2) (Nat.add (Nat.mul leaf lb) (Nat.sub (Nat.sub lb (nat_lit 1)) q))) lb St) := by
  change CFSG.KC.Loop.strictN _ _ = _
  rw [strictN_eqO]
  rfl

private theorem decRun_nil (St : Nat) : decRun F lb len p d w S RM M [] St = St := rfl

private theorem decRun_append : ∀ (xs ys : List Nat) (St : Nat),
    decRun F lb len p d w S RM M (xs ++ ys) St =
      decRun F lb len p d w S RM M ys (decRun F lb len p d w S RM M xs St)
  | [], _, _ => rfl
  | x :: xs, ys, St => by
    rw [List.cons_append, decRun_cons, decRun_cons, decRun_append xs ys]

private theorem decRun_range (hlb : 0 < lb) : ∀ (m St : Nat),
    decRun F lb len p d w S RM M (List.range m) St =
      (List.range (m * lb)).foldl (gstep F lb len p d w S RM M) St
  | 0, St => by
    rw [Nat.zero_mul]
    rfl
  | m + 1, St => by
    rw [List.range_succ, decRun_append, decRun_range hlb m, decRun_cons, decRun_nil]
    have e := leafRun F lb len p d w S RM M m hlb lb (Nat.le_refl lb)
    rw [e, Nat.sub_self, Nat.succ_mul, List.range_add, List.foldl_append, List.foldl_map,
      ← List.range_eq_range']

end Run

private noncomputable def enc (k R : Nat) : Nat :=
  Nat.add (nat_lit 3) (Nat.add (Nat.shiftLeft k (nat_lit 2)) (Nat.shiftLeft R (nat_lit 26)))

private theorem enc_val (k R : Nat) : enc k R = 3 + 4 * k + 67108864 * R := by
  unfold enc
  change 3 + (k <<< 2 + R <<< 26) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  ring

section Facts

variable {k R : Nat}

private theorem enc_land1 : Nat.land (enc k R) (nat_lit 1) = nat_lit 1 := by
  change enc k R &&& 1 = 1
  rw [Nat.and_one_is_mod, enc_val]
  omega

private theorem enc_shr1 :
    Nat.land (Nat.shiftRight (enc k R) (nat_lit 1)) (nat_lit 1) = nat_lit 1 := by
  change (enc k R >>> 1) &&& 1 = 1
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, enc_val, Nat.pow_one]
  omega

private theorem enc_bits (hk : k < 16777216) : bitsN (enc k R) (nat_lit 2) (nat_lit 24) = k := by
  unfold bitsN
  change (enc k R >>> 2) &&& ((1 <<< 24) - 1) = k
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    enc_val]
  norm_num
  omega

private theorem enc_shr26 (hk : k < 16777216) : Nat.shiftRight (enc k R) (nat_lit 26) = R := by
  change enc k R >>> 26 = R
  rw [Nat.shiftRight_eq_div_pow, enc_val]
  norm_num
  omega

end Facts

section Dec

variable (p d w S RM M : Nat)

private noncomputable def decc (St : Nat) (c : Char) : Nat := decByte p d w S RM M St c.toNat

private theorem fold_zero : ∀ cs : List Char, cs.foldl (decc p d w S RM M) 0 = 0
  | [] => rfl
  | c :: cs => by
    rw [List.foldl_cons]
    exact fold_zero cs

private theorem dec_one {b : Nat} (hb : b < 128) :
    decByte p d w S RM M 1 b = if b = 10 then 3 else 1 := by
  unfold decByte
  rw [Nat.blt_eq.mpr hb]
  by_cases h : b = 10
  · subst h
    rfl
  · have h' : Nat.beq b 10 = false := by
      cases e : Nat.beq b 10
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [h']
    simp only [h, ↓reduceIte]
    rfl

private theorem dec_enc {k R b : Nat} (hk : k < 16777216) (hb : b < 128) :
    decByte p d w S RM M (enc k R) b =
      if ws b = true then enc k R else
        if k < d * d then
          (if k % d + 1 = d then
            (if Nat.lor R (Nat.shiftLeft (ent p b) (Nat.mul w (Nat.mod k d))) =
                Nat.land (Nat.shiftRight M (Nat.mul S (Nat.div k d))) RM then enc (k + 1) 0 else 0)
          else enc (k + 1) (Nat.lor R (Nat.shiftLeft (ent p b) (Nat.mul w (Nat.mod k d)))))
        else enc k R := by
  unfold decByte
  rw [enc_land1, Nat.blt_eq.mpr hb, enc_shr1, enc_bits hk, enc_shr26 hk]
  dsimp only
  cases hws : ws b
  · have e11 : Nat.beq 1 1 = true := rfl
    rw [e11, show andB true true = true from rfl]
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h1 : Nat.blt k (Nat.mul d d)
    · have hn : ¬ k < d * d := fun h' => by
        have e : Nat.blt k (Nat.mul d d) = true := Nat.blt_eq.mpr h'
        rw [h1] at e
        exact Bool.noConfusion e
      simp only [hn, ↓reduceIte]
    · have hkd : k < d * d := Nat.blt_eq.mp h1
      simp only [hkd, ↓reduceIte]
      cases h2 : Nat.beq (Nat.succ (Nat.mod k d)) d
      · have hn : ¬ k % d + 1 = d := fun h' => by
          have e : Nat.beq (Nat.succ (Nat.mod k d)) d = true := Nat.beq_eq.mpr h'
          rw [h2] at e
          exact Bool.noConfusion e
        simp only [hn, ↓reduceIte]
        rfl
      · have hl : k % d + 1 = d := Nat.eq_of_beq_eq_true h2
        simp only [hl, ↓reduceIte]
        cases h3 : Nat.beq (Nat.lor R (Nat.shiftLeft (ent p b) (Nat.mul w (Nat.mod k d))))
            (Nat.land (Nat.shiftRight M (Nat.mul S (Nat.div k d))) RM)
        · have hn : ¬ Nat.lor R (Nat.shiftLeft (ent p b) (Nat.mul w (Nat.mod k d))) =
              Nat.land (Nat.shiftRight M (Nat.mul S (Nat.div k d))) RM := fun h' => by
            rw [h', Nat.beq_refl] at h3
            exact Bool.noConfusion h3
          simp only [hn, ↓reduceIte]
        · have hr := Nat.eq_of_beq_eq_true h3
          simp only [hr, ↓reduceIte]
          rfl
  · rfl

private theorem header : ∀ cs : List Char, (∀ c ∈ cs, c.toNat < 128) →
    Nat.land (cs.foldl (decc p d w S RM M) 1) 3 = 3 →
    cs.foldl (decc p d w S RM M) 1 =
      ((cs.dropWhile (· != '\n')).drop 1).foldl (decc p d w S RM M) 3
  | [], _, h => absurd h (by change ¬ Nat.land 1 3 = 3; decide)
  | c :: cs, ha, h => by
    have hc : c.toNat < 128 := ha c (by simp)
    have e : decc p d w S RM M 1 c = if c.toNat = 10 then 3 else 1 := dec_one p d w S RM M hc
    rw [List.foldl_cons, e] at h ⊢
    by_cases hn : c = '\n'
    · subst hn
      have e10 : ('\n' : Char).toNat = 10 := rfl
      simp only [e10, ↓reduceIte] at h ⊢
      rw [List.dropWhile_cons_of_neg (p := fun x => x != '\n') (by simp)]
      rfl
    · have h10 : c.toNat ≠ 10 := fun e' => hn (Char.ext (UInt32.toNat_inj.mp (by simpa using e')))
      simp only [h10, ↓reduceIte] at h ⊢
      rw [List.dropWhile_cons_of_pos (p := fun x => x != '\n') (by simpa using hn)]
      exact header cs (fun c' hc' => ha c' (List.mem_cons_of_mem _ hc')) h

end Dec

private theorem row_of_fld {w S d M q RM R : Nat} {g : Nat → Nat} (hS : S = d * w)
    (hRM : RM = 2 ^ S - 1) (hR : CFSG.KS.PackFld.Fld w R g) (hg : ∀ j, g j < 2 ^ w)
    (he : R = Nat.land (Nat.shiftRight M (Nat.mul S q)) RM) {j : Nat} (hj : j < d) :
    M / 2 ^ (S * q + w * j) % 2 ^ w = g j := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases ht : t < w
  · rw [← hR j t ht, he, hRM]
    change _ = ((M >>> (S * q)) &&& (2 ^ S - 1)).testBit (w * j + t)
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow, Nat.shiftRight_eq_div_pow,
      Nat.testBit_div_two_pow]
    have h1 : w * j + t < S := by
      have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hj)
      rw [Nat.mul_succ] at this
      rw [hS, Nat.mul_comm d w]
      omega
    have e : t + (S * q + w * j) = w * j + t + S * q := by omega
    simp only [ht, h1, decide_true, Bool.true_and, e]
  · rw [Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le (hg j) (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [ht]

private theorem getD_append_left' {pre X : List Nat} {n : Nat} (h : n < pre.length) :
    (pre ++ X)[n]?.getD 0 = pre[n]?.getD 0 := by
  rw [List.getElem?_append_left h]

private theorem divmod' {k d q m : Nat} (hk : k = q * d + m) (hm : m < d) :
    k / d = q ∧ k % d = m := by
  have hd : 0 < d := by omega
  exact (Nat.div_mod_unique hd).2 ⟨by rw [hk, Nat.mul_comm]; omega, hm⟩

open CFSG.KS.PackFld in
private theorem body {p d w S RM M : Nat} (hS : S = d * w) (hRM : RM = 2 ^ S - 1) (hp : 0 < p)
    (hpw : p ≤ 2 ^ w) (hdd : d * d < 16777216) : ∀ (B : List Char) (k R : Nat) (pre : List Nat),
    (∀ c ∈ B, c.toNat < 128) → pre.length = k → k ≤ d * d →
    (k < d * d → Fld w R (fun j => if j < k % d then (pre[k / d * d + j]?.getD 0) % p else 0)) →
    Nat.land (B.foldl (decc p d w S RM M) (enc k R)) 3 = 3 →
    bitsN (B.foldl (decc p d w S RM M) (enc k R)) 2 24 = d * d →
    ∀ i < d, k / d ≤ i → ∀ j < d,
      M / 2 ^ (S * i + w * j) % 2 ^ w = ((pre ++ entsL B)[i * d + j]?.getD 0) % p
  | [], k, R, pre, _, hl, hkd, _, _, hb, i, hi, hki, j, hj => by
    rw [List.foldl_nil, enc_bits (by omega)] at hb
    have : d ≤ k / d := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    omega
  | c :: B, k, R, pre, ha, hl, hkd, hinv, h3, hb, i, hi, hki, j, hj => by
    have hc : c.toNat < 128 := ha c (by simp)
    have ha' : ∀ c' ∈ B, c'.toNat < 128 := fun c' h' => ha c' (List.mem_cons_of_mem _ h')
    have hk24 : k < 16777216 := by omega
    have hd : 0 < d := by omega
    rw [List.foldl_cons] at h3 hb
    have e' : decc p d w S RM M (enc k R) c = _ := dec_enc p d w S RM M (R := R) hk24 hc
    rw [ws_eq] at e'
    by_cases hws : CFSG.Blueprint.NativeSporadic.asciiWhitespace c = true
    · simp only [hws, ↓reduceIte] at e'
      rw [e'] at h3 hb
      have he : entsL (c :: B) = entsL B := by simp [entsL, hws]
      rw [he]
      exact body hS hRM hp hpw hdd B k R pre ha' hl hkd hinv h3 hb i hi hki j hj
    · simp only [hws, Bool.false_eq_true, ↓reduceIte] at e'
      have he : entsL (c :: B) = dgv c :: entsL B := by simp [entsL, hws]
      rw [he, show pre ++ dgv c :: entsL B = (pre ++ [dgv c]) ++ entsL B by simp]
      have hl' : (pre ++ [dgv c]).length = k + 1 := by simp [hl]
      by_cases hk : k < d * d
      · simp only [hk, ↓reduceIte] at e'
        have hdm := Nat.div_add_mod' k d
        have hmd := Nat.mod_lt k hd
        have hent : ent p c.toNat < 2 ^ w := by
          rw [ent_eq]
          exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hpw
        have hF : Fld w (Nat.lor R (Nat.shiftLeft (ent p c.toNat) (Nat.mul w (Nat.mod k d))))
            (fun j => if j < k % d + 1 then ((pre ++ [dgv c])[k / d * d + j]?.getD 0) % p
              else 0) := by
          refine fld_congr (fld_or (hinv hk) (fld_shl (k % d) (fld_one hent))) ?_
          intro t
          by_cases h1 : t < k % d
          · have h2 : ¬ k % d ≤ t := by omega
            have h3' : t < k % d + 1 := by omega
            simp only [h1, h2, h3', ↓reduceIte, Nat.or_zero]
            rw [getD_append_left' (by rw [hl]; omega)]
          · by_cases h2 : t = k % d
            · subst h2
              have e1 : k / d * d + k % d = pre.length := by rw [hl]; omega
              simp only [h1, Nat.le_refl, ↓reduceIte, Nat.sub_self, Nat.lt_succ_self, Nat.zero_or]
              rw [e1, List.getElem?_concat_length, ent_eq]
              rfl
            · have h3' : ¬ t < k % d + 1 := by omega
              have h4 : t - k % d ≠ 0 := by omega
              simp only [h1, h3', h4, ↓reduceIte, Nat.zero_or]
              split <;> rfl
        have hg : ∀ t, (fun j => if j < k % d + 1 then ((pre ++ [dgv c])[k / d * d + j]?.getD 0) % p
            else 0) t < 2 ^ w := by
          intro t
          dsimp only
          split
          · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hpw
          · exact Nat.two_pow_pos w
        by_cases hlast : k % d + 1 = d
        · simp only [hlast, ↓reduceIte] at e'
          by_cases hrow : Nat.lor R (Nat.shiftLeft (ent p c.toNat) (Nat.mul w (Nat.mod k d))) =
              Nat.land (Nat.shiftRight M (Nat.mul S (Nat.div k d))) RM
          · simp only [hrow, ↓reduceIte] at e'
            rw [e'] at h3 hb
            obtain ⟨q1, m1⟩ := divmod' (k := k + 1) (d := d) (q := k / d + 1) (m := 0)
              (by rw [Nat.succ_mul]; omega) hd
            by_cases hiq : i = k / d
            · subst hiq
              have hdiv : Nat.div k d = k / d := rfl
              rw [hdiv] at hrow
              rw [row_of_fld hS hRM hF hg hrow hj]
              have hj' : j < k % d + 1 := by omega
              simp only [hj', ↓reduceIte]
              rw [getD_append_left' (pre := pre ++ [dgv c]) (X := entsL B) (by rw [hl']; omega)]
            · refine body hS hRM hp hpw hdd B (k + 1) 0 (pre ++ [dgv c]) ha' hl' (by omega)
                (fun _ => ?_) h3 hb i hi (by omega) j hj
              rw [m1]
              exact fld_congr (fld_zero w) (fun t => by simp)
          · simp only [hrow, ↓reduceIte] at e'
            rw [e', fold_zero] at h3
            exact absurd h3 (by decide)
        · simp only [hlast, ↓reduceIte] at e'
          rw [e'] at h3 hb
          obtain ⟨q1, m1⟩ := divmod' (k := k + 1) (d := d) (q := k / d) (m := k % d + 1)
            (by omega) (by omega)
          refine body hS hRM hp hpw hdd B (k + 1) _ (pre ++ [dgv c]) ha' hl' (by omega)
            (fun _ => ?_) h3 hb i hi (by omega) j hj
          rw [q1, m1]
          exact hF
      · have : d ≤ k / d := (Nat.le_div_iff_mul_le hd).2 (by omega)
        omega

theorem seed_sound {p d w S T L H CM RM ONE LV HV nb lb len M St : Nat} {F : Nat → Nat}
    {cs : List Char} {Cs : List Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    (hb : CFSG.KS.Bytes.bytesEqK cs F lb len = true)
    (hCs : Cs = List.range ((len + lb - 1) / lb))
    (hr : Nat.beq (decRun F lb len p d w S RM M Cs 1) St = true)
    (hd : seedDone d (validM p nb L H) M St = true) :
    CFSG.Blueprint.NativeSporadic.decode p d 1 (String.ofList cs) = ordMat p d w S M := by
  subst hnb
  unfold constsOK at hc
  obtain ⟨hp2, hc⟩ := andB_true hc
  obtain ⟨hS, hc⟩ := andB_true hc
  obtain ⟨_, hc⟩ := andB_true hc
  obtain ⟨hT, hc⟩ := andB_true hc
  obtain ⟨_, hc⟩ := andB_true hc
  obtain ⟨_, hc⟩ := andB_true hc
  obtain ⟨_, hc⟩ := andB_true hc
  obtain ⟨_, hc⟩ := andB_true hc
  obtain ⟨hRM, _⟩ := andB_true hc
  have hp : 2 ≤ p := Nat.le_of_ble_eq_true hp2
  have hS' : S = d * w := Nat.eq_of_beq_eq_true hS
  have hRM' : RM = 2 ^ S - 1 := by
    rw [Nat.eq_of_beq_eq_true hRM]
    change (1 <<< S) - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hpw : p ≤ 2 ^ w := by
    have h : Nat.shiftLeft p T ≤ Nat.shiftLeft 1 (Nat.sub w 1) := Nat.le_of_ble_eq_true hT
    change p <<< T ≤ 1 <<< (w - 1) at h
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul] at h
    have h1 : p ≤ p * 2 ^ T := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos T)
    have h2 : 2 ^ (w - 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  unfold CFSG.KS.Bytes.bytesEqK at hb
  obtain ⟨hlb, hrun⟩ := rawAnd_true hb
  have hlb' : 0 < lb := Nat.blt_eq.mp hlb
  obtain ⟨hlen, hbytes⟩ := bytes_run cs 0 hrun
  rw [Nat.zero_add] at hlen
  have hasc : ∀ c ∈ cs, c.toNat < 128 := by
    intro c hc'
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc'
    have := (hbytes k hk).1
    rwa [getElem!_pos cs k hk] at this
  have hSt : St = cs.foldl (decc p d w S RM M) 1 := by
    rw [← Nat.eq_of_beq_eq_true hr, hCs, decRun_range F lb len p d w S RM M hlb']
    have hm : len ≤ (len + lb - 1) / lb * lb := by
      have := Nat.div_add_mod (len + lb - 1) lb
      have := Nat.mod_lt (len + lb - 1) hlb'
      rw [Nat.mul_comm]
      omega
    rw [show (len + lb - 1) / lb * lb = len + ((len + lb - 1) / lb * lb - len) by omega,
      List.range_add, List.foldl_append, List.foldl_map]
    have htail : ∀ (l : List Nat) (X : Nat),
        l.foldl (fun x y => gstep F lb len p d w S RM M x (len + y)) X = X := by
      intro l
      induction l with
      | nil => intro X; rfl
      | cons a l ih =>
        intro X
        rw [List.foldl_cons]
        have : gstep F lb len p d w S RM M X (len + a) = X := by
          unfold gstep
          simp
        rw [this]
        exact ih X
    rw [htail]
    have hmap : (List.range len).map (fun i => cs[i]!) = cs := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        rw [List.getElem_map, List.getElem_range, getElem!_pos cs i h2]
    rw [List.foldl_ext (gstep F lb len p d w S RM M) (fun St i => decc p d w S RM M St cs[i]!) 1
      (fun X i hi => by
        have hi' : i < len := List.mem_range.mp hi
        unfold gstep decc
        rw [(hbytes i (by omega)).2, Nat.zero_add]
        simp [hi']), ← List.foldl_map (f := fun i => cs[i]!) (g := decc p d w S RM M), hmap]
  unfold seedDone at hd
  obtain ⟨hd3, hd⟩ := andB_true hd
  obtain ⟨hdb, _⟩ := andB_true hd
  have h3 : Nat.land St 3 = 3 := Nat.eq_of_beq_eq_true hd3
  have hbits : bitsN St 2 24 = d * d := Nat.eq_of_beq_eq_true hdb
  have hdd : d * d < 16777216 := by
    rw [← hbits]
    unfold bitsN
    change (St >>> 2) &&& ((1 <<< 24) - 1) < _
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  rw [hSt] at h3 hbits
  have hH := header p d w S RM M cs hasc h3
  rw [hH] at h3 hbits
  have e3 : enc 0 0 = 3 := by rw [enc_val]
  have hrows := body hS' hRM' (by omega) hpw hdd ((cs.dropWhile (· != '\n')).drop 1) 0 0 []
    (fun c hc' => hasc c ((List.dropWhile_sublist _).subset (List.mem_of_mem_drop hc'))) rfl
    (Nat.zero_le _)
    (fun _ => CFSG.KS.PackFld.fld_congr (CFSG.KS.PackFld.fld_zero w) (fun t => by simp))
    (by rw [e3]; exact h3)
    (by rw [e3]; exact hbits)
  funext i j
  unfold CFSG.Blueprint.NativeSporadic.decode ordMat
  simp only [↓reduceIte, String.toList_ofList]
  have := hrows i.val i.isLt (by simp) j.val j.isLt
  rw [List.nil_append] at this
  change ((entsL ((cs.dropWhile (· != '\n')).drop 1))[i.val * d + j.val]?.getD 0 : ZMod p) = _
  rw [this, ZMod.natCast_mod]

section MulR

open CFSG.KS.PackFld

private theorem dm_eq {d i j : Nat} (hj : j < d) : (d * i + j) / d = i ∧ (d * i + j) % d = j := by
  have hd : 0 < d := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

private theorem idx_lt {d i j : Nat} (hi : i < d) (hj : j < d) : d * i + j < d * d := by
  have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at this
  omega

private noncomputable def pk (w n : Nat) (g : Nat → Nat) : Nat :=
  ∑ t ∈ Finset.range n, g t * 2 ^ (w * t)

@[expose] noncomputable def lane (w X t : Nat) : Nat := X / 2 ^ (w * t) % 2 ^ w

@[expose] def Canon (p d w X : Nat) : Prop := X < 2 ^ (w * (d * d)) ∧ ∀ t < d * d, lane w X t < p

private theorem pk_succ (w n : Nat) (g : Nat → Nat) :
    pk w (n + 1) g = pk w n g + g n * 2 ^ (w * n) :=
  Finset.sum_range_succ _ _

private theorem pk_congr {w n : Nat} {f g : Nat → Nat} (h : ∀ t < n, f t = g t) :
    pk w n f = pk w n g :=
  Finset.sum_congr rfl fun t ht => by rw [h t (Finset.mem_range.1 ht)]

private theorem pk_add (w n : Nat) (f g : Nat → Nat) :
    pk w n f + pk w n g = pk w n (fun t => f t + g t) := by
  unfold pk
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => (Nat.add_mul _ _ _).symm

private theorem pk_sub {w n : Nat} {f g : Nat → Nat} (h : ∀ t < n, g t ≤ f t) :
    pk w n f - pk w n g = pk w n (fun t => f t - g t) := by
  have e : pk w n g + pk w n (fun t => f t - g t) = pk w n f := by
    rw [pk_add]
    exact pk_congr fun t ht => Nat.add_sub_cancel' (h t ht)
  omega

private theorem pk_mul (w n c : Nat) (f : Nat → Nat) :
    pk w n f * c = pk w n (fun t => f t * c) := by
  unfold pk
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => Nat.mul_right_comm _ _ _

private theorem pk_lt {w n : Nat} {g : Nat → Nat} (hg : ∀ t < n, g t < 2 ^ w) :
    pk w n g < 2 ^ (w * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    rw [pk_succ]
    have h1 := ih fun t ht => hg t (by omega)
    have h2 : g n + 1 ≤ 2 ^ w := hg n (by omega)
    have h3 := Nat.mul_le_mul_right (2 ^ (w * n)) h2
    have e : 2 ^ (w * (n + 1)) = 2 ^ w * 2 ^ (w * n) := by
      rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
    rw [e]
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

private theorem pk_rows (w d : Nat) (G : Nat → Nat) : ∀ m, pk w (d * m) G =
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range d, G (d * i + j) * 2 ^ (w * (d * i + j))
  | 0 => by simp [pk]
  | m + 1 => by
    rw [Finset.sum_range_succ, ← pk_rows w d G m, Nat.mul_succ]
    unfold pk
    rw [Finset.sum_range_add]

private theorem fld_pk {w n : Nat} {g : Nat → Nat} (hg : ∀ t < n, g t < 2 ^ w) :
    Fld w (pk w n g) (fun t => if t < n then g t else 0) := by
  induction n with
  | zero => exact fld_congr (fld_zero w) fun t => by simp
  | succ n ih =>
    have ih' := ih fun t ht => hg t (by omega)
    have hl := pk_lt (w := w) (n := n) (g := g) fun t ht => hg t (by omega)
    have e : pk w (n + 1) g = g n <<< (w * n) ||| pk w n g := by
      rw [pk_succ, ← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq, Nat.add_comm]
    rw [e]
    refine fld_congr (fld_or (fld_shl n (fld_one (hg n (by omega)))) ih') fun t => ?_
    rcases Nat.lt_trichotomy t n with h | h | h
    · have h1 : ¬ n ≤ t := by omega
      have h2 : t < n + 1 := by omega
      simp [h, h1, h2]
    · subst h
      simp
    · have h1 : n ≤ t := by omega
      have h2 : t - n ≠ 0 := by omega
      have h3 : ¬ t < n := by omega
      have h4 : ¬ t < n + 1 := by omega
      simp [h1, h2, h3, h4]

private theorem fld_unique {w X Y : Nat} {g : Nat → Nat} (hw : 0 < w) (hX : Fld w X g)
    (hY : Fld w Y g) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro b
  have hb : b = w * (b / w) + b % w := (Nat.div_add_mod b w).symm
  rw [hb, hX _ _ (Nat.mod_lt _ hw), hY _ _ (Nat.mod_lt _ hw)]

private theorem pk_of_fld {w n X : Nat} {g : Nat → Nat} (hw : 0 < w)
    (hX : Fld w X (fun t => if t < n then g t else 0)) (hg : ∀ t < n, g t < 2 ^ w) :
    X = pk w n g :=
  fld_unique hw hX (fld_pk hg)

private theorem fld_and {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A &&& B) (fun i => g i &&& h i) := by
  intro i k hk
  rw [Nat.testBit_and, hA i k hk, hB i k hk, Nat.testBit_and]

private theorem fld_shr {w A : Nat} {g : Nat → Nat} (k : Nat) (hA : Fld w A g) :
    Fld w (A >>> (w * k)) (fun i => g (i + k)) := by
  intro i b hb
  rw [Nat.testBit_shiftRight, ← hA (i + k) b hb, Nat.mul_add]
  congr 1
  omega

private theorem fld_lane (w X : Nat) : Fld w X (fun t => lane w X t) := by
  intro i k hk
  unfold lane
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm k]
  simp [hk]

private theorem lane_of_fld {w X s : Nat} {g : Nat → Nat} (hX : Fld w X g) (hg : g s < 2 ^ w) :
    lane w X s = g s := by
  apply Nat.eq_of_testBit_eq
  intro k
  unfold lane
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hk : k < w
  · rw [Nat.add_comm, hX s k hk]
    simp [hk]
  · rw [Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hk]

private theorem lane_pk {w n s : Nat} {g : Nat → Nat} (hg : ∀ t < n, g t < 2 ^ w) (hs : s < n) :
    lane w (pk w n g) s = g s := by
  rw [lane_of_fld (fld_pk hg) (by simp only [hs, ↓reduceIte]; exact hg s hs)]
  simp [hs]

private theorem pk_lane {w n X : Nat} (hw : 0 < w) (hX : X < 2 ^ (w * n)) :
    X = pk w n (lane w X) := by
  refine pk_of_fld hw (fld_congr (fld_lane w X) fun t => ?_)
    fun t _ => Nat.mod_lt _ (Nat.two_pow_pos w)
  by_cases ht : t < n
  · simp [ht]
  · have h : X < 2 ^ (w * t) :=
      Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left w (by omega)))
    simp only [ht, ↓reduceIte]
    unfold lane
    rw [Nat.div_eq_of_lt h, Nat.zero_mod]

private theorem canon_pk {p d w : Nat} {g : Nat → Nat} (hg : ∀ t < d * d, g t < p)
    (hp : p ≤ 2 ^ w) : Canon p d w (pk w (d * d) g) := by
  have hg' : ∀ t < d * d, g t < 2 ^ w := fun t ht => Nat.lt_of_lt_of_le (hg t ht) hp
  refine ⟨pk_lt hg', fun t ht => ?_⟩
  rw [lane_pk hg' ht]
  exact hg t ht

private theorem testBit_top {y k : Nat} (hy : y < 2 * 2 ^ k) :
    y.testBit k = decide (2 ^ k ≤ y) := by
  by_cases h : 2 ^ k ≤ y
  · obtain ⟨r, rfl⟩ : ∃ r, y = 2 ^ k + r := ⟨y - 2 ^ k, by omega⟩
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)]
    simp
  · rw [Nat.testBit_lt_two_pow (by omega)]
    simp [h]

private theorem or_top {a k : Nat} (ha : a < 2 ^ k) : a ||| 2 ^ k = a + 2 ^ k := by
  have h := Nat.shiftLeft_add_eq_or_of_lt ha 1
  rw [Nat.shiftLeft_eq, Nat.one_mul] at h
  rw [Nat.lor_comm, ← h, Nat.add_comm]

private theorem and_top {y k : Nat} (hy : y < 2 * 2 ^ k) :
    y &&& 2 ^ k = if 2 ^ k ≤ y then 2 ^ k else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hj : k = j
  · subst hj
    rw [testBit_top hy]
    by_cases h : 2 ^ k ≤ y <;> simp [h]
  · by_cases h : 2 ^ k ≤ y <;> simp [h, hj]

section Lanes

variable {w n : Nat}

private theorem two_pow_pred (hw : 0 < w) : 2 ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]

private theorem or_H (hw : 0 < w) {f : Nat → Nat} (hf : ∀ t < n, f t < 2 ^ (w - 1)) :
    pk w n f ||| pk w n (fun _ => 2 ^ (w - 1)) = pk w n (fun t => f t + 2 ^ (w - 1)) := by
  have e2 := two_pow_pred hw
  have h0 := Nat.two_pow_pos (w - 1)
  have hp : (2 : Nat) ^ (w - 1) < 2 ^ w := by omega
  refine pk_of_fld hw (fld_congr (fld_or (fld_pk fun t ht => (by have := hf t ht; omega))
    (fld_pk (n := n) fun _ _ => hp)) fun t => ?_) fun t ht => by have := hf t ht; omega
  by_cases ht : t < n
  · simp only [ht, ↓reduceIte]
    exact or_top (hf t ht)
  · simp [ht]

private theorem top_H (hw : 0 < w) {f : Nat → Nat} {c : Nat} (hf : ∀ t < n, f t < 2 ^ (w - 1))
    (hc : c ≤ 2 ^ (w - 1)) :
    ((pk w n f ||| pk w n (fun _ => 2 ^ (w - 1))) - c * pk w n (fun _ => 1)) &&&
        pk w n (fun _ => 2 ^ (w - 1)) =
      pk w n (fun t => if c ≤ f t then 2 ^ (w - 1) else 0) := by
  have e2 := two_pow_pred hw
  have h0 := Nat.two_pow_pos (w - 1)
  rw [or_H hw hf, Nat.mul_comm, pk_mul, pk_sub (fun t _ => by omega)]
  refine pk_of_fld hw (fld_congr (fld_and (fld_pk (fun t ht => by have := hf t ht; omega))
    (fld_pk (n := n) (g := fun _ => 2 ^ (w - 1)) (fun _ _ => by omega))) fun t => ?_)
    (fun t _ => by split <;> omega)
  by_cases ht : t < n
  · simp only [ht, ↓reduceIte, Nat.one_mul]
    have := hf t ht
    rw [and_top (by omega)]
    by_cases hcf : c ≤ f t
    · have h1 : 2 ^ (w - 1) ≤ f t + 2 ^ (w - 1) - c := by omega
      simp [hcf, h1]
    · have h1 : ¬ 2 ^ (w - 1) ≤ f t + 2 ^ (w - 1) - c := by omega
      simp [hcf, h1]
  · simp [ht]

private theorem csub_pk (hw : 0 < w) {f : Nat → Nat} {c : Nat}
    (hf : ∀ t < n, f t < 2 ^ (w - 1)) (hc : c ≤ 2 ^ (w - 1)) :
    csub w (pk w n (fun _ => 1)) (pk w n (fun _ => 2 ^ (w - 1))) c (pk w n f) =
      pk w n (fun t => if c ≤ f t then f t - c else f t) := by
  unfold csub
  change pk w n f - ((((pk w n f ||| pk w n (fun _ => 2 ^ (w - 1))) - c * pk w n (fun _ => 1)) &&&
    pk w n (fun _ => 2 ^ (w - 1))) >>> (w - 1)) * c = _
  rw [top_H hw hf hc, Nat.shiftRight_eq_div_pow]
  have e : pk w n (fun t => if c ≤ f t then 2 ^ (w - 1) else 0) =
      pk w n (fun t => if c ≤ f t then 1 else 0) * 2 ^ (w - 1) := by
    rw [pk_mul]
    exact pk_congr fun t _ => by split <;> simp
  rw [e, Nat.mul_div_cancel _ (Nat.two_pow_pos _), pk_mul,
    pk_sub (fun t _ => by split <;> simp_all)]
  exact pk_congr fun t _ => by split <;> simp

private theorem rec_succN (x : Nat) (s : Nat → Nat → Nat) (m : Nat) :
    Nat.rec (motive := fun _ => Nat) x s (m + 1) = s m (Nat.rec (motive := fun _ => Nat) x s m) :=
  rfl

private theorem redP_pk (hw : 0 < w) {p T : Nat} {f : Nat → Nat} (hT : p * 2 ^ T ≤ 2 ^ (w - 1))
    (hf : ∀ t < n, f t < 2 ^ (w - 1)) (hf2 : ∀ t < n, f t < p * 2 ^ (T + 1)) :
    redP w (pk w n (fun _ => 1)) (pk w n (fun _ => 2 ^ (w - 1))) p T (pk w n f) =
      pk w n (fun t => f t % p) := by
  have key : ∀ m ≤ T + 1, ∃ g : Nat → Nat,
      Nat.rec (motive := fun _ => Nat) (pk w n f)
        (fun i acc => csub w (pk w n (fun _ => 1)) (pk w n (fun _ => 2 ^ (w - 1)))
          (Nat.shiftLeft p (Nat.sub T i)) acc) m = pk w n g ∧
      ∀ t < n, g t % p = f t % p ∧ g t < p * 2 ^ (T + 1 - m) ∧ g t < 2 ^ (w - 1) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨f, rfl, fun t ht => ⟨rfl, hf2 t ht, hf t ht⟩⟩
    | succ m ih =>
      intro hm
      obtain ⟨g, hg, hb⟩ := ih (by omega)
      have hc : Nat.shiftLeft p (Nat.sub T m) = p * 2 ^ (T - m) := shl_eq p (T - m)
      have hcle : p * 2 ^ (T - m) ≤ 2 ^ (w - 1) :=
        Nat.le_trans (Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by omega) (by omega))) hT
      refine ⟨fun t => if p * 2 ^ (T - m) ≤ g t then g t - p * 2 ^ (T - m) else g t, ?_,
        fun t ht => ?_⟩
      · rw [rec_succN, hg, hc]
        exact csub_pk hw (fun t ht => (hb t ht).2.2) hcle
      · obtain ⟨h1, h2, h3⟩ := hb t ht
        have e : p * 2 ^ (T + 1 - m) = 2 * (p * 2 ^ (T - m)) := by
          have e' : T + 1 - m = (T - m) + 1 := by omega
          rw [e', Nat.pow_succ]
          ring
        have e' : T + 1 - (m + 1) = T - m := by omega
        rw [e']
        by_cases hgc : p * 2 ^ (T - m) ≤ g t
        · simp only [hgc, ↓reduceIte]
          refine ⟨?_, by omega, by omega⟩
          have e3 : (g t - p * 2 ^ (T - m) + 2 ^ (T - m) * p) % p =
              (g t - p * 2 ^ (T - m)) % p :=
            Nat.add_mul_mod_self_right _ _ _
          rw [Nat.mul_comm (2 ^ (T - m)) p, Nat.sub_add_cancel hgc] at e3
          rw [← e3, h1]
        · simp only [hgc, ↓reduceIte]
          exact ⟨h1, by omega, h3⟩
  obtain ⟨g, hg, hb⟩ := key (T + 1) (Nat.le_refl _)
  refine hg.trans (pk_congr fun t ht => ?_)
  obtain ⟨h1, h2, _⟩ := hb t ht
  rw [← h1, Nat.mod_eq_of_lt (by simpa using h2)]

end Lanes

private theorem rep1_eq {s m : Nat} (hs : 0 < s ∨ m = 0) :
    rep1 s m = ∑ i ∈ Finset.range m, 2 ^ (s * i) := by
  rcases hs with hs | rfl
  · have key : ∀ m, (2 ^ s - 1) * ∑ i ∈ Finset.range m, 2 ^ (s * i) + 1 = 2 ^ (s * m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, Nat.mul_add, Nat.add_right_comm, ih, Nat.mul_succ, Nat.pow_add]
        obtain ⟨q, hq⟩ : ∃ q, 2 ^ s = q + 1 :=
          ⟨2 ^ s - 1, by have := Nat.one_le_two_pow (n := s); omega⟩
        rw [hq, Nat.add_sub_cancel]
        ring
    have h2 : 2 ≤ 2 ^ s := by
      have := Nat.pow_le_pow_right (n := 2) (by omega) hs
      simpa using this
    unfold rep1
    change (1 <<< (s * m) - 1) / (1 <<< s - 1) = _
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, ← key m, Nat.add_sub_cancel]
    exact Nat.mul_div_cancel_left _ (by omega)
  · unfold rep1
    change (1 <<< (s * 0) - 1) / (1 <<< s - 1) = _
    simp

private theorem consts_facts {p w S d T L H CM RM ONE LV HV : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) :
    2 ≤ p ∧ S = d * w ∧ 0 < w ∧ d * ((p - 1) * (p - 1)) < 2 ^ (w - 1) ∧
      p * 2 ^ T ≤ 2 ^ (w - 1) ∧ 2 ^ (w - 1) ≤ p * 2 ^ (T + 1) ∧ L = pk w (d * d) (fun _ => 1) ∧
      H = pk w (d * d) (fun _ => 2 ^ (w - 1)) ∧
      CM = pk w (d * d) (fun t => if t % d = 0 then 2 ^ w - 1 else 0) ∧ RM = 2 ^ (w * d) - 1 ∧
      ONE = pk w (d * d) (fun t => if t / d = t % d then 1 else 0) := by
  unfold constsOK at hc
  obtain ⟨hp2, hc⟩ := andB_true hc
  obtain ⟨hS, hc⟩ := andB_true hc
  obtain ⟨hdp, hc⟩ := andB_true hc
  obtain ⟨hT, hc⟩ := andB_true hc
  obtain ⟨hT2, hc⟩ := andB_true hc
  obtain ⟨hL, hc⟩ := andB_true hc
  obtain ⟨hH, hc⟩ := andB_true hc
  obtain ⟨hCM, hc⟩ := andB_true hc
  obtain ⟨hRM, hc⟩ := andB_true hc
  obtain ⟨hONE, -⟩ := andB_true hc
  have hp : 2 ≤ p := Nat.le_of_ble_eq_true hp2
  have hS' : S = d * w := Nat.eq_of_beq_eq_true hS
  have hT' : p * 2 ^ T ≤ 2 ^ (w - 1) := by
    have h : p <<< T ≤ 1 <<< (w - 1) := Nat.le_of_ble_eq_true hT
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul] at h
    exact h
  have hT2' : 2 ^ (w - 1) ≤ p * 2 ^ (T + 1) := by
    have h : 1 <<< (w - 1) ≤ p <<< (T + 1) := Nat.le_of_ble_eq_true hT2
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul] at h
    exact h
  have hdp' : d * ((p - 1) * (p - 1)) < 2 ^ (w - 1) := by
    have h : d * ((p - 1) * (p - 1)) < 1 <<< (w - 1) := Nat.blt_eq.mp hdp
    rw [Nat.shiftLeft_eq, Nat.one_mul] at h
    exact h
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · have : p ≤ p * 2 ^ T := Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)
      rw [h0, Nat.zero_sub, Nat.pow_zero] at hT'
      omega
    · exact h0
  have hL' : L = pk w (d * d) (fun _ => 1) := by
    have h : L = rep1 w (d * d) := Nat.eq_of_beq_eq_true hL
    rw [h, rep1_eq (Or.inl hw)]
    simp [pk]
  have hH' : H = pk w (d * d) (fun _ => 2 ^ (w - 1)) := by
    have h : H = L <<< (w - 1) := Nat.eq_of_beq_eq_true hH
    rw [h, Nat.shiftLeft_eq, hL', pk_mul]
    exact pk_congr fun _ _ => Nat.one_mul _
  have hCM' : CM = pk w (d * d) (fun t => if t % d = 0 then 2 ^ w - 1 else 0) := by
    have h : CM = (1 <<< w - 1) * rep1 S d := Nat.eq_of_beq_eq_true hCM
    rw [h, Nat.shiftLeft_eq, Nat.one_mul, hS']
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      rw [rep1_eq (Or.inr rfl)]
      simp [pk]
    rw [rep1_eq (Or.inl (Nat.mul_pos hd hw)), pk_rows, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single 0]
    · have e : d * w * i = w * (d * i + 0) := by ring
      have e2 : (d * i + 0) % d = 0 := by simp
      rw [e, e2, ite_eq_left rfl]
    · intro j hj hj0
      rw [(dm_eq (i := i) (Finset.mem_range.1 hj)).2, ite_eq_right hj0, Nat.zero_mul]
    · intro h0
      exact absurd (Finset.mem_range.2 hd) h0
  have hRM' : RM = 2 ^ (w * d) - 1 := by
    have h : RM = 1 <<< S - 1 := Nat.eq_of_beq_eq_true hRM
    rw [h, Nat.shiftLeft_eq, Nat.one_mul, hS', Nat.mul_comm d w]
  have hONE' : ONE = pk w (d * d) (fun t => if t / d = t % d then 1 else 0) := by
    have h : ONE = rep1 (S + w) d := Nat.eq_of_beq_eq_true hONE
    rw [h, rep1_eq (Or.inl (by omega)), pk_rows, hS']
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [Finset.sum_eq_single i]
    · obtain ⟨e1, e2⟩ := dm_eq (i := i) hi'
      have e : (d * w + w) * i = w * (d * i + i) := by ring
      rw [e1, e2, ite_eq_left rfl, e, Nat.one_mul]
    · intro j hj hji
      obtain ⟨e1, e2⟩ := dm_eq (i := i) (Finset.mem_range.1 hj)
      rw [e1, e2, ite_eq_right (Ne.symm hji), Nat.zero_mul]
    · intro h0
      exact absurd hi h0
  exact ⟨hp, hS', hw, hdp', hT', hT2', hL', hH', hCM', hRM', hONE'⟩

private theorem mulU_eq (w S d CM RM A B : Nat) : mulU w S d CM RM A B =
    ∑ k ∈ Finset.range d, ((A >>> (w * k)) &&& CM) * ((B >>> (S * k)) &&& RM) := by
  unfold mulU
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

private theorem col_eq {w d k : Nat} {a : Nat → Nat} (hw : 0 < w) (ha : ∀ t < d * d, a t < 2 ^ w)
    (hk : k < d) :
    (pk w (d * d) a >>> (w * k)) &&& pk w (d * d) (fun t => if t % d = 0 then 2 ^ w - 1 else 0) =
      ∑ i ∈ Finset.range d, a (d * i + k) * 2 ^ (w * (d * i)) := by
  have hpos := Nat.two_pow_pos w
  have hm : ∀ t < d * d, (if t % d = 0 then 2 ^ w - 1 else 0) < 2 ^ w :=
    fun t _ => by split <;> omega
  have hlt : ∀ t < d * d, t % d = 0 → t + k < d * d := by
    intro t ht h0
    have hd : 0 < d := by omega
    have h1 := Nat.div_add_mod t d
    have h2 : t / d < d := (Nat.div_lt_iff_lt_mul hd).2 ht
    have := idx_lt h2 hk
    rw [h0] at h1
    omega
  have hF : Fld w ((pk w (d * d) a >>> (w * k)) &&&
      pk w (d * d) (fun t => if t % d = 0 then 2 ^ w - 1 else 0))
      (fun t => if t < d * d then (if t % d = 0 then a (t + k) else 0) else 0) := by
    refine fld_congr (fld_and (fld_shr k (fld_pk ha)) (fld_pk hm)) fun t => ?_
    by_cases ht : t < d * d
    · by_cases h0 : t % d = 0
      · have h3 := hlt t ht h0
        simp only [ht, h0, h3, ↓reduceIte]
        rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (ha _ h3)]
      · simp [ht, h0]
    · simp [ht]
  have hb : ∀ t < d * d, (if t % d = 0 then a (t + k) else 0) < 2 ^ w := by
    intro t ht
    by_cases h0 : t % d = 0
    · rw [ite_eq_left h0]
      exact ha _ (hlt t ht h0)
    · rw [ite_eq_right h0]
      exact hpos
  rw [pk_of_fld hw hF hb, pk_rows]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hd : 0 < d := by have := Finset.mem_range.1 hi; omega
  rw [Finset.sum_eq_single 0]
  · have e2 : (d * i + 0) % d = 0 := by simp
    rw [e2, ite_eq_left rfl, Nat.add_zero]
  · intro j hj hj0
    rw [(dm_eq (i := i) (Finset.mem_range.1 hj)).2, ite_eq_right hj0, Nat.zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.2 hd) h0

private theorem fld_RM (w d : Nat) :
    Fld w (2 ^ (w * d) - 1) (fun t => if t < d then 2 ^ w - 1 else 0) := by
  intro i k hk
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hi : i < d
  · have h1 : w * i + k < w * d := by
      have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hi)
      rw [Nat.mul_succ] at this
      omega
    simp only [hi, ↓reduceIte, Nat.testBit_two_pow_sub_one, h1, hk]
  · have h1 : ¬ w * i + k < w * d := by
      have := Nat.mul_le_mul_left w (Nat.le_of_not_lt hi)
      omega
    simp [hi, h1]

private theorem row_eq {w d k : Nat} {b : Nat → Nat} (hw : 0 < w) (hb : ∀ t < d * d, b t < 2 ^ w)
    (hk : k < d) :
    (pk w (d * d) b >>> (d * w * k)) &&& (2 ^ (w * d) - 1) = pk w d (fun j => b (d * k + j)) := by
  have e : d * w * k = w * (d * k) := by ring
  rw [e]
  refine pk_of_fld hw (fld_congr (fld_and (fld_shr (d * k) (fld_pk hb)) (fld_RM w d)) fun t => ?_)
    fun t ht => hb _ (by have := idx_lt hk ht; omega)
  by_cases ht : t < d
  · have h3 : t + d * k < d * d := by have := idx_lt hk ht; omega
    simp only [ht, h3, ↓reduceIte]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hb _ h3), Nat.add_comm]
  · simp [ht]

private noncomputable def prodL (d : Nat) (a b : Nat → Nat) (t : Nat) : Nat :=
  ∑ k ∈ Finset.range d, a (d * (t / d) + k) * b (d * k + t % d)

private theorem mulU_pk {w d : Nat} {a b : Nat → Nat} (hw : 0 < w)
    (ha : ∀ t < d * d, a t < 2 ^ w) (hb : ∀ t < d * d, b t < 2 ^ w) :
    mulU w (d * w) d (pk w (d * d) (fun t => if t % d = 0 then 2 ^ w - 1 else 0))
        (2 ^ (w * d) - 1) (pk w (d * d) a) (pk w (d * d) b) = pk w (d * d) (prodL d a b) := by
  rw [mulU_eq]
  calc _ = ∑ k ∈ Finset.range d, ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range d,
        a (d * i + k) * b (d * k + j) * 2 ^ (w * (d * i + j)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.1 hk
        rw [col_eq hw ha hk', row_eq hw hb hk', Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold pk
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.mul_add w, Nat.pow_add]
        ring
    _ = ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range d, ∑ k ∈ Finset.range d,
        a (d * i + k) * b (d * k + j) * 2 ^ (w * (d * i + j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        rw [pk_rows]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨e1, e2⟩ := dm_eq (i := i) (Finset.mem_range.1 hj)
        unfold prodL
        rw [e1, e2, Finset.sum_mul]

private theorem ordMat_pk {p d w : Nat} {g : Nat → Nat} (hg : ∀ t < d * d, g t < 2 ^ w)
    (i j : Fin d) :
    ordMat p d w (d * w) (pk w (d * d) g) i j = ((g (d * i.val + j.val) : Nat) : ZMod p) := by
  unfold ordMat
  have e : d * w * i.val + w * j.val = w * (d * i.val + j.val) := by ring
  rw [e]
  have h := lane_pk (w := w) hg (idx_lt i.isLt j.isLt)
  unfold lane at h
  rw [h]

theorem mulR_sound {p w S d T L H CM RM ONE LV HV A B : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hA : Canon p d w A)
    (hB : Canon p d w B) :
    Canon p d w (mulR p w S d T L H CM RM A B) ∧
      ordMat p d w S (mulR p w S d T L H CM RM A B) = ordMat p d w S A * ordMat p d w S B := by
  obtain ⟨hp, hS, hw, hdp, hT, hT2, hL, hH, hCM, hRM, -⟩ := consts_facts hc
  subst hS hL hH hCM hRM
  obtain ⟨a, rfl, ha⟩ : ∃ a, A = pk w (d * d) a ∧ ∀ t < d * d, a t < p :=
    ⟨lane w A, pk_lane hw hA.1, hA.2⟩
  obtain ⟨b, rfl, hb⟩ : ∃ b, B = pk w (d * d) b ∧ ∀ t < d * d, b t < p :=
    ⟨lane w B, pk_lane hw hB.1, hB.2⟩
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  have hpw : p ≤ 2 ^ w := by omega
  have ha' : ∀ t < d * d, a t < 2 ^ w := fun t ht => Nat.lt_of_lt_of_le (ha t ht) hpw
  have hb' : ∀ t < d * d, b t < 2 ^ w := fun t ht => Nat.lt_of_lt_of_le (hb t ht) hpw
  have hC : ∀ t < d * d, prodL d a b t ≤ d * ((p - 1) * (p - 1)) := by
    intro t ht
    have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h
        simp at ht
      · exact h
    have h1 : t / d < d := (Nat.div_lt_iff_lt_mul hd).2 ht
    have h2 : t % d < d := Nat.mod_lt _ hd
    unfold prodL
    calc _ ≤ ∑ _k ∈ Finset.range d, (p - 1) * (p - 1) :=
          Finset.sum_le_sum fun k hk => by
            have hk' := Finset.mem_range.1 hk
            have x1 := ha _ (idx_lt h1 hk')
            have x2 := hb _ (idx_lt hk' h2)
            exact Nat.mul_le_mul (by omega) (by omega)
      _ = d * ((p - 1) * (p - 1)) := by simp
  have e : mulR p w (d * w) d T (pk w (d * d) fun _ => 1) (pk w (d * d) fun _ => 2 ^ (w - 1))
      (pk w (d * d) fun t => if t % d = 0 then 2 ^ w - 1 else 0) (2 ^ (w * d) - 1)
      (pk w (d * d) a) (pk w (d * d) b) = pk w (d * d) (fun t => prodL d a b t % p) := by
    unfold mulR
    rw [mulU_pk hw ha' hb']
    exact redP_pk hw hT (fun t ht => by have := hC t ht; omega)
      (fun t ht => by have := hC t ht; omega)
  have hCp : ∀ t < d * d, prodL d a b t % p < p := fun t _ => Nat.mod_lt _ (by omega)
  rw [e]
  refine ⟨canon_pk hCp hpw, ?_⟩
  funext i j
  rw [Matrix.mul_apply, ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (hCp t ht) hpw)]
  simp only [ordMat_pk ha', ordMat_pk hb']
  rw [ZMod.natCast_mod]
  obtain ⟨e1, e2⟩ := dm_eq (i := i.val) j.isLt
  unfold prodL
  rw [e1, e2, Nat.cast_sum, Finset.sum_range]
  simp only [Nat.cast_mul]

theorem one_sound {p w S d T L H CM RM ONE LV HV : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) :
    Canon p d w ONE ∧ ordMat p d w S ONE = 1 := by
  obtain ⟨hp, hS, hw, -, hT, -, -, -, -, -, hONE⟩ := consts_facts hc
  subst hS hONE
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  have hpw : p ≤ 2 ^ w := by omega
  have hg : ∀ t < d * d, (if t / d = t % d then 1 else 0) < p := fun t _ => by split <;> omega
  refine ⟨canon_pk hg hpw, ?_⟩
  funext i j
  rw [ordMat_pk (fun t ht => Nat.lt_of_lt_of_le (hg t ht) hpw)]
  obtain ⟨e1, e2⟩ := dm_eq (i := i.val) j.isLt
  rw [e1, e2, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem validM_canon {p w S d T L H CM RM ONE LV HV X : Nat}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hX : validM p (d * S) L H X = true) :
    Canon p d w X := by
  obtain ⟨hp, hS, hw, -, hT, -, hL, hH, -, -, -⟩ := consts_facts hc
  subst hS hL hH
  unfold validM at hX
  obtain ⟨h1, hX⟩ := andB_true hX
  obtain ⟨h2, h3⟩ := andB_true hX
  have hp2 : p ≤ 2 ^ (w - 1) :=
    Nat.le_trans (Nat.le_mul_of_pos_right p (Nat.two_pow_pos T)) hT
  have e2 := two_pow_pred hw
  have hlt : X < 2 ^ (w * (d * d)) := by
    have h1' : X >>> (d * (d * w)) = 0 := Nat.eq_of_beq_eq_true h1
    rw [Nat.shiftRight_eq_div_pow] at h1'
    have e : d * (d * w) = w * (d * d) := by ring
    rw [e] at h1'
    rcases Nat.div_eq_zero_iff.1 h1' with h | h
    · exact absurd h (Nat.two_pow_pos _).ne'
    · exact h
  obtain ⟨a, rfl, ha⟩ : ∃ a, X = pk w (d * d) a ∧ ∀ t < d * d, a t < 2 ^ w :=
    ⟨lane w X, pk_lane hw hlt, fun t _ => Nat.mod_lt _ (Nat.two_pow_pos w)⟩
  have h0 := Nat.two_pow_pos (w - 1)
  have hHb : ∀ t < d * d, (2 : Nat) ^ (w - 1) < 2 ^ w := fun _ _ => by omega
  have htop : ∀ t < d * d, a t < 2 ^ (w - 1) := by
    intro t ht
    have h2' : pk w (d * d) a &&& pk w (d * d) (fun _ => 2 ^ (w - 1)) = 0 :=
      Nat.eq_of_beq_eq_true h2
    have hF := fld_and (fld_pk ha) (fld_pk hHb)
    rw [h2'] at hF
    have hb := hF t (w - 1) (by omega)
    rw [Nat.zero_testBit] at hb
    simp only [ht, ↓reduceIte] at hb
    have ha2 : a t < 2 * 2 ^ (w - 1) := by have := ha t ht; omega
    rw [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, testBit_top ha2] at hb
    simpa using hb
  have h3' : ((pk w (d * d) a ||| pk w (d * d) (fun _ => 2 ^ (w - 1))) -
      p * pk w (d * d) (fun _ => 1)) &&& pk w (d * d) (fun _ => 2 ^ (w - 1)) = 0 :=
    Nat.eq_of_beq_eq_true h3
  rw [top_H hw htop hp2] at h3'
  unfold pk at h3'
  refine ⟨pk_lt ha, fun t ht => ?_⟩
  rw [lane_pk ha ht]
  by_contra hn
  have hz := Finset.sum_eq_zero_iff.1 h3' t (Finset.mem_range.2 ht)
  have hn' : p ≤ a t := Nat.le_of_not_lt hn
  simp only [hn', ↓reduceIte] at hz
  exact absurd hz (Nat.mul_ne_zero (Nat.two_pow_pos _).ne' (Nat.two_pow_pos _).ne')

end MulR

private theorem orB_true {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

private theorem rec_and {f : Nat → Bool} : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m = true →
      ∀ g < m, f g = true
  | 0, _, g, hg => absurd hg (Nat.not_lt_zero g)
  | m + 1, h, g, hg => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m)
        (f m) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact rec_and m h1 g hg
    · exact h2

private theorem lenL_eq {α : Type} : ∀ l : List α, lenL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenL l) = _
    rw [lenL_eq l]
    rfl

private theorem nthRel_eq : ∀ (l : List (List (Nat × Bool))) (k : Nat) (hk : k < l.length),
    nthRel l k = l[k]
  | [], k, hk => absurd hk (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: l, k + 1, hk => by
    change nthRel l k = _
    rw [nthRel_eq l k (by simp at hk; omega)]
    rfl

private noncomputable def bndL (L : Nat) (r : List (Nat × Bool)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih2 => andB (Prod.rec (motive := fun _ => Bool) (fun g _ => Nat.blt g L) x) ih2) r

private theorem bndL_spec {L : Nat} : ∀ r : List (Nat × Bool), bndL L r = true →
    ∀ x ∈ r, x.1 < L
  | [], _ => by simp
  | (g, s) :: r, h => by
    have h' : andB (Nat.blt g L) (bndL L r) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.blt_eq.mp h1
    · exact bndL_spec r h2 x hx

private theorem relsBounded_spec {L : Nat} : ∀ rels : List (List (Nat × Bool)),
    relsBounded rels L = true → ∀ v ∈ rels, ∀ x ∈ v, x.1 < L
  | [], _ => by simp
  | r :: rs, h => by
    have h' : andB (bndL L r) (relsBounded rs L) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact bndL_spec v h1
    · exact relsBounded_spec rs h2 v hv

private theorem letEq_spec : ∀ x y : Nat × Bool, letEq x y = true → x = y
  | (g, s), (h, t), hxy => by
    have h' : andB (Nat.beq g h) (Bool.rec (motive := fun _ => Bool) (notB t) t s) = true := hxy
    obtain ⟨e1, e2⟩ := andB_true h'
    have e := Nat.eq_of_beq_eq_true e1
    subst e
    cases s <;> cases t <;> first | rfl | exact absurd e2 (by decide)

private theorem wordEq_spec : ∀ u v : List (Nat × Bool), wordEq u v = true → u = v
  | [], [], _ => rfl
  | [], _ :: _, h => absurd (h : false = true) Bool.false_ne_true
  | _ :: _, [], h => absurd (h : false = true) Bool.false_ne_true
  | x :: xs, y :: ys, h => by
    have h' : andB (letEq x y) (wordEq xs ys) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    rw [letEq_spec x y h1, wordEq_spec xs ys h2]

private noncomputable def flipL (x : Nat × Bool) : Nat × Bool :=
  Prod.rec (motive := fun _ => Nat × Bool) (fun g s => (g, notB s)) x

private theorem invWord_eq : ∀ u acc : List (Nat × Bool),
    invWord u acc = (u.map flipL).reverse ++ acc
  | [], _ => rfl
  | x :: u, acc => by
    change invWord u (flipL x :: acc) = _
    rw [invWord_eq u]
    simp

private theorem prod_inv {R : Type} [Monoid R] {f : Nat × Bool → R} :
    ∀ u : List (Nat × Bool), (∀ x ∈ u, f (flipL x) * f x = 1) →
      ((u.map flipL).reverse.map f).prod * (u.map f).prod = 1
  | [], _ => by simp
  | x :: u, h => by
    have ih := prod_inv u (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (by simp)
    simp only [List.map_cons, List.reverse_cons, List.map_append, List.prod_append, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [mul_assoc, ← mul_assoc (f (flipL x)), hx, one_mul, ih]

private theorem segProd_sem {R : Type} [Monoid R] {RB : Nat → Nat} {mul : Nat → Nat → Nat}
    {ONE Lg lo hi : Nat} {P : Nat → Prop} {M : Nat → R}
    (hmul : ∀ A B, P A → P B → P (mul A B) ∧ M (mul A B) = M A * M B) (hone : M ONE = 1) :
    ∀ (l : List (Nat × Bool)) (i acc : Nat), lo ≤ i → i + l.length ≤ hi → P acc →
      (∀ x ∈ l, P (letM RB Lg x)) →
      P (segProd RB mul ONE Lg lo hi l i acc) ∧
        M (segProd RB mul ONE Lg lo hi l i acc) = M acc * (l.map fun x => M (letM RB Lg x)).prod
  | [], _, _, _, _, hP, _ => ⟨hP, by rw [List.map_nil, List.prod_nil, mul_one]; rfl⟩
  | x :: l, i, acc, hlo, hhi, hP, hl => by
    have e : segProd RB mul ONE Lg lo hi (x :: l) i acc =
        segProd RB mul ONE Lg lo hi l (Nat.succ i)
          (Bool.rec (motive := fun _ => Nat) acc
            ((fun m => Bool.rec (motive := fun _ => Nat) (mul acc m) m (Nat.beq acc ONE))
              (letM RB Lg x))
            (andB (Nat.ble lo i) (Nat.blt i hi))) :=
      strictN_eqO _ (segProd RB mul ONE Lg lo hi l (Nat.succ i))
    have hx := hl x (by simp)
    have hhi' : i + l.length + 1 ≤ hi := by
      rw [List.length_cons] at hhi
      omega
    have hb1 : Nat.ble lo i = true := Nat.ble_eq.mpr hlo
    have hb2 : Nat.blt i hi = true := Nat.blt_eq.mpr (by omega)
    obtain ⟨acc', hacc, hP', hM'⟩ : ∃ acc', (Bool.rec (motive := fun _ => Nat) acc
        ((fun m => Bool.rec (motive := fun _ => Nat) (mul acc m) m (Nat.beq acc ONE))
          (letM RB Lg x))
        (andB (Nat.ble lo i) (Nat.blt i hi))) = acc' ∧ P acc' ∧
          M acc' = M acc * M (letM RB Lg x) := by
      rw [hb1, hb2]
      cases hq : Nat.beq acc ONE
      · exact ⟨mul acc (letM RB Lg x), rfl, hmul _ _ hP hx⟩
      · have hq' : acc = ONE := Nat.eq_of_beq_eq_true hq
        exact ⟨letM RB Lg x, rfl, hx, by rw [hq', hone, one_mul]⟩
    rw [e, hacc]
    obtain ⟨h1, h2⟩ := segProd_sem (RB := RB) (Lg := Lg) (lo := lo) (hi := hi) hmul hone l
      (i + 1) acc' (by omega) (by omega) hP' (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    exact ⟨h1, by rw [h2, hM', List.map_cons, List.prod_cons, mul_assoc]⟩

theorem rels_sound {p d w S T L H CM RM ONE LV HV nb Lg : Nat} {RB : Nat → Nat}
    {rels : List (List (Nat × Bool))}
    (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    (hroot : rootsOK RB (validM p nb L H) 1 (Lg + 1) = true)
    (hinv : invsOK RB (mulR p w S d T L H CM RM) (validM p nb L H) Lg ONE = true)
    (hb : relsBounded rels Lg = true)
    (hr : ∀ r < lenRels rels, relOK RB (mulR p w S d T L H CM RM) rels Lg ONE r = true ∨
      ∃ s < r, relDupOK rels s r = true) :
    (∀ g < Lg, ordMat p d w S (RB (g + 1)) * ordMat p d w S (RB (Lg + 1 + g)) = 1) ∧
      ∀ v ∈ rels, (v.map fun x => ordMat p d w S (letM RB Lg x)).prod = 1 := by
  subst hnb
  have hmul : ∀ A B, Canon p d w A → Canon p d w B →
      Canon p d w (mulR p w S d T L H CM RM A B) ∧
        ordMat p d w S (mulR p w S d T L H CM RM A B) = ordMat p d w S A * ordMat p d w S B :=
    fun A B hA hB => mulR_sound hc hA hB
  obtain ⟨hONEc, hONE⟩ := one_sound hc
  have hR0 := rec_and (f := fun i => Bool.rec (motive := fun _ => Bool) true
    (validM p (d * S) L H (RB i)) (Nat.ble 1 i)) (Lg + 1) hroot
  have hR : ∀ g < Lg, Canon p d w (RB (g + 1)) := by
    intro g hg
    have h := hR0 (g + 1) (by omega)
    have hb1 : Nat.ble 1 (g + 1) = true := Nat.ble_eq.mpr (by omega)
    rw [hb1] at h
    exact validM_canon hc h
  have hI0 := rec_and (f := fun g => andB (validM p (d * S) L H (RB (Nat.add (Nat.succ Lg) g)))
    (Nat.beq (mulR p w S d T L H CM RM (RB (Nat.succ g)) (RB (Nat.add (Nat.succ Lg) g))) ONE))
    Lg hinv
  have hI : ∀ g < Lg, Canon p d w (RB (Lg + 1 + g)) ∧
      mulR p w S d T L H CM RM (RB (g + 1)) (RB (Lg + 1 + g)) = ONE := by
    intro g hg
    obtain ⟨h1, h2⟩ := andB_true (hI0 g hg)
    exact ⟨validM_canon hc h1, Nat.eq_of_beq_eq_true h2⟩
  have hpair : ∀ g < Lg,
      ordMat p d w S (RB (g + 1)) * ordMat p d w S (RB (Lg + 1 + g)) = 1 := by
    intro g hg
    rw [← (hmul _ _ (hR g hg) (hI g hg).1).2, (hI g hg).2, hONE]
  refine ⟨hpair, ?_⟩
  have hbd := relsBounded_spec rels hb
  have hlet : ∀ x : Nat × Bool, x.1 < Lg → Canon p d w (letM RB Lg x) := by
    rintro ⟨g, s⟩ hg
    cases s
    · exact (hI g hg).1
    · exact hR g hg
  have hflip : ∀ x : Nat × Bool, x.1 < Lg →
      ordMat p d w S (letM RB Lg (flipL x)) * ordMat p d w S (letM RB Lg x) = 1 := by
    rintro ⟨g, s⟩ hg
    cases s
    · exact hpair g hg
    · exact mul_eq_one_comm.1 (hpair g hg)
  have hlen : lenRels rels = rels.length := lenL_eq rels
  have hrel : ∀ r, r < rels.length →
      ((nthRel rels r).map fun x => ordMat p d w S (letM RB Lg x)).prod = 1 := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr'
      have hmem : nthRel rels r ∈ rels := by
        rw [nthRel_eq rels r hr']
        exact List.getElem_mem hr'
      rcases hr r (by rw [hlen]; exact hr') with h | ⟨s, hs, h⟩
      · have h' : andB (Nat.blt r (lenL rels)) (andB (Nat.blt 0 (lenL (nthRel rels r)))
            (andB (Nat.ble (lenL (nthRel rels r)) (lenL (nthRel rels r)))
              (Nat.beq (segProd RB (mulR p w S d T L H CM RM) ONE Lg 0 (lenL (nthRel rels r))
                (nthRel rels r) 0 ONE) ONE))) = true := h
        obtain ⟨-, h'⟩ := andB_true h'
        obtain ⟨-, h'⟩ := andB_true h'
        obtain ⟨-, h'⟩ := andB_true h'
        have hseg := Nat.eq_of_beq_eq_true h'
        have hs := (segProd_sem (P := Canon p d w) (M := ordMat p d w S) (lo := 0)
          (hi := lenL (nthRel rels r)) hmul hONE
          (nthRel rels r) 0 ONE (Nat.le_refl 0) (by rw [lenL_eq]; omega) hONEc
          (fun x hx => hlet x (hbd _ hmem x hx))).2
        rw [hseg, hONE, one_mul] at hs
        exact hs.symm
      · have h' : andB (Nat.blt s r) (andB (Nat.blt r (lenL rels))
            (orB (wordEq (nthRel rels r) (nthRel rels s))
              (wordEq (nthRel rels r) (invWord (nthRel rels s) [])))) = true := h
        obtain ⟨-, h'⟩ := andB_true h'
        obtain ⟨-, h'⟩ := andB_true h'
        have hsl : s < rels.length := by omega
        have hsmem : nthRel rels s ∈ rels := by
          rw [nthRel_eq rels s hsl]
          exact List.getElem_mem hsl
        rcases orB_true h' with h'' | h''
        · rw [wordEq_spec _ _ h'']
          exact ih s hs hsl
        · rw [wordEq_spec _ _ h'', invWord_eq, List.append_nil]
          have hp := prod_inv (f := fun x => ordMat p d w S (letM RB Lg x)) (nthRel rels s)
            (fun x hx => hflip x (hbd _ hsmem x hx))
          rw [ih s hs hsl, mul_one] at hp
          exact hp
  intro v hv
  obtain ⟨r, hr', rfl⟩ := List.getElem_of_mem hv
  rw [← nthRel_eq rels r hr']
  exact hrel r hr'

end CFSG.KS.Ord

end
