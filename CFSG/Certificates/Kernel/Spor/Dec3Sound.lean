module

public import CFSG.Certificates.Kernel.Orders.Cert3
public import CFSG.Certificates.Kernel.Spor.Mat3Sound
public import Certificates.Data.Kernel.Spor.Bytes
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.KS.Dec3

open CFSG.KC.Ord CFSG.KS.Mat3

theorem rawAnd_true3 {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem char_beq3 (c d : Char) : (c == d) = (c.toNat == d.toNat) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Char.ext (UInt32.toNat_inj.mp h)

theorem char_le3 (c d : Char) : (c ≤ d) ↔ c.toNat ≤ d.toNat := UInt32.le_iff_toNat_le

@[expose] noncomputable def dgv3 (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

@[expose] noncomputable def ents3 (B : List Char) : List Nat :=
  (B.filter fun c => !CFSG.Blueprint.NativeSporadic.asciiWhitespace c).map dgv3

theorem ws_eq3 (c : Char) :
    ws c.toNat = CFSG.Blueprint.NativeSporadic.asciiWhitespace c := by
  unfold ws CFSG.Blueprint.NativeSporadic.asciiWhitespace
  rw [char_beq3, char_beq3, char_beq3, char_beq3]
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

theorem ent_eq3 (p : Nat) (c : Char) : ent p c.toNat = dgv3 c % p := by
  unfold ent dgv3
  have e0 : ('0' : Char).toNat = 48 := rfl
  have e9 : ('9' : Char).toNat = 57 := rfl
  rw [e0]
  unfold andB
  have hd : ('0' ≤ c && c ≤ '9') = (Nat.ble 48 c.toNat && Nat.ble c.toNat 57) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq, char_le3, e0, e9]
  rw [hd]
  cases Nat.ble 48 c.toNat <;> cases Nat.ble c.toNat 57 <;> simp
  rfl

@[expose] noncomputable def byt3 (F : Nat → Nat) (lb i : Nat) : Nat :=
  Nat.land (Nat.shiftRight (F (Nat.div i lb)) (Nat.mul 8 (Nat.mod i lb))) 255

theorem bytes_run3 {F : Nat → Nat} {lb len : Nat} : ∀ (cs : List Char) (i : Nat),
    CFSG.KS.Bytes.run F lb len cs i = true →
    i + cs.length = len ∧ ∀ k < cs.length, (cs[k]!).toNat < 128 ∧ (cs[k]!).toNat = byt3 F lb (i + k)
  | [], i, h => ⟨by have := Nat.eq_of_beq_eq_true h; simpa using this, fun k hk => by simp at hk⟩
  | ch :: cs, i, h => by
    change bAnd(Nat.blt (Char.toNat ch) (nat_lit 128), bAnd(Nat.blt i len,
      bAnd(Nat.beq (Char.toNat ch) (byt3 F lb i),
        CFSG.KS.Bytes.run F lb len cs (Nat.succ i)))) = true at h
    obtain ⟨h1, h⟩ := rawAnd_true3 h
    obtain ⟨_, h⟩ := rawAnd_true3 h
    obtain ⟨h3, h4⟩ := rawAnd_true3 h
    obtain ⟨a, b⟩ := bytes_run3 cs (i + 1) h4
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

variable (F : Nat → Nat) (lb len d N RM M : Nat)

@[expose] noncomputable def gstep3 (St idx : Nat) : Nat :=
  if idx < len then decByte3 d N RM M St (byt3 F lb idx) else St

theorem leafRun3 (leaf : Nat) (hlb : 0 < lb) : ∀ n ≤ lb, ∀ St,
    Nat.rec (motive := fun _ => Nat → Nat) (fun St => St)
      (fun q ih2 St => (fun idx => CFSG.KC.Loop.strictN
          (Bool.rec (motive := fun _ => Nat) St
            (decByte3 d N RM M St (Nat.land (Nat.shiftRight (F leaf)
              (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub lb (nat_lit 1)) q))) (nat_lit 255)))
            (Nat.blt idx len))
          ih2) (Nat.add (Nat.mul leaf lb) (Nat.sub (Nat.sub lb (nat_lit 1)) q))) n St =
      (List.range' (lb - n) n).foldl
        (fun St off => gstep3 F lb len d N RM M St (leaf * lb + off)) St := by
  intro n
  induction n with
  | zero => intro _ St; rfl
  | succ n ih =>
    intro hn St
    change CFSG.KC.Loop.strictN _ _ = _
    rw [strictN_eq3, ih (by omega)]
    have e : lb - (n + 1) = lb - 1 - n := by omega
    rw [e, List.range'_succ, List.foldl_cons]
    have e2 : lb - 1 - n + 1 = lb - n := by omega
    rw [e2]
    congr 1
    unfold gstep3 byt3
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

theorem decRun3_cons (leaf : Nat) (Cs : List Nat) (St : Nat) :
    decRun3 F lb len d N RM M (leaf :: Cs) St = decRun3 F lb len d N RM M Cs
      (Nat.rec (motive := fun _ => Nat → Nat) (fun St => St)
        (fun q ih2 St => (fun idx => CFSG.KC.Loop.strictN
            (Bool.rec (motive := fun _ => Nat) St
              (decByte3 d N RM M St (Nat.land (Nat.shiftRight (F leaf)
                (Nat.mul (nat_lit 8) (Nat.sub (Nat.sub lb (nat_lit 1)) q))) (nat_lit 255)))
              (Nat.blt idx len))
            ih2) (Nat.add (Nat.mul leaf lb) (Nat.sub (Nat.sub lb (nat_lit 1)) q))) lb St) := by
  change CFSG.KC.Loop.strictN _ _ = _
  rw [strictN_eq3]
  rfl

theorem decRun3_nil (St : Nat) : decRun3 F lb len d N RM M [] St = St := rfl

theorem decRun3_append : ∀ (xs ys : List Nat) (St : Nat),
    decRun3 F lb len d N RM M (xs ++ ys) St =
      decRun3 F lb len d N RM M ys (decRun3 F lb len d N RM M xs St)
  | [], _, _ => rfl
  | x :: xs, ys, St => by
    rw [List.cons_append, decRun3_cons, decRun3_cons, decRun3_append xs ys]

theorem decRun3_range (hlb : 0 < lb) : ∀ (m St : Nat),
    decRun3 F lb len d N RM M (List.range m) St =
      (List.range (m * lb)).foldl (gstep3 F lb len d N RM M) St
  | 0, St => by
    rw [Nat.zero_mul]
    rfl
  | m + 1, St => by
    rw [List.range_succ, decRun3_append, decRun3_range hlb m, decRun3_cons, decRun3_nil]
    have e := leafRun3 F lb len d N RM M m hlb lb (Nat.le_refl lb)
    rw [e, Nat.sub_self, Nat.succ_mul, List.range_add, List.foldl_append, List.foldl_map,
      ← List.range_eq_range']

end Run

theorem decRun3_join {F : Nat → Nat} {lb len d N RM M : Nat} {l1 l2 : List Nat} {x y z : Nat}
    (h1 : Nat.beq (decRun3 F lb len d N RM M l1 x) y = true)
    (h2 : Nat.beq (decRun3 F lb len d N RM M l2 y) z = true) :
    Nat.beq (decRun3 F lb len d N RM M (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  change decRun3 F lb len d N RM M (l1 ++ l2) x = z
  rw [decRun3_append, h1, h2]

@[expose] noncomputable def enc3 (k R : Nat) : Nat :=
  Nat.add (nat_lit 3) (Nat.add (Nat.shiftLeft k (nat_lit 2)) (Nat.shiftLeft R (nat_lit 26)))

theorem enc3_val (k R : Nat) : enc3 k R = 3 + 4 * k + 67108864 * R := by
  unfold enc3
  change 3 + (k <<< 2 + R <<< 26) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  ring

section Facts

variable {k R : Nat}

theorem enc3_land1 : Nat.land (enc3 k R) (nat_lit 1) = nat_lit 1 := by
  change enc3 k R &&& 1 = 1
  rw [Nat.and_one_is_mod, enc3_val]
  omega

theorem enc3_shr1 :
    Nat.land (Nat.shiftRight (enc3 k R) (nat_lit 1)) (nat_lit 1) = nat_lit 1 := by
  change (enc3 k R >>> 1) &&& 1 = 1
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, enc3_val, Nat.pow_one]
  omega

theorem enc3_bits (hk : k < 16777216) : bitsN (enc3 k R) (nat_lit 2) (nat_lit 24) = k := by
  unfold bitsN
  change (enc3 k R >>> 2) &&& ((1 <<< 24) - 1) = k
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    enc3_val]
  norm_num
  omega

theorem enc3_shr26 (hk : k < 16777216) : Nat.shiftRight (enc3 k R) (nat_lit 26) = R := by
  change enc3 k R >>> 26 = R
  rw [Nat.shiftRight_eq_div_pow, enc3_val]
  norm_num
  omega

end Facts

section Dec

variable (d N RM M : Nat)

@[expose] noncomputable def decc3 (St : Nat) (c : Char) : Nat := decByte3 d N RM M St c.toNat

theorem fold_zero3 : ∀ cs : List Char, cs.foldl (decc3 d N RM M) 0 = 0
  | [] => rfl
  | c :: cs => by
    rw [List.foldl_cons]
    exact fold_zero3 cs

theorem dec_one3 {b : Nat} (hb : b < 128) :
    decByte3 d N RM M 1 b = if b = 10 then 3 else 1 := by
  unfold decByte3
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

theorem dec_enc3 {k R b : Nat} (hk : k < 16777216) (hb : b < 128) :
    decByte3 d N RM M (enc3 k R) b =
      if ws b = true then enc3 k R else
        if k < d * d then
          (if k % d + 1 = d then
            (if Nat.lor R (Nat.add (Nat.shiftLeft (Nat.land (ent (nat_lit 3) b) (nat_lit 1)) (Nat.mod k d))
                  (Nat.shiftLeft (Nat.shiftRight (ent (nat_lit 3) b) (nat_lit 1)) (Nat.add d (Nat.mod k d)))) =
                rowOf3 d N RM M (Nat.div k d) then enc3 (k + 1) 0 else 0)
          else enc3 (k + 1) (Nat.lor R (Nat.add (Nat.shiftLeft (Nat.land (ent (nat_lit 3) b) (nat_lit 1))
              (Nat.mod k d)) (Nat.shiftLeft (Nat.shiftRight (ent (nat_lit 3) b) (nat_lit 1))
                (Nat.add d (Nat.mod k d))))))
        else enc3 k R := by
  unfold decByte3
  rw [enc3_land1, Nat.blt_eq.mpr hb, enc3_shr1, enc3_bits hk, enc3_shr26 hk]
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
        cases h3 : Nat.beq (Nat.lor R (Nat.add (Nat.shiftLeft (Nat.land (ent (nat_lit 3) b) (nat_lit 1))
            (Nat.mod k d)) (Nat.shiftLeft (Nat.shiftRight (ent (nat_lit 3) b) (nat_lit 1))
              (Nat.add d (Nat.mod k d))))) (rowOf3 d N RM M (Nat.div k d))
        · have hn : ¬ Nat.lor R (Nat.add (Nat.shiftLeft (Nat.land (ent (nat_lit 3) b) (nat_lit 1))
              (Nat.mod k d)) (Nat.shiftLeft (Nat.shiftRight (ent (nat_lit 3) b) (nat_lit 1))
                (Nat.add d (Nat.mod k d)))) = rowOf3 d N RM M (Nat.div k d) := fun h' => by
            rw [h', Nat.beq_refl] at h3
            exact Bool.noConfusion h3
          simp only [hn, ↓reduceIte]
        · have hr := Nat.eq_of_beq_eq_true h3
          simp only [hr, ↓reduceIte]
          rfl
  · rfl

theorem header3 : ∀ cs : List Char, (∀ c ∈ cs, c.toNat < 128) →
    Nat.land (cs.foldl (decc3 d N RM M) 1) 3 = 3 →
    cs.foldl (decc3 d N RM M) 1 =
      ((cs.dropWhile (· != '\n')).drop 1).foldl (decc3 d N RM M) 3
  | [], _, h => absurd h (by change ¬ Nat.land 1 3 = 3; decide)
  | c :: cs, ha, h => by
    have hc : c.toNat < 128 := ha c (by simp)
    have e : decc3 d N RM M 1 c = if c.toNat = 10 then 3 else 1 := dec_one3 d N RM M hc
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
      exact header3 cs (fun c' hc' => ha c' (List.mem_cons_of_mem _ hc')) h

end Dec

@[expose] def RowP (d n : Nat) (g : Nat → Nat) (R : Nat) : Prop :=
  ∀ u, R.testBit u = true ↔ (u < d ∧ u < n ∧ g u = 1) ∨ (d ≤ u ∧ u < d + d ∧ u - d < n ∧ g (u - d) = 2)

theorem ins_bit {d e j : Nat} (he : e < 3) (u : Nat) :
    (Nat.add (Nat.shiftLeft (Nat.land e (nat_lit 1)) j)
      (Nat.shiftLeft (Nat.shiftRight e (nat_lit 1)) (Nat.add d j))).testBit u = true ↔
      (u = j ∧ e = 1) ∨ (u = d + j ∧ e = 2) := by
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2) with rfl | rfl | rfl
  · change (0 <<< j + 0 <<< (d + j)).testBit u = true ↔ _
    simp
  · change (1 <<< j + 0 <<< (d + j)).testBit u = true ↔ _
    rw [Nat.zero_shiftLeft, Nat.add_zero, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]
    omega
  · change (0 <<< j + 1 <<< (d + j)).testBit u = true ↔ _
    rw [Nat.zero_shiftLeft, Nat.zero_add, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff]
    omega

theorem rowP_ins {d n e R : Nat} {g g' : Nat → Nat} (hn : n < d) (he : e < 3) (hR : RowP d n g R)
    (hg1 : ∀ t < n, g' t = g t) (hg2 : g' n = e) :
    RowP d (n + 1) g' (Nat.lor R (Nat.add (Nat.shiftLeft (Nat.land e (nat_lit 1)) n)
      (Nat.shiftLeft (Nat.shiftRight e (nat_lit 1)) (Nat.add d n)))) := by
  intro u
  rw [lor_eq3, Nat.testBit_or, Bool.or_eq_true, hR u, ins_bit he u]
  constructor
  · rintro ((⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩))
    · exact Or.inl ⟨h1, by omega, by rw [hg1 u h2]; exact h3⟩
    · exact Or.inr ⟨h1, h2, by omega, by rw [hg1 _ h3]; exact h4⟩
    · subst h1
      exact Or.inl ⟨hn, by omega, by rw [hg2]; exact h2⟩
    · subst h1
      refine Or.inr ⟨by omega, by omega, by omega, ?_⟩
      rw [show d + n - d = n by omega, hg2]
      exact h2
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
      · exact Or.inl (Or.inl ⟨h1, h2, by rw [← hg1 u h2]; exact h3⟩)
      · exact Or.inr (Or.inl ⟨rfl, by rw [← hg2]; exact h3⟩)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 h3 with h3 | h3
      · exact Or.inl (Or.inr ⟨h1, h2, h3, by rw [← hg1 _ h3]; exact h4⟩)
      · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
        rw [← hg2, ← h3]
        exact h4

theorem rowOf3_bit {d N M i j : Nat} (hj : j < d) :
    (rowOf3 d N (2 ^ d - 1) M i).testBit j = M.testBit (d * i + j) ∧
      (rowOf3 d N (2 ^ d - 1) M i).testBit (d + j) = M.testBit (N + (d * i + j)) := by
  unfold rowOf3
  rw [add_eq3, shl_eq3, land_eq3, land_eq3, shr_eq3, shr_eq3, mul_eq3, add_eq3,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.mul_comm _ (2 ^ d),
    Nat.add_comm, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos d)),
    Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos d)), ite_eq_left hj,
    ite_eq_right (by omega), Nat.add_sub_cancel_left, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.add_assoc]
  simp [hj]

theorem bv_val {b1 b2 : Bool} {x : Nat} (hx : x < 3) (h1 : b1 = true ↔ x = 1) (h2 : b2 = true ↔ x = 2) :
    bv b1 b2 = ((x : Nat) : ZMod 3) := by
  rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2) with rfl | rfl | rfl
  · have : b1 = false := by cases b1 <;> simp_all
    have : b2 = false := by cases b2 <;> simp_all
    subst b1 b2
    rfl
  · have : b1 = true := h1.2 rfl
    subst b1
    rfl
  · have : b1 = false := by cases b1 <;> simp_all
    have : b2 = true := h2.2 rfl
    subst b1 b2
    rfl

theorem getD_append_left3 {pre X : List Nat} {n : Nat} (h : n < pre.length) :
    (pre ++ X)[n]?.getD 0 = pre[n]?.getD 0 := by
  rw [List.getElem?_append_left h]

theorem divmod3 {k d q m : Nat} (hk : k = q * d + m) (hm : m < d) :
    k / d = q ∧ k % d = m := by
  have hd : 0 < d := by omega
  exact (Nat.div_mod_unique hd).2 ⟨by rw [hk, Nat.mul_comm]; omega, hm⟩

theorem body3 {d N M : Nat} (hdd : d * d < 16777216) :
    ∀ (B : List Char) (k R : Nat) (pre : List Nat),
    (∀ c ∈ B, c.toNat < 128) → pre.length = k → k ≤ d * d →
    (k < d * d → RowP d (k % d) (fun j => (pre[k / d * d + j]?.getD 0) % 3) R) →
    Nat.land (B.foldl (decc3 d N (2 ^ d - 1) M) (enc3 k R)) 3 = 3 →
    bitsN (B.foldl (decc3 d N (2 ^ d - 1) M) (enc3 k R)) 2 24 = d * d →
    ∀ i < d, k / d ≤ i → ∀ j < d,
      bv (M.testBit (d * i + j)) (M.testBit (N + (d * i + j))) =
        ((((pre ++ ents3 B)[i * d + j]?.getD 0) % 3 : Nat) : ZMod 3)
  | [], k, R, pre, _, hl, hkd, _, _, hb, i, hi, hki, j, hj => by
    rw [List.foldl_nil, enc3_bits (by omega)] at hb
    have : d ≤ k / d := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    omega
  | c :: B, k, R, pre, ha, hl, hkd, hinv, h3, hb, i, hi, hki, j, hj => by
    have hc : c.toNat < 128 := ha c (by simp)
    have ha' : ∀ c' ∈ B, c'.toNat < 128 := fun c' h' => ha c' (List.mem_cons_of_mem _ h')
    have hk24 : k < 16777216 := by omega
    have hd : 0 < d := by omega
    rw [List.foldl_cons] at h3 hb
    have e' : decc3 d N (2 ^ d - 1) M (enc3 k R) c = _ := dec_enc3 d N (2 ^ d - 1) M (R := R) hk24 hc
    rw [ws_eq3] at e'
    by_cases hws : CFSG.Blueprint.NativeSporadic.asciiWhitespace c = true
    · simp only [hws, ↓reduceIte] at e'
      rw [e'] at h3 hb
      have he : ents3 (c :: B) = ents3 B := by simp [ents3, hws]
      rw [he]
      exact body3 hdd B k R pre ha' hl hkd hinv h3 hb i hi hki j hj
    · simp only [hws, Bool.false_eq_true, ↓reduceIte] at e'
      have he : ents3 (c :: B) = dgv3 c :: ents3 B := by simp [ents3, hws]
      rw [he, show pre ++ dgv3 c :: ents3 B = (pre ++ [dgv3 c]) ++ ents3 B by simp]
      have hl' : (pre ++ [dgv3 c]).length = k + 1 := by simp [hl]
      by_cases hk : k < d * d
      · simp only [hk, ↓reduceIte] at e'
        have hdm := Nat.div_add_mod' k d
        have hmd := Nat.mod_lt k hd
        have hent : ent (nat_lit 3) c.toNat = dgv3 c % 3 := ent_eq3 3 c
        have hF : RowP d (k % d + 1) (fun j => ((pre ++ [dgv3 c])[k / d * d + j]?.getD 0) % 3)
            (Nat.lor R (Nat.add (Nat.shiftLeft (Nat.land (ent (nat_lit 3) c.toNat) (nat_lit 1))
              (Nat.mod k d)) (Nat.shiftLeft (Nat.shiftRight (ent (nat_lit 3) c.toNat) (nat_lit 1))
                (Nat.add d (Nat.mod k d))))) := by
          refine rowP_ins hmd (by rw [hent]; exact Nat.mod_lt _ (by omega)) (hinv hk) ?_ ?_
          · intro t ht
            rw [getD_append_left3 (by rw [hl]; omega)]
          · have e1 : k / d * d + k % d = pre.length := by rw [hl]; omega
            rw [e1, List.getElem?_concat_length, hent]
            rfl
        by_cases hlast : k % d + 1 = d
        · simp only [hlast, ↓reduceIte] at e'
          by_cases hrow : Nat.lor R (Nat.add (Nat.shiftLeft (Nat.land (ent (nat_lit 3) c.toNat) (nat_lit 1))
              (Nat.mod k d)) (Nat.shiftLeft (Nat.shiftRight (ent (nat_lit 3) c.toNat) (nat_lit 1))
                (Nat.add d (Nat.mod k d)))) = rowOf3 d N (2 ^ d - 1) M (Nat.div k d)
          · simp only [hrow, ↓reduceIte] at e'
            rw [e'] at h3 hb
            obtain ⟨q1, m1⟩ := divmod3 (k := k + 1) (d := d) (q := k / d + 1) (m := 0)
              (by rw [Nat.succ_mul]; omega) hd
            by_cases hiq : i = k / d
            · subst hiq
              have hdiv : Nat.div k d = k / d := rfl
              rw [hdiv] at hrow
              rw [hrow] at hF
              obtain ⟨r1, r2⟩ := rowOf3_bit (N := N) (M := M) (i := k / d) hj
              rw [← r1, ← r2]
              have hidx : k / d * d + j < (pre ++ [dgv3 c]).length := by rw [hl']; omega
              rw [Nat.mul_comm (k / d) d] at hidx ⊢
              rw [getD_append_left3 (pre := pre ++ [dgv3 c]) (X := ents3 B) hidx]
              apply bv_val (Nat.mod_lt _ (by omega))
              · rw [hF j, hlast]
                rw [Nat.mul_comm d (k / d)]
                constructor
                · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
                  · exact h
                  · omega
                · intro h
                  exact Or.inl ⟨hj, hj, h⟩
              · rw [hF (d + j), hlast]
                rw [Nat.mul_comm d (k / d)]
                constructor
                · rintro (⟨h, -⟩ | ⟨-, -, -, h⟩)
                  · omega
                  · rwa [Nat.add_sub_cancel_left] at h
                · intro h
                  refine Or.inr ⟨by omega, by omega, by omega, ?_⟩
                  rwa [Nat.add_sub_cancel_left]
            · refine body3 hdd B (k + 1) 0 (pre ++ [dgv3 c]) ha' hl' (by omega)
                (fun _ => ?_) h3 hb i hi (by omega) j hj
              rw [m1]
              intro u
              simp
          · simp only [hrow, ↓reduceIte] at e'
            rw [e', fold_zero3] at h3
            exact absurd h3 (by decide)
        · simp only [hlast, ↓reduceIte] at e'
          rw [e'] at h3 hb
          obtain ⟨q1, m1⟩ := divmod3 (k := k + 1) (d := d) (q := k / d) (m := k % d + 1)
            (by omega) (by omega)
          refine body3 hdd B (k + 1) _ (pre ++ [dgv3 c]) ha' hl' (by omega)
            (fun _ => ?_) h3 hb i hi (by omega) j hj
          rw [q1, m1]
          exact hF
      · have : d ≤ k / d := (Nat.le_div_iff_mul_le hd).2 (by omega)
        omega

theorem seed3_sound {d f N LO RM CI ONE UP lb len M St : Nat} {F : Nat → Nat}
    {cs : List Char} {Cs : List Nat}
    (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hb : CFSG.KS.Bytes.bytesEqK cs F lb len = true)
    (hCs : Cs = List.range ((len + lb - 1) / lb))
    (hr : Nat.beq (decRun3 F lb len d N RM M Cs 1) St = true)
    (hd : seedDone d (valid3 N LO) M St = true) :
    CFSG.Blueprint.NativeSporadic.decode 3 d 1 (String.ofList cs) = mat3 d N M := by
  obtain ⟨-, -, -, hRM, -, -⟩ := consts3_facts hc
  subst hRM
  unfold CFSG.KS.Bytes.bytesEqK at hb
  obtain ⟨hlb, hrun⟩ := rawAnd_true3 hb
  have hlb' : 0 < lb := Nat.blt_eq.mp hlb
  obtain ⟨hlen, hbytes⟩ := bytes_run3 cs 0 hrun
  rw [Nat.zero_add] at hlen
  have hasc : ∀ c ∈ cs, c.toNat < 128 := by
    intro c hc'
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc'
    have := (hbytes k hk).1
    rwa [getElem!_pos cs k hk] at this
  have hSt : St = cs.foldl (decc3 d N (2 ^ d - 1) M) 1 := by
    rw [← Nat.eq_of_beq_eq_true hr, hCs, decRun3_range F lb len d N (2 ^ d - 1) M hlb']
    have hm : len ≤ (len + lb - 1) / lb * lb := by
      have := Nat.div_add_mod (len + lb - 1) lb
      have := Nat.mod_lt (len + lb - 1) hlb'
      rw [Nat.mul_comm]
      omega
    rw [show (len + lb - 1) / lb * lb = len + ((len + lb - 1) / lb * lb - len) by omega,
      List.range_add, List.foldl_append, List.foldl_map]
    have htail : ∀ (l : List Nat) (X : Nat),
        l.foldl (fun x y => gstep3 F lb len d N (2 ^ d - 1) M x (len + y)) X = X := by
      intro l
      induction l with
      | nil => intro X; rfl
      | cons a l ih =>
        intro X
        rw [List.foldl_cons]
        have : gstep3 F lb len d N (2 ^ d - 1) M X (len + a) = X := by
          unfold gstep3
          simp
        rw [this]
        exact ih X
    rw [htail]
    have hmap : (List.range len).map (fun i => cs[i]!) = cs := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        rw [List.getElem_map, List.getElem_range, getElem!_pos cs i h2]
    rw [List.foldl_ext (gstep3 F lb len d N (2 ^ d - 1) M)
      (fun St i => decc3 d N (2 ^ d - 1) M St cs[i]!) 1
      (fun X i hi => by
        have hi' : i < len := List.mem_range.mp hi
        unfold gstep3 decc3
        rw [(hbytes i (by omega)).2, Nat.zero_add]
        simp [hi']), ← List.foldl_map (f := fun i => cs[i]!) (g := decc3 d N (2 ^ d - 1) M), hmap]
  unfold seedDone at hd
  obtain ⟨hd3, hd⟩ := andB_true3 hd
  obtain ⟨hdb, _⟩ := andB_true3 hd
  have h3 : Nat.land St 3 = 3 := Nat.eq_of_beq_eq_true hd3
  have hbits : bitsN St 2 24 = d * d := Nat.eq_of_beq_eq_true hdb
  have hdd : d * d < 16777216 := by
    rw [← hbits]
    unfold bitsN
    change (St >>> 2) &&& ((1 <<< 24) - 1) < _
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  rw [hSt] at h3 hbits
  have hH := header3 d N (2 ^ d - 1) M cs hasc h3
  rw [hH] at h3 hbits
  have e3 : enc3 0 0 = 3 := by rw [enc3_val]
  have hrows := body3 (N := N) (M := M) hdd ((cs.dropWhile (· != '\n')).drop 1) 0 0 []
    (fun c hc' => hasc c ((List.dropWhile_sublist _).subset (List.mem_of_mem_drop hc'))) rfl
    (Nat.zero_le _) (fun _ u => by simp) (by rw [e3]; exact h3) (by rw [e3]; exact hbits)
  funext i j
  unfold CFSG.Blueprint.NativeSporadic.decode mat3
  simp only [↓reduceIte, String.toList_ofList]
  have := hrows i.val i.isLt (by simp) j.val j.isLt
  rw [List.nil_append] at this
  change ((ents3 ((cs.dropWhile (· != '\n')).drop 1))[i.val * d + j.val]?.getD 0 : ZMod 3) = _
  rw [this, ZMod.natCast_mod]

theorem seedDone3_canon {d N LO M St : Nat} (hLO : LO = 2 ^ N - 1)
    (hd : seedDone d (valid3 N LO) M St = true) : Canon3 N M := by
  unfold seedDone at hd
  obtain ⟨-, hd⟩ := andB_true3 hd
  obtain ⟨-, hv⟩ := andB_true3 hd
  exact (valid3_iff hLO).1 hv

end CFSG.KS.Dec3

end
