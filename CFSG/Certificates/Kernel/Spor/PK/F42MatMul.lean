module

public import CFSG.Certificates.Kernel.Spor.PK.F42Mat

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.F42 CFSG.F3.Native
open CFSG.LieType.Multipliers.F42 (eqPM commutes)

@[expose] def mulPart (n : ℕ) (X Y : Array V) : Array V :=
  X.map fun r => Nat.fold n (fun j _ acc => combStep Y r j acc) V.zero

theorem mulPart_full (X Y : Array V) : mulPart 52 X Y = mul 52 X Y := rfl

@[expose] def termM (X Y : Array V) (k : ℕ) : Array V :=
  Array.ofFn (n := 52) fun i =>
    if X[i]!.p.testBit k then Y[k]! else if X[i]!.m.testBit k then Y[k]!.neg else V.zero

private theorem mm_size52 {X : Array V} (hX : Can52 X) : X.size = 52 := (canonM_spec hX).1

private theorem mm_termM_size (X Y : Array V) (k : ℕ) : (termM X Y k).size = 52 := by
  simp [termM]

private theorem mm_termM_getElem (X Y : Array V) (k : ℕ) {i : ℕ} (hi : i < 52) :
    (termM X Y k)[i]! =
      if X[i]!.p.testBit k then Y[k]! else if X[i]!.m.testBit k then Y[k]!.neg else V.zero := by
  unfold termM
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  rfl

private theorem mm_mulPart_size (n : ℕ) (X Y : Array V) : (mulPart n X Y).size = X.size := by
  simp [mulPart]

private theorem mm_mulPart_getElem (n : ℕ) (X Y : Array V) {i : ℕ} (hi : i < X.size) :
    (mulPart n X Y)[i]! = Nat.fold n (fun j _ acc => combStep Y X[i]! j acc) V.zero := by
  unfold mulPart
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos X i hi]

private theorem mm_addM_getElem (X Y : Array V) {i : ℕ} (hi : i < 52) :
    (addM 52 X Y)[i]! = X[i]!.add Y[i]! := by
  unfold addM
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

private theorem mm_add_zero (a : V) : a.add V.zero = a := by
  cases a
  simp [V.add, V.zero]

private theorem mm_array_ext {A B : Array V} (hA : A.size = 52) (hB : B.size = 52)
    (h : ∀ i < 52, A[i]! = B[i]!) : A = B := by
  apply Array.ext (by rw [hA, hB])
  intro i hi hi'
  have := h i (by omega)
  rwa [getElem!_pos A i hi, getElem!_pos B i hi'] at this

private theorem mm_mulPart_succ {X Y : Array V} (hX : Can52 X) {n : ℕ} :
    mulPart (n + 1) X Y = addM 52 (mulPart n X Y) (termM X Y n) := by
  have hs := mm_size52 hX
  refine mm_array_ext (by rw [mm_mulPart_size, hs]) (addM_size 52 _ _) fun i hi => ?_
  have hiX : i < X.size := by rw [hs]; exact hi
  rw [mm_mulPart_getElem _ _ _ hiX, mm_addM_getElem _ _ hi, mm_mulPart_getElem _ _ _ hiX,
    mm_termM_getElem _ _ _ hi]
  simp only [Nat.fold_succ]
  unfold combStep
  generalize Nat.fold n (fun j _ acc => combStep Y X[i]! j acc) V.zero = acc
  by_cases hp : X[i]!.p.testBit n = true <;> by_cases hm : X[i]!.m.testBit n = true <;>
    simp [hp, hm, V.sub, mm_add_zero]

private theorem mm_can52_termM {X Y : Array V} (hY : Can52 Y) {k : ℕ} (hk : k < 52) :
    Can52 (termM X Y k) := by
  obtain ⟨-, hY'⟩ := can52_iff.1 hY
  obtain ⟨hy1, hy2, hy3⟩ := hY' k hk
  refine can52_iff.2 ⟨mm_termM_size X Y k, fun i hi => ?_⟩
  rw [mm_termM_getElem X Y k hi]
  split_ifs
  · exact ⟨hy1, hy2, hy3⟩
  · exact ⟨hy2, hy1, by rw [Nat.and_comm]; exact hy3⟩
  · exact ⟨Nat.two_pow_pos 52, Nat.two_pow_pos 52, rfl⟩

theorem can52_mulPart {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) {n : ℕ} (hn : n ≤ 52) :
    Can52 (mulPart n X Y) := by
  induction n with
  | zero =>
    refine can52_iff.2 ⟨by rw [mm_mulPart_size, mm_size52 hX], fun i hi => ?_⟩
    rw [mm_mulPart_getElem _ _ _ (by rw [mm_size52 hX]; exact hi), Nat.fold_zero]
    exact ⟨Nat.two_pow_pos 52, Nat.two_pow_pos 52, rfl⟩
  | succ n ih =>
    rw [mm_mulPart_succ hX]
    exact can52_addM (ih (by omega)) (mm_can52_termM hY (by omega))

theorem can52_termM {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) {k : ℕ} (hk : k < 52) :
    Can52 (termM X Y k) :=
  mm_can52_termM hY hk

theorem mulPart_succ {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) {n : ℕ} (hn : n < 52) :
    mulPart (n + 1) X Y = addM 52 (mulPart n X Y) (termM X Y n) :=
  mm_mulPart_succ hX

private theorem mm_testBit_enc {w len : ℕ} {f : ℕ → ℕ} (hf : ∀ i < len, f i < 2 ^ w) {i j : ℕ}
    (hi : i < len) (hj : j < w) : (enc w f len).testBit (w * i + j) = (f i).testBit j := by
  have h := fd_enc hf hi
  unfold fd at h
  rw [← h, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hj, Nat.add_comm]

private theorem mm_testBit_enc_ge {w len : ℕ} {f : ℕ → ℕ} (hf : ∀ i < len, f i < 2 ^ w) {t : ℕ}
    (ht : w * len ≤ t) : (enc w f len).testBit t = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (enc_lt hf) (Nat.pow_le_pow_right Nat.zero_lt_two ht))

private theorem mm_enc_mul_right (w : ℕ) (f : ℕ → ℕ) (c len : ℕ) :
    enc w f len * c = enc w (fun i => f i * c) len := by
  induction len with
  | zero => rw [enc_zero, enc_zero, Nat.zero_mul]
  | succ n ih => rw [enc_succ, enc_succ, Nat.add_mul, ih, Nat.mul_right_comm]

private theorem mm_enc_zero_fun (w len : ℕ) : enc w (fun _ => 0) len = 0 := by
  induction len with
  | zero => rfl
  | succ n ih => rw [enc_succ, ih, Nat.zero_mul]

private theorem mm_fd_land (w x y i : ℕ) : fd w (x &&& y) i = fd w x i &&& fd w y i := by
  unfold fd; rw [Nat.and_div_two_pow, Nat.and_mod_two_pow]

private theorem mm_fd_lor (w x y i : ℕ) : fd w (x ||| y) i = fd w x i ||| fd w y i := by
  unfold fd; rw [Nat.or_div_two_pow, Nat.or_mod_two_pow]

private theorem mm_fd_xor (w x y i : ℕ) : fd w (x ^^^ y) i = fd w x i ^^^ fd w y i := by
  unfold fd; rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow]

private theorem mm_enc_land {w len : ℕ} {f g : ℕ → ℕ} (hf : ∀ i < len, f i < 2 ^ w)
    (hg : ∀ i < len, g i < 2 ^ w) :
    enc w f len &&& enc w g len = enc w (fun i => f i &&& g i) len := by
  have hh : ∀ i < len, f i &&& g i < 2 ^ w := fun i hi => Nat.and_lt_two_pow _ (hg i hi)
  refine eq_of_fd_eq (Nat.and_lt_two_pow _ (enc_lt hg)) (enc_lt hh) fun i hi => ?_
  rw [mm_fd_land, fd_enc hf hi, fd_enc hg hi, fd_enc hh hi]

private theorem mm_enc_lor {w len : ℕ} {f g : ℕ → ℕ} (hf : ∀ i < len, f i < 2 ^ w)
    (hg : ∀ i < len, g i < 2 ^ w) :
    enc w f len ||| enc w g len = enc w (fun i => f i ||| g i) len := by
  have hh : ∀ i < len, f i ||| g i < 2 ^ w := fun i hi => Nat.or_lt_two_pow (hf i hi) (hg i hi)
  refine eq_of_fd_eq (Nat.or_lt_two_pow (enc_lt hf) (enc_lt hg)) (enc_lt hh) fun i hi => ?_
  rw [mm_fd_lor, fd_enc hf hi, fd_enc hg hi, fd_enc hh hi]

private theorem mm_addS_eq_add (ap am bp bm : ℕ) :
    addS ap am bp bm =
      (V.add ⟨ap, am⟩ ⟨bp, bm⟩).p ||| ((V.add ⟨ap, am⟩ ⟨bp, bm⟩).m <<< 2704) := by
  unfold addS
  simp only [letN_eq]
  rfl

private theorem mm_add_lt {a b : V} {n : ℕ} (hap : a.p < 2 ^ n) (ham : a.m < 2 ^ n)
    (hbp : b.p < 2 ^ n) (hbm : b.m < 2 ^ n) : (a.add b).p < 2 ^ n ∧ (a.add b).m < 2 ^ n := by
  unfold V.add
  dsimp only
  constructor <;>
  · repeat' first
      | apply Nat.or_lt_two_pow
      | apply Nat.xor_lt_two_pow
      | apply Nat.and_lt_two_pow
      | assumption

private theorem mm_fd_add (w : ℕ) (A B : V) (i : ℕ) :
    fd w (A.add B).p i = (V.add ⟨fd w A.p i, fd w A.m i⟩ ⟨fd w B.p i, fd w B.m i⟩).p ∧
    fd w (A.add B).m i = (V.add ⟨fd w A.p i, fd w A.m i⟩ ⟨fd w B.p i, fd w B.m i⟩).m := by
  unfold V.add
  dsimp only
  simp only [mm_fd_lor, mm_fd_land, mm_fd_xor, and_self]

theorem addS_pk52 {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) :
    addS (pk52 X % 2 ^ 2704) (pk52 X / 2 ^ 2704) (pk52 Y % 2 ^ 2704) (pk52 Y / 2 ^ 2704) =
      pk52 (addM 52 X Y) := by
  obtain ⟨-, hX'⟩ := can52_iff.1 hX
  obtain ⟨-, hY'⟩ := can52_iff.1 hY
  have hap : ∀ i < 52, X[i]!.p < 2 ^ 52 := fun i hi => (hX' i hi).1
  have ham : ∀ i < 52, X[i]!.m < 2 ^ 52 := fun i hi => (hX' i hi).2.1
  have hbp : ∀ i < 52, Y[i]!.p < 2 ^ 52 := fun i hi => (hY' i hi).1
  have hbm : ∀ i < 52, Y[i]!.m < 2 ^ 52 := fun i hi => (hY' i hi).2.1
  have hadd : ∀ i < 52, (X[i]!.add Y[i]!).p < 2 ^ 52 ∧ (X[i]!.add Y[i]!).m < 2 ^ 52 :=
    fun i hi => mm_add_lt (hap i hi) (ham i hi) (hbp i hi) (hbm i hi)
  rw [pk52_mod hX, pk52_div hX, pk52_mod hY, pk52_div hY, mm_addS_eq_add]
  have e1 : (V.add ⟨enc 52 (fun i => X[i]!.p) 52, enc 52 (fun i => X[i]!.m) 52⟩
      ⟨enc 52 (fun i => Y[i]!.p) 52, enc 52 (fun i => Y[i]!.m) 52⟩).p =
      enc 52 (fun i => (X[i]!.add Y[i]!).p) 52 := by
    refine eq_of_fd_eq ?_ (enc_lt fun i hi => (hadd i hi).1) fun i hi => ?_
    · exact (mm_add_lt (a := ⟨enc 52 (fun i => X[i]!.p) 52, enc 52 (fun i => X[i]!.m) 52⟩)
        (b := ⟨enc 52 (fun i => Y[i]!.p) 52, enc 52 (fun i => Y[i]!.m) 52⟩)
        (enc_lt hap) (enc_lt ham) (enc_lt hbp) (enc_lt hbm)).1
    · have := (mm_fd_add 52 ⟨enc 52 (fun i => X[i]!.p) 52, enc 52 (fun i => X[i]!.m) 52⟩
        ⟨enc 52 (fun i => Y[i]!.p) 52, enc 52 (fun i => Y[i]!.m) 52⟩ i).1
      dsimp only at this
      rw [this, fd_enc hap hi, fd_enc ham hi, fd_enc hbp hi, fd_enc hbm hi,
        fd_enc (fun i hi => (hadd i hi).1) hi]
  have e2 : (V.add ⟨enc 52 (fun i => X[i]!.p) 52, enc 52 (fun i => X[i]!.m) 52⟩
      ⟨enc 52 (fun i => Y[i]!.p) 52, enc 52 (fun i => Y[i]!.m) 52⟩).m =
      enc 52 (fun i => (X[i]!.add Y[i]!).m) 52 := by
    refine eq_of_fd_eq ?_ (enc_lt fun i hi => (hadd i hi).2) fun i hi => ?_
    · exact (mm_add_lt (a := ⟨enc 52 (fun i => X[i]!.p) 52, enc 52 (fun i => X[i]!.m) 52⟩)
        (b := ⟨enc 52 (fun i => Y[i]!.p) 52, enc 52 (fun i => Y[i]!.m) 52⟩)
        (enc_lt hap) (enc_lt ham) (enc_lt hbp) (enc_lt hbm)).2
    · have := (mm_fd_add 52 ⟨enc 52 (fun i => X[i]!.p) 52, enc 52 (fun i => X[i]!.m) 52⟩
        ⟨enc 52 (fun i => Y[i]!.p) 52, enc 52 (fun i => Y[i]!.m) 52⟩ i).2
      dsimp only at this
      rw [this, fd_enc hap hi, fd_enc ham hi, fd_enc hbp hi, fd_enc hbm hi,
        fd_enc (fun i hi => (hadd i hi).2) hi]
  have hlt : enc 52 (fun i => (X[i]!.add Y[i]!).p) 52 < 2 ^ 2704 :=
    enc_lt fun i hi => (hadd i hi).1
  rw [e1, e2, lor_shiftLeft_eq_add hlt, Nat.mul_comm (enc 52 (fun i => (X[i]!.add Y[i]!).m) 52)]
  unfold pk52
  rw [enc_congr (f := fun i => (X[i]!.add Y[i]!).p) (g := fun i => (addM 52 X Y)[i]!.p)
      (fun i hi => by rw [mm_addM_getElem X Y hi]),
    enc_congr (f := fun i => (X[i]!.add Y[i]!).m) (g := fun i => (addM 52 X Y)[i]!.m)
      (fun i hi => by rw [mm_addM_getElem X Y hi])]

@[expose] noncomputable def mulPlus (Ap Am Bp Bm k : ℕ) : ℕ :=
  Nat.lor (Nat.land (Nat.mul (Nat.land (Nat.shiftRight Ap k) rowR) rowF)
      (Nat.mul (Nat.land (Nat.shiftRight Bp (Nat.mul 52 k)) rowF) rowR))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight Am k) rowR) rowF)
      (Nat.mul (Nat.land (Nat.shiftRight Bm (Nat.mul 52 k)) rowF) rowR))

@[expose] noncomputable def mulMinus (Ap Am Bp Bm k : ℕ) : ℕ :=
  Nat.lor (Nat.land (Nat.mul (Nat.land (Nat.shiftRight Ap k) rowR) rowF)
      (Nat.mul (Nat.land (Nat.shiftRight Bm (Nat.mul 52 k)) rowF) rowR))
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight Am k) rowR) rowF)
      (Nat.mul (Nat.land (Nat.shiftRight Bp (Nat.mul 52 k)) rowF) rowR))

@[expose] noncomputable def mulLoop (Ap Am Bp Bm n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun k acc =>
    addS (Nat.land acc planeMask) (Nat.shiftRight acc 2704) (mulPlus Ap Am Bp Bm k)
      (mulMinus Ap Am Bp Bm k)) n

theorem mulS_eq_loop (A B : ℕ) :
    mulS A B = mulLoop (Nat.land A planeMask) (Nat.shiftRight A 2704) (Nat.land B planeMask)
      (Nat.shiftRight B 2704) 52 := by
  unfold mulS
  simp only [letN_eq]
  rfl

private theorem mm_spread_aux {xp : ℕ → ℕ} (hxp : ∀ i < 52, xp i < 2 ^ 52) {k : ℕ} (hk : k < 52) :
    (enc 52 xp 52 >>> k) &&& rowR = enc 52 (fun i => if (xp i).testBit k then 1 else 0) 52 := by
  have h1 : ∀ i < 52, (fun _ : ℕ => 1) i < 2 ^ 52 := fun _ _ => Nat.one_lt_two_pow (by norm_num)
  have hg : ∀ i < 52, (if (xp i).testBit k then 1 else 0) < 2 ^ 52 := fun i _ => by
    split_ifs
    · exact Nat.one_lt_two_pow (by norm_num)
    · exact Nat.two_pow_pos 52
  rw [rowR_eq]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  by_cases ht : t < 52 * 52
  · obtain ⟨i, j, hi, hj, rfl⟩ : ∃ i j, i < 52 ∧ j < 52 ∧ t = 52 * i + j :=
      ⟨t / 52, t % 52, by omega, by omega, by omega⟩
    rw [mm_testBit_enc h1 hi hj, mm_testBit_enc hg hi hj]
    by_cases hj0 : j = 0
    · subst hj0
      rw [show k + (52 * i + 0) = 52 * i + k by omega, mm_testBit_enc hxp hi hk]
      by_cases hb : (xp i).testBit k = true <;> simp [hb]
    · have h1j : (1 : ℕ).testBit j = false :=
        Bool.eq_false_iff.2 fun h => hj0 (Nat.testBit_one_eq_true_iff_self_eq_zero.1 h)
      simp only [h1j, Bool.and_false]
      split_ifs <;> simp [h1j]
  · rw [mm_testBit_enc_ge h1 (by omega), mm_testBit_enc_ge hg (by omega)]
    simp

private theorem mm_spread_enc {xp : ℕ → ℕ} (hxp : ∀ i < 52, xp i < 2 ^ 52) {k : ℕ} (hk : k < 52) :
    ((enc 52 xp 52 >>> k) &&& rowR) * rowF =
      enc 52 (fun i => if (xp i).testBit k then 2 ^ 52 - 1 else 0) 52 := by
  rw [mm_spread_aux hxp hk, mm_enc_mul_right, rowF_eq]
  apply enc_congr
  intro i hi
  split_ifs <;> simp

private theorem mm_bcast_enc {yp : ℕ → ℕ} (hyp : ∀ i < 52, yp i < 2 ^ 52) {k : ℕ} (hk : k < 52) :
    ((enc 52 yp 52 >>> (52 * k)) &&& rowF) * rowR = enc 52 (fun _ => yp k) 52 := by
  have h1 : (enc 52 yp 52 >>> (52 * k)) &&& rowF = yp k := by
    rw [rowF_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    exact fd_enc hyp hk
  rw [h1, rowR_eq, Nat.mul_comm, mm_enc_mul_right]
  apply enc_congr
  intro i hi
  exact Nat.one_mul _

private theorem mm_sel_lt (b : Bool) : (if b = true then 2 ^ 52 - 1 else 0) < 2 ^ 52 := by
  split_ifs
  · exact Nat.sub_lt (Nat.two_pow_pos 52) Nat.one_pos
  · exact Nat.two_pow_pos 52

private theorem mm_mulPlus_enc {xp xm yp ym : ℕ → ℕ} (hxp : ∀ i < 52, xp i < 2 ^ 52)
    (hxm : ∀ i < 52, xm i < 2 ^ 52) (hyp : ∀ i < 52, yp i < 2 ^ 52)
    (hym : ∀ i < 52, ym i < 2 ^ 52) {k : ℕ} (hk : k < 52) :
    mulPlus (enc 52 xp 52) (enc 52 xm 52) (enc 52 yp 52) (enc 52 ym 52) k =
      enc 52 (fun i => ((if (xp i).testBit k then 2 ^ 52 - 1 else 0) &&& yp k) |||
        ((if (xm i).testBit k then 2 ^ 52 - 1 else 0) &&& ym k)) 52 := by
  unfold mulPlus
  simp only [Nat.land_eq, Nat.lor_eq, Nat.mul_eq, Nat.shiftRight_eq']
  rw [mm_spread_enc hxp hk, mm_spread_enc hxm hk, mm_bcast_enc hyp hk, mm_bcast_enc hym hk,
    mm_enc_land (fun i _ => mm_sel_lt _) (fun _ _ => hyp k hk),
    mm_enc_land (fun i _ => mm_sel_lt _) (fun _ _ => hym k hk),
    mm_enc_lor (fun i _ => Nat.and_lt_two_pow _ (hyp k hk))
      (fun i _ => Nat.and_lt_two_pow _ (hym k hk))]

private theorem mm_mulMinus_enc {xp xm yp ym : ℕ → ℕ} (hxp : ∀ i < 52, xp i < 2 ^ 52)
    (hxm : ∀ i < 52, xm i < 2 ^ 52) (hyp : ∀ i < 52, yp i < 2 ^ 52)
    (hym : ∀ i < 52, ym i < 2 ^ 52) {k : ℕ} (hk : k < 52) :
    mulMinus (enc 52 xp 52) (enc 52 xm 52) (enc 52 yp 52) (enc 52 ym 52) k =
      enc 52 (fun i => ((if (xp i).testBit k then 2 ^ 52 - 1 else 0) &&& ym k) |||
        ((if (xm i).testBit k then 2 ^ 52 - 1 else 0) &&& yp k)) 52 := by
  unfold mulMinus
  simp only [Nat.land_eq, Nat.lor_eq, Nat.mul_eq, Nat.shiftRight_eq']
  rw [mm_spread_enc hxp hk, mm_spread_enc hxm hk, mm_bcast_enc hyp hk, mm_bcast_enc hym hk,
    mm_enc_land (fun i _ => mm_sel_lt _) (fun _ _ => hym k hk),
    mm_enc_land (fun i _ => mm_sel_lt _) (fun _ _ => hyp k hk),
    mm_enc_lor (fun i _ => Nat.and_lt_two_pow _ (hym k hk))
      (fun i _ => Nat.and_lt_two_pow _ (hyp k hk))]

private theorem mm_and_full {y : ℕ} (hy : y < 2 ^ 52) : (2 ^ 52 - 1) &&& y = y := by
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow hy

theorem mulPlusMinus_pk52 {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) {k : ℕ} (hk : k < 52) :
    mulPlus (pk52 X % 2 ^ 2704) (pk52 X / 2 ^ 2704) (pk52 Y % 2 ^ 2704) (pk52 Y / 2 ^ 2704) k =
        pk52 (termM X Y k) % 2 ^ 2704 ∧
      mulMinus (pk52 X % 2 ^ 2704) (pk52 X / 2 ^ 2704) (pk52 Y % 2 ^ 2704) (pk52 Y / 2 ^ 2704) k =
        pk52 (termM X Y k) / 2 ^ 2704 := by
  have hT := can52_termM hX hY hk
  obtain ⟨-, hX'⟩ := can52_iff.1 hX
  obtain ⟨-, hY'⟩ := can52_iff.1 hY
  have hap : ∀ i < 52, X[i]!.p < 2 ^ 52 := fun i hi => (hX' i hi).1
  have ham : ∀ i < 52, X[i]!.m < 2 ^ 52 := fun i hi => (hX' i hi).2.1
  have hbp : ∀ i < 52, Y[i]!.p < 2 ^ 52 := fun i hi => (hY' i hi).1
  have hbm : ∀ i < 52, Y[i]!.m < 2 ^ 52 := fun i hi => (hY' i hi).2.1
  have hnot : ∀ i < 52, X[i]!.p.testBit k = true → X[i]!.m.testBit k = false := by
    intro i hi hp
    have h := congrArg (fun x => x.testBit k) (hX' i hi).2.2
    simpa [Nat.testBit_and, hp] using h
  rw [pk52_mod hT, pk52_div hT, pk52_mod hX, pk52_div hX, pk52_mod hY, pk52_div hY,
    mm_mulPlus_enc hap ham hbp hbm hk, mm_mulMinus_enc hap ham hbp hbm hk]
  constructor <;> apply enc_congr <;> intro i hi <;> rw [mm_termM_getElem X Y k hi]
  · by_cases hp : X[i]!.p.testBit k = true
    · simp only [hp, hnot i hi hp, if_true, Bool.false_eq_true, if_false, Nat.zero_and,
        Nat.or_zero, mm_and_full (hbp k hk)]
    · by_cases hm : X[i]!.m.testBit k = true
      · simp only [hp, hm, if_true, Bool.false_eq_true, if_false, Nat.zero_and, Nat.zero_or,
          mm_and_full (hbm k hk)]
        rfl
      · simp only [hp, hm, Bool.false_eq_true, if_false, Nat.zero_and, Nat.or_zero]
        rfl
  · by_cases hp : X[i]!.p.testBit k = true
    · simp only [hp, hnot i hi hp, if_true, Bool.false_eq_true, if_false, Nat.zero_and,
        Nat.or_zero, mm_and_full (hbm k hk)]
    · by_cases hm : X[i]!.m.testBit k = true
      · simp only [hp, hm, if_true, Bool.false_eq_true, if_false, Nat.zero_and, Nat.zero_or,
          mm_and_full (hbp k hk)]
        rfl
      · simp only [hp, hm, Bool.false_eq_true, if_false, Nat.zero_and, Nat.or_zero]
        rfl

private theorem mm_pk52_mulPart_zero {X Y : Array V} (hX : Can52 X) : pk52 (mulPart 0 X Y) = 0 := by
  have h : ∀ i < 52, (mulPart 0 X Y)[i]! = V.zero := fun i hi => by
    rw [mm_mulPart_getElem _ _ _ (by rw [mm_size52 hX]; exact hi), Nat.fold_zero]
  unfold pk52
  rw [enc_congr (g := fun _ => 0) (fun i hi => congrArg V.p (h i hi)),
    enc_congr (g := fun _ => 0) (fun i hi => congrArg V.m (h i hi)), mm_enc_zero_fun,
    Nat.mul_zero]

private theorem mm_mulLoop_succ (Ap Am Bp Bm n : ℕ) : mulLoop Ap Am Bp Bm (n + 1) =
    addS (mulLoop Ap Am Bp Bm n % 2 ^ 2704) (mulLoop Ap Am Bp Bm n / 2 ^ 2704)
      (mulPlus Ap Am Bp Bm n) (mulMinus Ap Am Bp Bm n) := by
  have e1 : Nat.land (mulLoop Ap Am Bp Bm n) planeMask = mulLoop Ap Am Bp Bm n % 2 ^ 2704 := by
    rw [planeMask_eq, Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod]
  have e2 : Nat.shiftRight (mulLoop Ap Am Bp Bm n) 2704 = mulLoop Ap Am Bp Bm n / 2 ^ 2704 :=
    Nat.shiftRight_eq_div_pow _ _
  rw [← e1, ← e2]
  rfl

theorem mulLoop_pk52 {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) {n : ℕ} (hn : n ≤ 52) :
    mulLoop (pk52 X % 2 ^ 2704) (pk52 X / 2 ^ 2704) (pk52 Y % 2 ^ 2704) (pk52 Y / 2 ^ 2704) n =
      pk52 (mulPart n X Y) := by
  induction n with
  | zero => rw [mm_pk52_mulPart_zero hX]; rfl
  | succ n ih =>
    have hn' : n < 52 := by omega
    rw [mm_mulLoop_succ, ih (by omega), (mulPlusMinus_pk52 hX hY hn').1,
      (mulPlusMinus_pk52 hX hY hn').2, addS_pk52 (can52_mulPart hX hY (by omega))
        (can52_termM hX hY hn'), mulPart_succ hX hY hn']

theorem mulS_pk52 {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) :
    mulS (pk52 X) (pk52 Y) = pk52 (mul 52 X Y) := by
  have e1 : ∀ N : ℕ, Nat.land N planeMask = N % 2 ^ 2704 := fun N => by
    rw [planeMask_eq, Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod]
  have e2 : ∀ N : ℕ, Nat.shiftRight N 2704 = N / 2 ^ 2704 :=
    fun N => Nat.shiftRight_eq_div_pow _ _
  rw [mulS_eq_loop, e1, e2, e1, e2, mulLoop_pk52 hX hY le_rfl, mulPart_full]

theorem eqPMS_pk52 {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) :
    eqPMS (pk52 X) (pk52 Y) = eqPM X Y := by
  unfold eqPMS eqPM
  simp only [letB_eq, orB_eq]
  rw [negS_pk52 hY, beq_pk52 hX hY, beq_pk52 hX (can52_negM hY)]
  rfl

theorem mulI_eq (A B : ℕ) :
    mulI A B = if B = idS then A else if A = idS then B else mulS A B := by
  unfold mulI
  rw [letN_eq, letN_eq, letN_eq]
  by_cases hB : B = idS
  · have : Nat.beq B idS = true := by simp [hB]
    simp only [this, hB, if_true]
    rfl
  · have hB' : Nat.beq B idS = false := by
      cases h : Nat.beq B idS
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hB
    by_cases hA : A = idS
    · have hA' : Nat.beq A idS = true := by simp [hA]
      simp only [hB', hA', hB, hA, if_true, if_false]
      rfl
    · have hA' : Nat.beq A idS = false := by
        cases h : Nat.beq A idS
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hA
      simp only [hB', hA', hB, hA, if_false]

theorem mulI_pk52 {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) :
    mulI (pk52 X) (pk52 Y) = pk52 (mul 52 X Y) := by
  rw [mulI_eq]
  by_cases hB : pk52 Y = idS
  · have hY1 : Y = idM 52 := pk52_inj hY can52_idM (hB.trans idS_eq)
    rw [if_pos hB, hY1, mul52_one hX]
  · by_cases hA : pk52 X = idS
    · have hX1 : X = idM 52 := pk52_inj hX can52_idM (hA.trans idS_eq)
      rw [if_neg hB, if_pos hA, hX1, one_mul52 hY]
    · rw [if_neg hB, if_neg hA]
      exact mulS_pk52 hX hY

theorem commS_pk52 {X Y : Array V} (hX : Can52 X) (hY : Can52 Y) :
    commS (pk52 X) (pk52 Y) = commutes X Y := by
  unfold commS commutes
  rw [mulI_pk52 hX hY, mulI_pk52 hY hX, beq_pk52 (can52_mul hX hY) (can52_mul hY hX)]

theorem pk52_of_mulS_eq_idS {X Y : Array V} (hX : Can52 X) (hY : Can52 Y)
    (h : mul 52 X Y = idM 52) {N : ℕ} (hN : wfS N = true) (hmul : mulS (pk52 X) N = idS) :
    N = pk52 Y := by
  obtain ⟨Z, hZ, rfl⟩ := exists_pk52 hN
  rw [mulS_pk52 hX hZ, idS_eq] at hmul
  have h2 : mul 52 X Z = idM 52 := pk52_inj (can52_mul hX hZ) can52_idM hmul
  rw [inv_unique52 hX hY hZ h h2]

theorem mulS_idS_not_wf : ∃ A B : ℕ, wfS A = true ∧ wfS B = false ∧ mulS A B = idS := by
  refine ⟨(idS - 1 - 2 ^ 53 - 2 ^ 106) + (2 ^ 2 + 2 ^ 53 + 2 ^ 54 + 2 ^ 104 + 2 ^ 105) +
      2 ^ (2704 + 106),
    (idS - 1 - 2 ^ 53 - 2 ^ 106) + (1 + 2 ^ 2 + 2 ^ 53 + 2 ^ 104) + 2 ^ 2704 * (1 + 2 + 2 ^ 52),
    ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.KS.PK

end
