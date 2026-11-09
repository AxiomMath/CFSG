module

public import Certificates.Data.CFSGNative.F3.Basic

public section

namespace CFSG.F3.Planes

open CFSG.F3.Native

@[expose] def fp3Blk (d x i : Nat) : Nat := (x >>> (i * d)) % 2 ^ d

@[expose] def fp3Row (d : Nat) (M : V) (i : Nat) : V := ⟨fp3Blk d M.p i, fp3Blk d M.m i⟩

@[expose] def fp3Rows (d : Nat) (M : V) : Array V := Array.ofFn (n := d) fun i => fp3Row d M i.val

@[expose] def fp3Rep (d : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => fp3Rep d n * 2 ^ d + 1

@[expose] def fp3Spread (d k x : Nat) : Nat := ((x >>> k) &&& fp3Rep d d) * (2 ^ d - 1)

@[expose] def fp3Bcast (d k y : Nat) : Nat := fp3Rep d d * fp3Blk d y k

@[expose] def fp3Term (d : Nat) (X Y : V) (k : Nat) : V :=
  ⟨(fp3Spread d k X.p &&& fp3Bcast d k Y.p) ||| (fp3Spread d k X.m &&& fp3Bcast d k Y.m),
    (fp3Spread d k X.p &&& fp3Bcast d k Y.m) ||| (fp3Spread d k X.m &&& fp3Bcast d k Y.p)⟩

@[expose] noncomputable def fp3SB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun _ _ => k y) y

@[expose] noncomputable def fp3StepK (d R T Xp Xm Yp Ym k ap am : Nat) (K : Nat → Nat → Bool) :
    Bool :=
  fp3SB (Nat.mul (Nat.land (Nat.shiftRight Xp k) R) T) fun x1 =>
  fp3SB (Nat.mul (Nat.land (Nat.shiftRight Xm k) R) T) fun x2 =>
  fp3SB (Nat.mul R (Nat.mod (Nat.shiftRight Yp (Nat.mul k d)) (Nat.pow 2 d))) fun y1 =>
  fp3SB (Nat.mul R (Nat.mod (Nat.shiftRight Ym (Nat.mul k d)) (Nat.pow 2 d))) fun y2 =>
  fp3SB (Nat.lor (Nat.land x1 y1) (Nat.land x2 y2)) fun bp =>
  fp3SB (Nat.lor (Nat.land x1 y2) (Nat.land x2 y1)) fun bm =>
  fp3SB (Nat.lor ap am) fun a0 =>
  fp3SB (Nat.lor bp bm) fun b0 =>
  fp3SB (Nat.lor (Nat.lor (Nat.xor ap (Nat.land ap b0)) (Nat.xor bp (Nat.land bp a0)))
    (Nat.land am bm)) fun cp =>
  fp3SB (Nat.lor (Nat.lor (Nat.xor am (Nat.land am b0)) (Nat.xor bm (Nat.land bm a0)))
    (Nat.land ap bp)) fun cm =>
  K cp cm

@[expose] noncomputable def fp3LoopK (d R T Xp Xm Yp Ym : Nat) (n : Nat) :
    Nat → Nat → (Nat → Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → (Nat → Nat → Bool) → Bool) (fun ap am K => K ap am)
    (fun k ih ap am K => ih ap am fun bp bm => fp3StepK d R T Xp Xm Yp Ym k bp bm K) n

@[expose] def fp3Mul (d : Nat) (X Y : V) : V :=
  Nat.fold d (fun k _ acc => acc.add (fp3Term d X Y k)) V.zero

theorem testBit_fp3Blk (d x i j : Nat) :
    (fp3Blk d x i).testBit j = (decide (j < d) && x.testBit (i * d + j)) := by
  simp [fp3Blk, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem fp3Blk_and (d a b i : Nat) : fp3Blk d (a &&& b) i = fp3Blk d a i &&& fp3Blk d b i :=
  Nat.eq_of_testBit_eq fun j => by
    simp only [testBit_fp3Blk, Nat.testBit_and]
    cases decide (j < d) <;> simp

theorem fp3Blk_or (d a b i : Nat) : fp3Blk d (a ||| b) i = fp3Blk d a i ||| fp3Blk d b i :=
  Nat.eq_of_testBit_eq fun j => by
    simp only [testBit_fp3Blk, Nat.testBit_or]
    cases decide (j < d) <;> simp

theorem fp3Blk_xor (d a b i : Nat) : fp3Blk d (a ^^^ b) i = fp3Blk d a i ^^^ fp3Blk d b i :=
  Nat.eq_of_testBit_eq fun j => by
    simp only [testBit_fp3Blk, Nat.testBit_xor]
    cases decide (j < d) <;> simp

theorem fp3Blk_zero (d i : Nat) : fp3Blk d 0 i = 0 := by simp [fp3Blk]

theorem fp3Blk_mul_add_zero (d a : Nat) {r : Nat} (hr : r < 2 ^ d) :
    fp3Blk d (a * 2 ^ d + r) 0 = r := by
  rw [fp3Blk, Nat.zero_mul, Nat.shiftRight_zero, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hr]

theorem fp3Blk_mul_add_succ (d a : Nat) {r : Nat} (hr : r < 2 ^ d) (i : Nat) :
    fp3Blk d (a * 2 ^ d + r) (i + 1) = fp3Blk d a i := by
  have e : (a * 2 ^ d + r) >>> d = a := by
    rw [Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos d),
      Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [fp3Blk, fp3Blk, Nat.succ_mul, Nat.add_comm (i * d) d, Nat.shiftRight_add, e]

theorem fp3Blk_succ (d x i : Nat) : fp3Blk d x (i + 1) = fp3Blk d (x / 2 ^ d) i := by
  have h := fp3Blk_mul_add_succ d (x / 2 ^ d) (Nat.mod_lt x (Nat.two_pow_pos d)) i
  rwa [Nat.div_add_mod'] at h

theorem fp3Blk_zero_eq (d x : Nat) : fp3Blk d x 0 = x % 2 ^ d := by simp [fp3Blk]

theorem fp3Blk_mul {d m : Nat} (hm : m < 2 ^ d) :
    ∀ (i : Nat) {E : Nat}, (∀ i, fp3Blk d E i ≤ 1) → fp3Blk d (E * m) i = fp3Blk d E i * m := by
  intro i
  induction i with
  | zero =>
    intro E hE
    have h1 : E % 2 ^ d * m < 2 ^ d := by
      have := hE 0
      rw [fp3Blk_zero_eq] at this
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> rw [h] <;> omega
    have e : E * m = E / 2 ^ d * m * 2 ^ d + E % 2 ^ d * m := by
      rw [Nat.mul_right_comm (E / 2 ^ d) m (2 ^ d), ← Nat.add_mul, Nat.div_add_mod']
    rw [e, fp3Blk_mul_add_zero d _ h1, fp3Blk_zero_eq]
  | succ i ih =>
    intro E hE
    have h1 : E % 2 ^ d * m < 2 ^ d := by
      have := hE 0
      rw [fp3Blk_zero_eq] at this
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> rw [h] <;> omega
    have e : E * m = E / 2 ^ d * m * 2 ^ d + E % 2 ^ d * m := by
      rw [Nat.mul_right_comm (E / 2 ^ d) m (2 ^ d), ← Nat.add_mul, Nat.div_add_mod']
    rw [e, fp3Blk_mul_add_succ d _ h1, ih (fun j => by rw [← fp3Blk_succ]; exact hE (j + 1)),
      fp3Blk_succ]

theorem fp3Blk_fp3Rep {d : Nat} (hd : 0 < d) :
    ∀ (n i : Nat), fp3Blk d (fp3Rep d n) i = if i < n then 1 else 0
  | 0, i => by simp [fp3Rep, fp3Blk_zero]
  | n + 1, 0 => by
    rw [fp3Rep, fp3Blk_mul_add_zero d _ (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.1 hd))]
    simp
  | n + 1, i + 1 => by
    rw [fp3Rep, fp3Blk_mul_add_succ d _ (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.1 hd)),
      fp3Blk_fp3Rep hd n i]
    simp only [Nat.add_lt_add_iff_right]

theorem fp3Blk_lt (d x i : Nat) : fp3Blk d x i < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)

theorem fp3Blk_fp3Spread {d : Nat} (hd : 0 < d) (k x : Nat) {i : Nat} (hi : i < d) :
    fp3Blk d (fp3Spread d k x) i = if x.testBit (i * d + k) then 2 ^ d - 1 else 0 := by
  have hE : ∀ j, fp3Blk d ((x >>> k) &&& fp3Rep d d) j ≤ 1 := by
    intro j
    rw [fp3Blk_and, fp3Blk_fp3Rep hd]
    split
    · exact Nat.and_le_right
    · rw [Nat.and_zero]
      exact Nat.zero_le 1
  rw [fp3Spread, fp3Blk_mul (Nat.sub_lt (Nat.two_pow_pos d) Nat.one_pos) i hE, fp3Blk_and,
    fp3Blk_fp3Rep hd]
  simp only [hi, ↓reduceIte]
  have e : fp3Blk d (x >>> k) i &&& 1 = if x.testBit (i * d + k) then 1 else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, testBit_fp3Blk, Nat.testBit_shiftRight]
    rcases j with _ | j
    · split <;> simp_all [Nat.add_comm k]
    · split <;> simp [Nat.testBit_succ]
  rw [e]
  split <;> simp

theorem fp3Blk_fp3Bcast {d : Nat} (hd : 0 < d) (k y : Nat) {i : Nat} (hi : i < d) :
    fp3Blk d (fp3Bcast d k y) i = fp3Blk d y k := by
  rw [fp3Bcast, fp3Blk_mul (fp3Blk_lt d y k) i (fun j => by rw [fp3Blk_fp3Rep hd]; split <;> omega),
    fp3Blk_fp3Rep hd]
  simp only [hi, ↓reduceIte, Nat.one_mul]

theorem fp3And_ones {d a : Nat} (ha : a < 2 ^ d) : (2 ^ d - 1) &&& a = a := by
  rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt ha]

theorem fp3Row_fp3Term {d : Nat} (hd : 0 < d) (X Y : V) {k i : Nat} (hi : i < d)
    (hX : (X.p.testBit (i * d + k) && X.m.testBit (i * d + k)) = false) :
    fp3Row d (fp3Term d X Y k) i =
      if X.p.testBit (i * d + k) then fp3Row d Y k
      else if X.m.testBit (i * d + k) then (fp3Row d Y k).neg else V.zero := by
  simp only [fp3Row, fp3Term, fp3Blk_or, fp3Blk_and, fp3Blk_fp3Spread hd _ _ hi, fp3Blk_fp3Bcast hd _ _ hi]
  cases hp : X.p.testBit (i * d + k) <;> cases hm : X.m.testBit (i * d + k) <;>
    simp_all [V.neg, V.zero, fp3And_ones (fp3Blk_lt d _ _)]

theorem fp3Row_add (d : Nat) (a b : V) (i : Nat) :
    fp3Row d (a.add b) i = (fp3Row d a i).add (fp3Row d b i) := by
  simp only [fp3Row, V.add, fp3Blk_or, fp3Blk_and, fp3Blk_xor]

theorem fp3Add_zero (a : V) : a.add V.zero = a := by
  simp [V.add, V.zero]

theorem fp3Row_fold {d : Nat} (hd : 0 < d) {X Y : V} {i : Nat} (hi : i < d)
    (hX : (fp3Row d X i).wf = true) : ∀ n ≤ d,
      fp3Row d (Nat.fold n (fun k _ acc => acc.add (fp3Term d X Y k)) V.zero) i =
        Nat.fold n (fun j _ acc => if (fp3Row d X i).p.testBit j then acc.add (fp3Rows d Y)[j]!
          else if (fp3Row d X i).m.testBit j then acc.sub (fp3Rows d Y)[j]! else acc) V.zero
  | 0, _ => by simp [fp3Row, V.zero, fp3Blk_zero]
  | n + 1, hn => by
    have hnd : n < d := hn
    have hX' : (X.p.testBit (i * d + n) && X.m.testBit (i * d + n)) = false := by
      simp only [V.wf, fp3Row, beq_iff_eq] at hX
      have h := congrArg (Nat.testBit · n) hX
      simpa only [Nat.testBit_and, testBit_fp3Blk, hnd, decide_true, Bool.true_and,
        Nat.zero_testBit] using h
    have hY : (fp3Rows d Y)[n]! = fp3Row d Y n := by
      rw [fp3Rows, getElem!_pos (Array.ofFn _) n (by simpa using hnd), Array.getElem_ofFn]
    simp only [Nat.fold_succ]
    rw [fp3Row_add, fp3Row_fold hd hi hX n (Nat.le_of_lt hn), fp3Row_fp3Term hd X Y hi hX', hY]
    simp only [fp3Row, testBit_fp3Blk, hnd, decide_true, Bool.true_and]
    split
    · rfl
    · split
      · rfl
      · exact fp3Add_zero _

theorem fp3SB_eq (y : Nat) (k : Nat → Bool) : fp3SB y k = k y := by
  cases y <;> rfl

theorem fp3StepK_eq (d : Nat) (X Y : V) (k ap am : Nat) (K : Nat → Nat → Bool) :
    fp3StepK d (fp3Rep d d) (2 ^ d - 1) X.p X.m Y.p Y.m k ap am K =
      K ((V.mk ap am).add (fp3Term d X Y k)).p ((V.mk ap am).add (fp3Term d X Y k)).m := by
  simp only [fp3StepK, fp3SB_eq]
  rfl

theorem fp3LoopK_eq (d : Nat) (X Y : V) : ∀ (n ap am : Nat) (K : Nat → Nat → Bool),
    fp3LoopK d (fp3Rep d d) (2 ^ d - 1) X.p X.m Y.p Y.m n ap am K =
      K (Nat.fold n (fun k _ acc => acc.add (fp3Term d X Y k)) (V.mk ap am)).p
        (Nat.fold n (fun k _ acc => acc.add (fp3Term d X Y k)) (V.mk ap am)).m
  | 0, _, _, _ => by rw [Nat.fold_zero]; rfl
  | n + 1, ap, am, K => by
    change fp3LoopK d (fp3Rep d d) (2 ^ d - 1) X.p X.m Y.p Y.m n ap am
      (fun bp bm => fp3StepK d (fp3Rep d d) (2 ^ d - 1) X.p X.m Y.p Y.m n bp bm K) = _
    rw [fp3LoopK_eq d X Y n, fp3StepK_eq, Nat.fold_succ]

theorem fp3LoopK_fp3Mul (d : Nat) (X Y : V) (K : Nat → Nat → Bool) :
    fp3LoopK d (fp3Rep d d) (2 ^ d - 1) X.p X.m Y.p Y.m d 0 0 K =
      K (fp3Mul d X Y).p (fp3Mul d X Y).m :=
  fp3LoopK_eq d X Y d 0 0 K

theorem fp3Rows_fp3Mul {d : Nat} (hd : 0 < d) {X Y : V}
    (hX : ∀ i < d, (fp3Row d X i).wf = true) :
    fp3Rows d (fp3Mul d X Y) = mul d (fp3Rows d X) (fp3Rows d Y) := by
  rw [mul]
  change Array.ofFn _ = (Array.ofFn _).map _
  rw [Array.map_ofFn]
  congr 1
  funext i
  exact fp3Row_fold hd i.isLt (hX i i.isLt) d (Nat.le_refl d)

end CFSG.F3.Planes

end
