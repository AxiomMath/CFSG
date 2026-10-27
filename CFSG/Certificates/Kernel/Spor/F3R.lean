module

public import Certificates.Data.CFSGNative.F3.Conj

public section

namespace CFSG.KS.F3R

open CFSG.F3.Native

@[expose] def foldN {α : Type} (n : Nat) (f : Nat → α → α) (a : α) : α :=
  Nat.rec (motive := fun _ => α) a (fun i acc => f i acc) n

@[expose] def allNat (n : Nat) (p : Nat → Bool) : Bool := foldN n (fun i acc => acc && p i) true

theorem fold_eq {α : Type} (n : Nat) (f : Nat → α → α) (a : α) :
    Nat.fold n (fun i _ acc => f i acc) a = foldN n f a := by
  induction n with
  | zero =>
    rw [Nat.fold_zero]
    rfl
  | succ n ih =>
    rw [Nat.fold_succ, ih]
    rfl

theorem all_eq (n : Nat) (p : Nat → Bool) : Nat.all n (fun i _ => p i) = allNat n p := by
  induction n with
  | zero =>
    rw [Nat.all_zero]
    rfl
  | succ n ih =>
    rw [Nat.all_succ, ih]
    rfl

@[expose] def combK (d : Nat) (Y : Array V) (r : V) : V :=
  foldN d (fun j acc => if r.p.testBit j then acc.add Y[j]!
    else if r.m.testBit j then acc.sub Y[j]! else acc) V.zero

theorem comb_eq (d : Nat) (Y : Array V) (r : V) : comb d Y r = combK d Y r :=
  fold_eq d _ V.zero

@[expose] def mulK (d : Nat) (X Y : Array V) : Array V := X.map (combK d Y)

theorem mul_eq (d : Nat) (X Y : Array V) : mul d X Y = mulK d X Y := by
  unfold mul mulK
  congr 1
  funext r
  exact comb_eq d Y r

@[expose] def powMK (d : Nat) (M : Array V) : Nat → Array V
  | 0 => idM d
  | e + 1 => mulK d (powMK d M e) M

theorem powM_eq (d : Nat) (M : Array V) (e : Nat) : powM d M e = powMK d M e := by
  induction e with
  | zero => rfl
  | succ e ih => rw [powM, powMK, ih, mul_eq]

@[expose] def ofFnK (d : Nat) (f : Nat → Nat) : V :=
  foldN d (fun j v => if f j % 3 = 1 then ⟨v.p ||| (1 <<< j), v.m⟩
    else if f j % 3 = 2 then ⟨v.p, v.m ||| (1 <<< j)⟩ else v) V.zero

theorem ofFn_eq (d : Nat) (f : Nat → Nat) : V.ofFn d f = ofFnK d f := fold_eq d _ V.zero

@[expose] def rowsOfK (d : Nat) (s : String) : Array V :=
  let e := (decodeEntries s).toArray
  Array.ofFn (n := d) fun i => ofFnK d fun j => e[i.val * d + j]?.getD 0

theorem rowsOf_eq (d : Nat) (s : String) : rowsOf d s = rowsOfK d s := by
  unfold rowsOf rowsOfK
  simp only [ofFn_eq]

@[expose] def decodeL (cs : List Char) : List Nat :=
  let body := (cs.dropWhile (· != '\n')).drop 1
  (body.filter fun c => !wsChar c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

theorem decode_ofList (cs : List Char) : decodeEntries (String.ofList cs) = decodeL cs := by
  unfold decodeEntries decodeL
  rw [String.toList_ofList]

@[expose] def rowsOfL (d : Nat) (cs : List Char) : Array V :=
  let e := (decodeL cs).toArray
  Array.ofFn (n := d) fun i => ofFnK d fun j => e[i.val * d + j]?.getD 0

theorem rowsOf_ofList (d : Nat) (cs : List Char) : rowsOf d (String.ofList cs) = rowsOfL d cs := by
  rw [rowsOf_eq]
  unfold rowsOfK rowsOfL
  rw [decode_ofList]

@[expose] def transposeK (d : Nat) (X : Array V) : Array V :=
  Array.ofFn (n := d) fun j => ofFnK d fun i => X[i]!.get j.val

theorem transpose_eq (d : Nat) (X : Array V) : transpose d X = transposeK d X := by
  unfold transpose transposeK
  congr 1
  funext j
  exact ofFn_eq d _

@[expose] def eqMK (d : Nat) (X Y : Array V) : Bool :=
  X.size == d && Y.size == d && allNat d fun i => X[i]!.beq Y[i]!

theorem eqM_eq (d : Nat) (X Y : Array V) : eqM d X Y = eqMK d X Y := by
  unfold eqM eqMK
  rw [all_eq]

@[expose] def canonMK (d : Nat) (X : Array V) : Bool :=
  X.size == d && X.toList.all fun v => v.wf && v.p >>> d == 0 && v.m >>> d == 0

theorem canonM_eq (d : Nat) (X : Array V) : canonM d X = canonMK d X := by
  unfold canonM canonMK
  rw [← Array.all_toList]

@[expose] def wfMK (X : Array V) : Bool := X.toList.all V.wf

theorem wfM_eq (X : Array V) : wfM X = wfMK X := by
  unfold wfM wfMK
  rw [← Array.all_toList]

end CFSG.KS.F3R

end
