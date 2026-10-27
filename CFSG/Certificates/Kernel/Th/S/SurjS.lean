module

public import CFSG.Certificates.Kernel.Th.S.SeedS
public import CFSG.Certificates.Kernel.Th.S.BigS

public section

namespace CFSG.KC.Th.SurjS

open CFSG.KC.Th CFSG.KC.Loop CFSG.KC.Th.SeedS

@[expose] noncomputable def hexD (n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 16) (Nat.sub n (nat_lit 87))
      (andB (Nat.ble (nat_lit 97) n) (Nat.ble n (nat_lit 102))))
    (Nat.sub n (nat_lit 48))
    (andB (Nat.ble (nat_lit 48) n) (Nat.ble n (nat_lit 57)))

@[expose] noncomputable def textRow (RB : Nat → Nat) (rm q : Nat) : Nat :=
  rowB rm (RB (Nat.succ (Nat.div q (nat_lit 248)))) (Nat.mod q (nat_lit 248))

@[expose] noncomputable def textRun (RB : Nat → Nat) (rm : Nat) (l : List Char) :
    Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun q j _ => andB (Nat.beq q (nat_lit 1984)) (Nat.beq j (nat_lit 0)))
    (fun ch _ ih q j acc => strictB (Char.toNat ch) fun n =>
      Bool.rec (motive := fun _ => Bool)
        ((fun d => Bool.rec (motive := fun _ => Bool) false
            (strictB (Nat.add acc (Nat.shiftLeft d (Nat.mul (nat_lit 4) j))) fun a =>
              strictB (Nat.succ j) fun j1 => ih q j1 a)
            (andB (Nat.blt d (nat_lit 16)) (Nat.blt j (nat_lit 62)))) (hexD n))
        (andB (andB (Nat.beq j (nat_lit 62)) (Nat.blt q (nat_lit 1984)))
          (andB (Nat.beq (textRow RB rm q) acc)
            (strictB (Nat.succ q) fun q1 => ih q1 (nat_lit 0) (nat_lit 0))))
        (Nat.beq n (nat_lit 10)))
    l

@[expose] noncomputable def textOK (RB : Nat → Nat) (rm : Nat) (l : List Char) : Bool :=
  textRun RB rm l (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def layoutOK (c rm M : Nat) : Bool := Nat.beq (Nat.land M (Nat.mul rm c)) M

@[expose] noncomputable def regsOK (RB : Nat → Nat) (c rm ONE : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun g ih => andB ih (andB (andB (layoutOK c rm (RB (Nat.succ g)))
      (layoutOK c rm (RB (Nat.add g (nat_lit 9)))))
      (Nat.beq (mulB c rm (RB (Nat.succ g)) (RB (Nat.add g (nat_lit 9)))) ONE)))
    (nat_lit 8)

@[expose] noncomputable def regList (off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (Nat.add off (Nat.succ k)) (Nat.mul (nat_lit 11) k)))
    (nat_lit 8)

@[expose] noncomputable def GR : Nat := regList (nat_lit 0)

@[expose] noncomputable def IR : Nat := regList (nat_lit 8)

@[expose] noncomputable def wordV (RB : Nat → Nat) (c rm : Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => strictN (mulB c rm acc (BigS.letV RB GR IR x)) ih) w

@[expose] noncomputable def letterChars (x : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat)
    [Nat.add (nat_lit 49) (Nat.shiftRight x (nat_lit 1))]
    [nat_lit 45, Nat.add (nat_lit 49) (Nat.shiftRight x (nat_lit 1))]
    (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def wordChars (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [nat_lit 10]
    (fun x t ih => List.append (letterChars x)
      (List.rec (motive := fun _ => List Nat) [nat_lit 10] (fun _ _ _ => nat_lit 32 :: ih) t)) w

@[expose] noncomputable def wordsChars (ws : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w _ ih => List.append (wordChars w) ih) ws

@[expose] noncomputable def lettersOK (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB ih (andB (List.rec (motive := fun _ => Bool) false (fun _ _ _ => true) w)
      (List.rec (motive := fun _ => Bool) true
        (fun x _ ih2 => andB ih2 (Nat.blt (Nat.shiftRight x (nat_lit 1)) (nat_lit 8))) w)))
    ws

@[expose] noncomputable def codesEq (l : List Char) (m : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun ch _ ih m => List.rec (motive := fun _ => Bool) false
      (fun y t _ => andB (Nat.beq (Char.toNat ch) y) (ih t)) m) l m

@[expose] noncomputable def wordsOK (l : List Char) (ws : List (List Nat)) : Bool :=
  andB (lettersOK ws) (codesEq l (wordsChars ws))

end CFSG.KC.Th.SurjS

end
