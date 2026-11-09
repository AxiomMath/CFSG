module

public import Certificates.Data.Kernel.PGrp
public import CFSG.Certificates.Kernel.Enum.DefsC
public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Benes
meta import all CFSG.Certificates.Kernel.Common.Benes

open Lean Elab Command

public section

namespace CFSG.KC.PGrp

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def posFrom (n w : Nat) (G : Nat → Nat) (wd : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (pcomp n w (mask w) acc (G l)) ih) wd acc

@[expose] noncomputable def posFromC (n w : Nat) (G : Nat → Nat) (wd : List Nat) (acc : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (pcompC n w (mask w) acc (G l)) ih) wd acc

@[expose] noncomputable def posPart (n w : Nat) (G : Nat → Nat) (X : Nat) (wd : List Nat) (Y : Nat) :
    Bool :=
  Nat.beq (posFromC n w G wd X) Y

theorem strictN_eq_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem posWordK_eq_from (n w : Nat) (G : Nat → Nat) (wd : List Nat) :
    posWordK n w G wd = posFrom n w G wd (pidn n w) := rfl

theorem posFrom_nil (n w : Nat) (G : Nat → Nat) (acc : Nat) : posFrom n w G [] acc = acc := rfl

theorem posFrom_cons (n w : Nat) (G : Nat → Nat) (x : Nat) (wd : List Nat) (acc : Nat) :
    posFrom n w G (x :: wd) acc = posFrom n w G wd (pcomp n w (mask w) acc (G x)) :=
  strictN_eq_app _ _

theorem posFromC_cons (n w : Nat) (G : Nat → Nat) (x : Nat) (wd : List Nat) (acc : Nat) :
    posFromC n w G (x :: wd) acc = posFromC n w G wd (pcompC n w (mask w) acc (G x)) :=
  strictN_eq_app _ _

theorem posFrom_eq_C (n w : Nat) (G : Nat → Nat) :
    ∀ (wd : List Nat) (acc : Nat), posFrom n w G wd acc = posFromC n w G wd acc
  | [], _ => rfl
  | x :: wd, acc => by
    rw [posFrom_cons, posFromC_cons, CFSG.KS.PK.pcompC_eq, posFrom_eq_C n w G wd]

theorem posFrom_append (n w : Nat) (G : Nat → Nat) :
    ∀ (a b : List Nat) (acc : Nat),
      posFrom n w G (a ++ b) acc = posFrom n w G b (posFrom n w G a acc)
  | [], _, _ => rfl
  | x :: a, b, acc => by
    rw [List.cons_append, posFrom_cons, posFrom_cons, posFrom_append n w G a b]

theorem posFrom_of_part (n w : Nat) (G : Nat → Nat) (X : Nat) (wd : List Nat) (Y : Nat)
    (p : posPart n w G X wd Y = true) : posFrom n w G wd X = Y := by
  rw [posFrom_eq_C]
  exact Nat.eq_of_beq_eq_true p

theorem posFrom_drop_step (n w : Nat) (G : Nat → Nat) (l : List Nat) (a b c X Y Z : Nat)
    (hc : a + b = c) (p : posPart n w G X ((l.drop a).take b) Y = true)
    (h : posFrom n w G (l.drop c) Y = Z) : posFrom n w G (l.drop a) X = Z := by
  subst hc
  have e : l.drop a = (l.drop a).take b ++ l.drop (a + b) := by
    rw [← List.drop_drop]
    exact (List.take_append_drop b (l.drop a)).symm
  have e2 : posFrom n w G (l.drop a) X = posFrom n w G ((l.drop a).take b ++ l.drop (a + b)) X :=
    congrArg (fun t => posFrom n w G t X) e
  rw [e2, posFrom_append, posFrom_of_part n w G X _ Y p, h]

theorem posWordK_of_drop0 (n w : Nat) (G : Nat → Nat) (l : List Nat) (X Z r : Nat)
    (hid : pidn n w = X) (h : posFrom n w G (l.drop (nat_lit 0)) X = Z) (hr : Z = r) :
    posWordK n w G l = r := by
  rw [posWordK_eq_from, hid, ← hr, ← h, List.drop_zero]

end CFSG.KC.PGrp

namespace CFSG.KC.PGrp.PosWordSplit

meta def litN (n : Nat) : Expr := mkRawNatLit n

meta def reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

meta def reflNat (n : Nat) : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (litN n)

meta def isTrueE (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

meta def natE : Expr := mkConst ``Nat

meta def dropE (a l : Expr) : Expr := mkApp3 (mkConst ``List.drop [0]) natE a l

meta def takeE (b l : Expr) : Expr := mkApp3 (mkConst ``List.take [0]) natE b l

meta partial def listLen (l : Expr) (acc : Nat := 0) : CoreM Nat := do
  match Kernel.whnf (← getEnv) {} l with
  | .ok e =>
    if e.isAppOfArity ``List.cons 3 then listLen e.appArg! (acc + 1)
    else if e.isAppOfArity ``List.nil 1 then return acc
    else throwError "#kc_posword_split: the word does not reduce to a list literal ({e.getAppFn})"
  | .error ex => throwKernelException ex

end CFSG.KC.PGrp.PosWordSplit

open CFSG.KC.PGrp.PosWordSplit in
elab "#kc_posword_split " id:ident ll:num " : " t:term : command => do
  let name := (← getCurrNamespace) ++ id.getId
  let L := ll.getNat
  let ty ← liftTermElabM do
    let e ← Term.elabTerm t (some (mkSort Level.zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  if ty.hasMVar || ty.hasFVar then throwError "#kc_posword_split: the statement is not closed"
  let some (_, lhs, r) := ty.eq? | throwError "#kc_posword_split: expected `posWordK … = r`"
  unless lhs.isAppOfArity ``CFSG.KC.PGrp.posWordK 4 do
    throwError "#kc_posword_split: expected a posWordK product"
  let a := lhs.getAppArgs
  let nE := a[0]!
  let wE := a[1]!
  let G := a[2]!
  let l := a[3]!
  liftCoreM <| withOptions (Elab.async.set · false) do
    let len ← listLen l
    let k := max 1 ((len + L - 1) / L)
    let cut := fun (i : Nat) => len * i / k
    let slice := fun (i : Nat) =>
      if i + 1 < k then takeE (litN (cut (i + 1) - cut i)) (dropE (litN (cut i)) l)
      else dropE (litN (cut i)) l
    let mut X : Array Nat := Array.replicate (k + 1) 0
    let idv ← CFSG.KC.Benes.kNat "identity" (mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE)
    X := X.set! 0 idv
    for i in [0:k] do
      let v ← CFSG.KC.Benes.kNat "piece"
        (mkAppN (mkConst ``CFSG.KC.PGrp.posFromC) #[nE, wE, G, slice i, litN X[i]!])
      X := X.set! (i + 1) v
    let pname := fun (i : Nat) => name.appendAfter s!"_p{i}"
    for i in [0:k] do
      let pty := isTrueE (mkAppN (mkConst ``CFSG.KC.PGrp.posPart)
        #[nE, wE, G, litN X[i]!, slice i, litN X[i + 1]!])
      CFSG.KC.addThmDecl { name := pname i, levelParams := [], type := pty, value := reflTrue }
    let mut h := mkAppN (mkConst ``CFSG.KC.PGrp.posFrom_of_part)
      #[nE, wE, G, litN X[k - 1]!, slice (k - 1), litN X[k]!, mkConst (pname (k - 1))]
    for t in [0:k - 1] do
      let i := k - 2 - t
      let b := cut (i + 1) - cut i
      h := mkAppN (mkConst ``CFSG.KC.PGrp.posFrom_drop_step)
        #[nE, wE, G, l, litN (cut i), litN b, litN (cut (i + 1)), litN X[i]!, litN X[i + 1]!,
          litN X[k]!, reflNat (cut (i + 1)), mkConst (pname i), h]
    let pf := mkAppN (mkConst ``CFSG.KC.PGrp.posWordK_of_drop0)
      #[nE, wE, G, l, litN X[0]!, litN X[k]!, r, reflNat X[0]!, h, reflNat X[k]!]
    CFSG.KC.addThmDecl { name, levelParams := [], type := ty, value := pf }

end
