module

public import CFSG.Certificates.Kernel.Spor.WordAccC
public import CFSG.Certificates.Kernel.Spor.PK.Perm.WordAppend
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Benes
meta import all CFSG.Certificates.Kernel.Common.Benes

open Lean Elab Command

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def wordAccPart (n w X : Nat) (S SI : Nat → Nat) (wd : List Int) (Y : Nat) :
    Bool :=
  Nat.beq (wordAccC n w X S SI wd) Y

theorem wordK_drop_last (n w idn : Nat) (S SI : Nat → Nat) (l : List Int) (c X : Nat)
    (p : wordAccPart n w idn S SI (l.drop c) X = true) :
    wordK n w (mask w) idn S SI (l.drop c) = X := by
  rw [wordK_eq_C]
  exact Nat.eq_of_beq_eq_true p

theorem wordK_drop_step (n w idn : Nat) (S SI : Nat → Nat) (l : List Int) (a b c X Y : Nat)
    (hc : a + b = c) (p : wordAccPart n w X S SI ((l.drop a).take b) Y = true)
    (h : wordK n w (mask w) idn S SI (l.drop c) = X) :
    wordK n w (mask w) idn S SI (l.drop a) = Y := by
  subst hc
  have e : l.drop a = (l.drop a).take b ++ l.drop (a + b) := by
    rw [← List.drop_drop]
    exact (List.take_append_drop b (l.drop a)).symm
  rw [show wordK n w (mask w) idn S SI (l.drop a) =
      wordK n w (mask w) idn S SI ((l.drop a).take b ++ l.drop (a + b)) from congrArg _ e,
    wordK_append, h, wordK_eq_C]
  exact Nat.eq_of_beq_eq_true p

theorem wordEqK_of_drop0 (n w idn : Nat) (S SI : Nat → Nat) (kS : Nat) (l : List Int) (r : Nat)
    (h : wordK n w (mask w) idn S SI (l.drop (nat_lit 0)) = r) (hs : szOK n w = true)
    (hl : lettersK kS l = true) :
    CFSG.KS.Prim.wordEqK n w (mask w) idn S SI kS l r = true :=
  wordEqK_of_word (by rw [List.drop_zero] at h; exact h) hs hl

end CFSG.KS.Raw

namespace CFSG.KS.Raw.WordSplit

meta def litN (n : Nat) : Expr := mkRawNatLit n

meta def reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

meta def isTrueE (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

meta def intE : Expr := mkConst ``Int

meta def dropE (a l : Expr) : Expr := mkApp3 (mkConst ``List.drop [0]) intE a l

meta def takeE (b l : Expr) : Expr := mkApp3 (mkConst ``List.take [0]) intE b l

meta partial def listLen (l : Expr) (acc : Nat := 0) : CoreM Nat := do
  match Kernel.whnf (← getEnv) {} l with
  | .ok e =>
    if e.isAppOfArity ``List.cons 3 then listLen e.appArg! (acc + 1)
    else if e.isAppOfArity ``List.nil 1 then return acc
    else throwError "#kc_wordeq_split: the word does not reduce to a list literal ({e.getAppFn})"
  | .error ex => throwKernelException ex

end CFSG.KS.Raw.WordSplit

open CFSG.KS.Raw.WordSplit in
elab "#kc_wordeq_split " id:ident ll:num " : " t:term : command => do
  let name := (← getCurrNamespace) ++ id.getId
  let L := ll.getNat
  let ty ← liftTermElabM do
    let e ← Term.elabTerm t (some (mkSort Level.zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  if ty.hasMVar || ty.hasFVar then throwError "#kc_wordeq_split: the statement is not closed"
  let some (_, lhs, _) := ty.eq? | throwError "#kc_wordeq_split: expected `… = true`"
  unless lhs.isAppOfArity ``CFSG.KS.Prim.wordEqK 9 do
    throwError "#kc_wordeq_split: expected a wordEqK check"
  let a := lhs.getAppArgs
  let nE := a[0]!
  let wE := a[1]!
  let idn := a[3]!
  let S := a[4]!
  let SI := a[5]!
  let kS := a[6]!
  let l := a[7]!
  let r := a[8]!
  liftCoreM <| withOptions (Elab.async.set · false) do
    let len ← listLen l
    let k := max 1 ((len + L - 1) / L)
    let cut := fun (i : Nat) => len * i / k
    let mut X : Array Nat := Array.replicate (k + 1) 0
    let idv ← CFSG.KC.Benes.kNat "identity" idn
    X := X.set! k idv
    let accC := fun (start : Expr) (wd : Expr) => mkAppN (mkConst ``CFSG.KS.Raw.wordAccC)
      #[nE, wE, start, S, SI, wd]
    let vLast ← CFSG.KC.Benes.kNat "piece" (accC idn (dropE (litN (cut (k - 1))) l))
    X := X.set! (k - 1) vLast
    for t in [0:k - 1] do
      let i := k - 2 - t
      let chunk := takeE (litN (cut (i + 1) - cut i)) (dropE (litN (cut i)) l)
      let v ← CFSG.KC.Benes.kNat "piece" (accC (litN X[i + 1]!) chunk)
      X := X.set! i v
    let pname := fun (i : Nat) => name.appendAfter s!"_p{i}"
    let lastTy := isTrueE (mkAppN (mkConst ``CFSG.KS.Raw.wordAccPart)
      #[nE, wE, idn, S, SI, dropE (litN (cut (k - 1))) l, litN X[k - 1]!])
    CFSG.KC.addThmDecl { name := pname (k - 1), levelParams := [], type := lastTy, value := reflTrue }
    for i in [0:k - 1] do
      let chunk := takeE (litN (cut (i + 1) - cut i)) (dropE (litN (cut i)) l)
      let pty := isTrueE (mkAppN (mkConst ``CFSG.KS.Raw.wordAccPart)
        #[nE, wE, litN X[i + 1]!, S, SI, chunk, litN X[i]!])
      CFSG.KC.addThmDecl { name := pname i, levelParams := [], type := pty, value := reflTrue }
    let mut h := mkAppN (mkConst ``CFSG.KS.Raw.wordK_drop_last)
      #[nE, wE, idn, S, SI, l, litN (cut (k - 1)), litN X[k - 1]!, mkConst (pname (k - 1))]
    for t in [0:k - 1] do
      let i := k - 2 - t
      let b := cut (i + 1) - cut i
      let hc := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (litN (cut (i + 1)))
      h := mkAppN (mkConst ``CFSG.KS.Raw.wordK_drop_step)
        #[nE, wE, idn, S, SI, l, litN (cut i), litN b, litN (cut (i + 1)), litN X[i + 1]!,
          litN X[i]!, hc, mkConst (pname i), h]
    let hr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (litN X[0]!)
    let hX := mkAppN (mkConst ``Eq.trans [1])
      #[mkConst ``Nat, mkAppN (mkConst ``CFSG.KS.Raw.wordK)
        #[nE, wE, mkApp (mkConst ``CFSG.KS.mask) wE, idn, S, SI, dropE (litN 0) l], litN X[0]!, r, h, hr]
    let hs := reflTrue
    let hl := reflTrue
    let pf := mkAppN (mkConst ``CFSG.KS.Raw.wordEqK_of_drop0) #[nE, wE, idn, S, SI, kS, l, r, hX, hs, hl]
    CFSG.KC.addThmDecl { name, levelParams := [], type := ty, value := pf }

end
