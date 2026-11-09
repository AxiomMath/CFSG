module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.BabyMonster.Twin
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.BabyMonster.FourSound
public import Lean.Message

public section

namespace CFSG.KC.BM.LoadChain

open CFSG.KC.BM

theorem mulW4_chain {B : List Nat} {Ws Ds : List (List Nat)}
    {A0 A1 A2 A3 M0 M1 M2 M3 C0 C1 C2 C3 : Nat}
    (h1 : mulW4 [B] A0 A1 A2 A3 (rhs4 [] M0 M1 M2 M3) = true)
    (h2 : mulW4 Ws M0 M1 M2 M3 (rhs4 Ds C0 C1 C2 C3) = true) :
    mulW4 (B :: Ws) A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true := by
  obtain ⟨e0, e1, e2, e3⟩ := F4.mulW4_sound h1
  have g : ∀ {A M : Nat}, Nat.beq (mulW [B] A) (mulW [] M) = true →
      mulW (B :: Ws) A = mulW Ws M := by
    intro A M h
    have e : mulS B A = M := by
      have h' := Nat.eq_of_beq_eq_true h
      rw [F4.mulW_cons] at h'
      exact h'
    rw [F4.mulW_cons, e]
  rw [F4.mulW4_eq, F4.rhs4_eq] at h2
  rw [F4.mulW4_eq, F4.rhs4_eq, g e0, g e1, g e2, g e3]
  exact h2

theorem mulWn_chain {n : Nat} {B : List Nat} {Ws : List (List Nat)} {x y z : Nat}
    (h1 : Nat.beq (mulWn n [B] x) y = true) (h2 : Nat.beq (mulWn n Ws y) z = true) :
    Nat.beq (mulWn n (B :: Ws) x) z = true := by
  have e : mulWn n [B] x = y := Nat.eq_of_beq_eq_true h1
  rw [SL.mulWn_cons, SL.mulWn_nil] at e
  rw [SL.mulWn_cons, e]
  exact h2

theorem mulW_chain {B : List Nat} {Ws : List (List Nat)} {x y z : Nat}
    (h1 : Nat.beq (mulW [B] x) y = true) (h2 : Nat.beq (mulW Ws y) z = true) :
    Nat.beq (mulW (B :: Ws) x) z = true := by
  have e : mulW [B] x = y := Nat.eq_of_beq_eq_true h1
  rw [F4.mulW_cons] at e
  change mulS B x = y at e
  rw [F4.mulW_cons, e]
  exact h2

theorem beq_join {x y v : Nat} (h1 : Nat.beq x v = true) (h2 : Nat.beq y v = true) :
    Nat.beq x y = true := by
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  exact Nat.beq_refl v

end CFSG.KC.BM.LoadChain

end

namespace CFSG.KC.BM.LoadChain

open Lean Elab Command

meta def N : Nat := 4370

meta def natE : Expr := mkConst ``Nat
meta def listNatE : Expr := mkApp (mkConst ``List [0]) natE
meta def boolE : Expr := mkConst ``Bool

meta def mkList (ty : Expr) (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) ty e acc) (mkApp (mkConst ``List.nil [0]) ty)

meta def rel (P : Name) (n : Name) : Name :=
  let r := n.getRoot
  if r == `CFSG || r == `Nat || r == `Bool || r == `List then n else P ++ n

meta def stripName (P M : Name) (j : Nat) : Name := rel P M ++ Name.mkSimple s!"s{j}"

meta def stripE (P M : Name) (j : Nat) : Expr :=
  if (N + 63) / 64 ≤ j then mkRawNatLit 0
  else if M == `I then mkApp (mkConst `CFSG.KC.BM.idS) (mkRawNatLit j)
  else mkConst (stripName P M j)

meta def wordE (P : Name) (ws : Array Name) : Expr :=
  mkList listNatE (ws.map fun w => mkConst (rel P w))

meta def trueEq (b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolE b (mkConst ``Bool.true)

meta partial def litOf? : Expr → Option Nat
  | .lit (.natVal v) => some v
  | .mdata _ e => litOf? e
  | _ => none

meta def readLit (n : Name) : CoreM Nat := do
  let some v := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "#bm_mul4c: {n} has no value"
  let some x := litOf? v | throwError "#bm_mul4c: {n} is not a numeral"
  return x

meta def idStrip (n s : Nat) : Nat :=
  let r := min 64 (n - 64 * s)
  (((1 <<< (65 * r)) - 1) / ((1 <<< 65) - 1)) <<< (4096 * s)

meta def readMat (n : Nat) (P M : Name) : CoreM (Array Nat) :=
  (Array.range ((n + 63) / 64)).mapM fun j =>
    if M == `I then pure (idStrip n j) else readLit (stripName P M j)

meta def addNat (name : Name) (v : Nat) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type := natE, value := mkRawNatLit v, hints := .regular 0,
      safety := .safe }

meta def addThm (name : Name) (type value : Expr) : CoreM Unit :=
  CFSG.KC.addThmDecl { name, levelParams := [], type, value }

meta def check4 (W : Expr) (a : Nat → Expr) (D : Expr) (c : Nat → Expr) (j : Nat) : Expr :=
  mkAppN (mkConst `CFSG.KC.BM.mulW4) #[W, a j, a (j + 1), a (j + 2), a (j + 3),
    mkAppN (mkConst `CFSG.KC.BM.rhs4) #[D, c j, c (j + 1), c (j + 2), c (j + 3)]]

meta def mul4Chain (P T A : Name) (Bs : Array Name) (C : Name) (Ds : Array Name) :
    CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) do
    let k := Bs.size
    if k < 2 then throwError "#bm_mul4c: a word of {k} letters; use #bm_mul4"
    let ns := (N + 63) / 64
    let t0 ← IO.monoNanosNow
    let mut cur ← readMat N P A
    for i in [1:k] do
      cur := CFSG.KC.BM.Twin.mulStrips N cur (← readMat N P Bs[i - 1]!)
      for j in [0:ns] do
        addNat (P ++ T ++ Name.mkSimple s!"m{i}" ++ Name.mkSimple s!"s{j}") cur[j]!
    let t1 ← IO.monoNanosNow
    let lvl (i j : Nat) : Expr :=
      if i == 0 then stripE P A j
      else if ns ≤ j then mkRawNatLit 0
      else mkConst (P ++ T ++ Name.mkSimple s!"m{i}" ++ Name.mkSimple s!"s{j}")
    let nilW := mkApp (mkConst ``List.nil [0]) listNatE
    let dsE := wordE P Ds
    let cS := stripE P C
    for g in [0:(ns + 3) / 4] do
      let j := 4 * g
      let stepN (i : Nat) : Name := P ++ T ++ Name.mkSimple s!"c{i}_g{g}"
      for i in [1:k + 1] do
        let (D, c) := if i == k then (dsE, cS) else (nilW, lvl i)
        addThm (stepN i) (trueEq (check4 (wordE P #[Bs[i - 1]!]) (lvl (i - 1)) D c j)) reflBoolTrue
      let mut pf := mkConst (stepN k)
      for i' in [1:k] do
        let i := k - i'
        let rest := wordE P (Bs.extract i k)
        pf := mkAppN (mkConst ``CFSG.KC.BM.LoadChain.mulW4_chain)
          (#[mkConst (rel P Bs[i - 1]!), rest, dsE] ++
            ((Array.range 4).map fun t => lvl (i - 1) (j + t)) ++
            ((Array.range 4).map fun t => lvl i (j + t)) ++
            ((Array.range 4).map fun t => cS (j + t)) ++ #[mkConst (stepN i), pf])
      addThm (P ++ T.appendAfter s!"_g{g}") (trueEq (check4 (wordE P Bs) (stripE P A) dsE cS j)) pf
    let t2 ← IO.monoNanosNow
    let ms (a b : Nat) : Float := (b - a).toFloat / 1e6
    logInfo m!"BMTIME {T} products {ms t0 t1} checks {ms t1 t2} ms"

meta def mulnChain (plain : Bool) (P : Name) (n : Nat) (T A : Name) (Bs : Array Name) (C : Name)
    (Ds : Array Name) : CommandElabM Unit :=
  liftCoreM <| withOptions (Elab.async.set · false) do
    unless 4352 < n && n ≤ 4416 do throwError "#bm_mulnc: dimension {n}"
    let ns := (n + 63) / 64
    let nE := mkRawNatLit n
    let strip (M : Name) (j : Nat) : Expr :=
      if M == `I then
        if plain then mkApp (mkConst `CFSG.KC.BM.idS) (mkRawNatLit j)
        else mkApp2 (mkConst `CFSG.KC.BM.idSn) nE (mkRawNatLit j)
      else mkConst (stripName P M j)
    let word (ws : Array Name) : Expr :=
      let l := mkList listNatE (ws.map fun w => mkConst (rel P w))
      if plain then mkApp (mkConst `CFSG.KC.BM.mulW) l else mkApp2 (mkConst `CFSG.KC.BM.mulWn) nE l
    let chainC := if plain then ``CFSG.KC.BM.LoadChain.mulW_chain else ``CFSG.KC.BM.LoadChain.mulWn_chain
    let chainPre : Array Expr := if plain then #[] else #[nE]
    let t0 ← IO.monoNanosNow
    let Bm ← Bs.mapM (readMat n P)
    let Dm ← Ds.mapM (readMat n P)
    let a ← readMat n P A
    let c ← readMat n P C
    let t1 ← IO.monoNanosNow
    for j in [0:ns] do
      let J := P ++ T.appendAfter s!"_{j}"
      let side (s : String) (x0 : Expr) (x0v : Nat) (Ws : Array Name) (Wm : Array (Array Nat))
          (v : Expr) : CoreM Expr := do
        if Ws.isEmpty then
          let nm := J ++ Name.mkSimple s!"{s}0"
          addThm nm (trueEq (mkApp2 (mkConst ``Nat.beq) (mkApp (word #[]) x0) v)) reflBoolTrue
          return mkConst nm
        let mut xs : Array Expr := #[x0]
        let mut xv := x0v
        for i in [1:Ws.size] do
          xv := (CFSG.KC.BM.Twin.mulStrips n #[xv] Wm[i - 1]!)[0]!
          let nm := J ++ Name.mkSimple s!"{s}{i}"
          addNat nm xv
          xs := xs.push (mkConst nm)
        xs := xs.push v
        let stepN (i : Nat) : Name := J ++ Name.mkSimple s!"{s}_c{i}"
        for i in [1:Ws.size + 1] do
          addThm (stepN i)
            (trueEq (mkApp2 (mkConst ``Nat.beq) (mkApp (word #[Ws[i - 1]!]) xs[i - 1]!) xs[i]!))
            reflBoolTrue
        let mut pf := mkConst (stepN Ws.size)
        for i' in [1:Ws.size] do
          let i := Ws.size - i'
          pf := mkAppN (mkConst chainC) <| chainPre ++
            #[mkConst (rel P Ws[i - 1]!), mkList listNatE ((Ws.extract i Ws.size).map
              fun w => mkConst (rel P w)), xs[i - 1]!, xs[i]!, v, mkConst (stepN i), pf]
        return pf
      let mut vv := a[j]!
      for M in Bm do
        vv := (CFSG.KC.BM.Twin.mulStrips n #[vv] M)[0]!
      let vN := J ++ `v
      addNat vN vv
      let v := mkConst vN
      let pl ← side "l" (strip A j) a[j]! Bs Bm v
      let pr ← side "r" (strip C j) c[j]! Ds Dm v
      addThm J (trueEq (mkApp2 (mkConst ``Nat.beq) (mkApp (word Bs) (strip A j))
          (mkApp (word Ds) (strip C j))))
        (mkAppN (mkConst ``CFSG.KC.BM.LoadChain.beq_join)
          #[mkApp (word Bs) (strip A j), mkApp (word Ds) (strip C j), v, pl, pr])
    let t2 ← IO.monoNanosNow
    let ms (a b : Nat) : Float := (b - a).toFloat / 1e6
    logInfo m!"BMTIME {T} read {ms t0 t1} checks {ms t1 t2} ms"

end CFSG.KC.BM.LoadChain

open CFSG.KC.BM.LoadChain

elab "#bm_mul4c " pre:ident tag:ident a:ident "[" bs:ident* "]" c:ident "[" ds:ident* "]" :
    command =>
  mul4Chain pre.getId tag.getId a.getId (bs.map (·.getId)) c.getId (ds.map (·.getId))

elab "#bm_mulnc " pre:ident n:num tag:ident a:ident "[" bs:ident* "]" c:ident "[" ds:ident* "]" :
    command =>
  mulnChain false pre.getId n.getNat tag.getId a.getId (bs.map (·.getId)) c.getId (ds.map (·.getId))

elab "#bm_mulc " pre:ident tag:ident a:ident "[" bs:ident* "]" c:ident "[" ds:ident* "]" :
    command =>
  mulnChain true pre.getId 4370 tag.getId a.getId (bs.map (·.getId)) c.getId (ds.map (·.getId))
