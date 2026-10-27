module

public import CFSG.Fischer.F4

public section

namespace CFSG.LargeExtraspecial.AS35QTS

open CFSG.Fischer

structure V3 where
  x0 : F4
  x1 : F4
  x2 : F4
deriving DecidableEq

structure M3 where
  r0 : V3
  r1 : V3
  r2 : V3
deriving DecidableEq

structure Cd where
  e : ZMod 2
  a : V3
  m : M3
deriving DecidableEq

@[expose] def fr (x : F4) : F4 := x * x

@[expose] def vadd (u v : V3) : V3 := ⟨u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2⟩

@[expose] def dot (u v : V3) : F4 := u.x0 * v.x0 + u.x1 * v.x1 + u.x2 * v.x2

@[expose] def hermC (u v : V3) : F4 := fr u.x0 * v.x0 + fr u.x1 * v.x1 + fr u.x2 * v.x2

@[expose] def col0 (A : M3) : V3 := ⟨A.r0.x0, A.r1.x0, A.r2.x0⟩

@[expose] def col1 (A : M3) : V3 := ⟨A.r0.x1, A.r1.x1, A.r2.x1⟩

@[expose] def col2 (A : M3) : V3 := ⟨A.r0.x2, A.r1.x2, A.r2.x2⟩

@[expose] def mv (A : M3) (v : V3) : V3 := ⟨dot A.r0 v, dot A.r1 v, dot A.r2 v⟩

@[expose] def rowMul (r : V3) (B : M3) : V3 := ⟨dot r (col0 B), dot r (col1 B), dot r (col2 B)⟩

@[expose] def mm (A B : M3) : M3 := ⟨rowMul A.r0 B, rowMul A.r1 B, rowMul A.r2 B⟩

@[expose] def tr2C (c : F4) : ZMod 2 := if c + fr c = 0 then 0 else 1

@[expose] def betaC (u v : V3) : ZMod 2 := tr2C (F4.ω * hermC u v)

@[expose] def mulC (x y : Cd) : Cd :=
  ⟨x.e + y.e + betaC x.a (mv x.m y.a), vadd x.a (mv x.m y.a), mm x.m y.m⟩

@[expose] def v0 : V3 := ⟨0, 0, 0⟩

@[expose] def I3 : M3 := ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩

@[expose] def unitB (A : M3) : Bool :=
  hermC (col0 A) (col0 A) == 1 && hermC (col0 A) (col1 A) == 0 &&
    hermC (col0 A) (col2 A) == 0 && hermC (col1 A) (col0 A) == 0 &&
    hermC (col1 A) (col1 A) == 1 && hermC (col1 A) (col2 A) == 0 &&
    hermC (col2 A) (col0 A) == 0 && hermC (col2 A) (col1 A) == 0 &&
    hermC (col2 A) (col2 A) == 1

@[expose] def f4s : List F4 := [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]

@[expose] def v3s : List V3 :=
  f4s.flatMap fun a => f4s.flatMap fun b => f4s.map fun c => ⟨a, b, c⟩

@[expose] def gu3s : List M3 :=
  (v3s.flatMap fun r0 => v3s.flatMap fun r1 => v3s.map fun r2 => ⟨r0, r1, r2⟩).filter unitB

@[expose] def codes : List Cd :=
  [(0 : ZMod 2), 1].flatMap fun e => v3s.flatMap fun a => gu3s.map fun m => ⟨e, a, m⟩

@[expose] def e0 : Cd := ⟨0, v0, I3⟩

@[expose] def tau0 : Cd := ⟨1, v0, I3⟩

@[expose] def powC (c : Cd) : ℕ → Cd
  | 0 => e0
  | k + 1 => mulC (powC c k) c

@[expose] def zpowL (c : Cd) : List Cd := List.iterate (fun x => mulC x c) e0 72

@[expose] def pow72 (c : Cd) : Cd :=
  let c2 := mulC c c
  let c4 := mulC c2 c2
  let c8 := mulC c4 c4
  let c16 := mulC c8 c8
  let c32 := mulC c16 c16
  let c64 := mulC c32 c32
  mulC c64 c8

@[expose] def commB (x y : Cd) : Bool := mulC x y == mulC y x

@[expose] def isInv (c : Cd) : Bool := mulC c c == e0 && c != e0

@[expose] def cgens : List Cd :=
  [⟨0, ⟨1, 0, 0⟩, I3⟩, ⟨0, ⟨0, 1, 0⟩, I3⟩, ⟨0, ⟨0, 0, 1⟩, I3⟩, ⟨0, ⟨⟨2⟩, 0, 0⟩, I3⟩,
    ⟨0, v0, ⟨⟨0, 0, 1⟩, ⟨1, 0, 0⟩, ⟨0, 1, 0⟩⟩⟩, ⟨0, v0, ⟨⟨⟨2⟩, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩⟩]

@[expose] def il : List Cd := codes.filter isInv

@[expose] def sq : List Cd := codes.map fun s => mulC s s

@[expose] def sl : List Cd := il.filter fun c => c.m != I3 && sq.contains c

@[expose] def dl : List Cd := tau0 :: sl

@[expose] def wl : List Cd := il.filter fun c => !(dl.contains c)

@[expose] def t0c : Cd := sl.headD e0

@[expose] def lineIn (dl : List Cd) (t : Cd) : List Cd := dl.filter (commB t)

@[expose] def ckLists (sl : List Cd) : Bool :=
  gu3s.length == 648 && decide gu3s.Nodup && sl.length == 36 && decide sl.Nodup

@[expose] def ckRoot (cs il : List Cd) : Bool :=
  let qs := cs.filter fun c => c.m == I3
  (qs.all fun q => powC q 4 == e0) &&
    il.all fun c => c.m == I3 || qs.any fun q => mulC q q == tau0 && commB q c

@[expose] def ckInv (il sl dl : List Cd) : Bool :=
  let ps := (dl.flatMap fun a => dl.map fun b => (a, b)).filterMap fun p =>
    if p.1 != p.2 && commB p.1 p.2 then some (mulC p.1 p.2) else none
  il.all fun c => c == tau0 || sl.contains c || ps.contains c

@[expose] def ckClass (sl : List Cd) : Bool :=
  sl.all fun t => gu3s.any fun A => mm A (sl.headD e0).m == mm t.m A &&
    ([(0 : ZMod 2), 1].any fun e => v3s.any fun a =>
      mulC ⟨e, a, A⟩ (sl.headD e0) == mulC t ⟨e, a, A⟩)

@[expose] def ckOrd (dl : List Cd) : Bool :=
  dl.all fun a => dl.all fun b =>
    mulC (mulC a b) (mulC a b) == e0 || mulC (mulC (mulC a b) (mulC a b)) (mulC a b) == e0

@[expose] def ckLine (sl dl : List Cd) : Bool :=
  (sl.all fun t => (lineIn dl t).length == 5) &&
    (sl.all fun t => (lineIn dl t).all fun a => (lineIn dl t).all fun b => commB a b) &&
    (sl.all fun t => sl.all fun t' => !(commB t t') || sl.all fun s => commB t s == commB t' s) &&
    (sl.all fun t => (lineIn dl t).all fun a => (lineIn dl t).all fun b =>
      (lineIn dl t).all fun a' => (lineIn dl t).all fun b' => a == b || a' == b' ||
        mulC a b != mulC a' b' || (a == a' && b == b') || (a == b' && b == a')) &&
    sl.all fun t => !(dl.contains (mulC tau0 t))

@[expose] def ckNZ (dl wl : List Cd) : Bool :=
  (dl.all fun x => wl.all fun v => pow72 (mulC x v) == e0) &&
    ((dl.toFinset ×ˢ wl.toFinset).filter fun p => tau0 ∈ zpowL (mulC p.1 p.2)).card == 1188

@[expose] def ckNW (sl dl wl : List Cd) : Bool :=
  let t := sl.headD e0
  (((lineIn dl t).toFinset ×ˢ (wl.filter (commB t)).toFinset).filter fun p =>
    mulC tau0 t ∈ zpowL (mulC p.1 p.2)).card == 3

@[expose] def ckSwap (il sl : List Cd) : Bool :=
  sl.all fun p => sl.all fun p' => p == p' || !(commB p p') ||
    ((il.toFinset.filter fun v => mulC v p == mulC p' v).card == 16 &&
      sl.all fun q => q == p || q == p' || !(commB p q) ||
        il.all fun v => !(mulC v p == mulC p' v && commB v q))

@[expose] def ckCent (cs sl : List Cd) : Bool :=
  (cs.filter (commB (sl.headD e0))).toFinset.card == 2304

@[expose] def ckCenter (cs : List Cd) : Bool :=
  cs.all fun c => !(cgens.all (commB c)) || c == e0 || c == tau0

@[expose] def ckSmall : Bool :=
  unitB I3 && mulC e0 e0 == e0 && cgens.all fun g => unitB g.m

@[expose] def qtsCheck (cs il sl dl wl : List Cd) : Bool :=
  ckSmall && ckLists sl && ckRoot cs il && ckInv il sl dl && ckClass sl && ckOrd dl &&
    ckLine sl dl && ckNZ dl wl && ckNW sl dl wl && ckSwap il sl && ckCent cs sl && ckCenter cs

@[expose] def qtsOK : Bool :=
  let cs := codes
  let il := cs.filter isInv
  let sq := cs.map fun s => mulC s s
  let sl := il.filter fun c => c.m != I3 && sq.contains c
  let dl := tau0 :: sl
  let wl := il.filter fun c => !(dl.contains c)
  qtsCheck cs il sl dl wl

theorem qtsOK_eq : qtsOK = qtsCheck codes il sl dl wl := rfl

end CFSG.LargeExtraspecial.AS35QTS
