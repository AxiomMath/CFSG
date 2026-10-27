module

public import CFSG.LargeExtraspecial.SMod20BasicCheck
public import Certificates.Data.SMod20UaStab
public import Std.Data.HashMap.Basic

public section

namespace CFSG.SmithE

open CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def frobC (c : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => acc + f4mul (coord c i) (coord c i) * 4 ^ i) 0

@[expose] def dltC (c : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => acc + (if i < 2 then f4mul 2 (coord c i) else coord c i) *
    4 ^ i) 0

@[expose] def ptMapT (f : Nat → Nat) : Array Nat :=
  Array.ofFn (n := 693) fun p => uPos[normC (f uPts[p.val]!)]!

@[expose] def compTab (s t : Array Nat) : Array Nat := Array.ofFn (n := 693) fun x => s[t[x.val]!]!

@[expose] def invTab (s : Array Nat) : Array Nat :=
  (List.range 693).foldl (fun r x => r.set! s[x]! x) (Array.replicate 693 0)

@[expose] def idTab : Array Nat := Array.ofFn (n := 693) fun x => x.val

@[expose] def stabTab (T : Array Table) (g : Nat) : Array Nat :=
  Array.ofFn (n := 693) fun x => stabAp T stabWords[g]! x.val

@[expose] def liftTab (T : Array Table) : Nat → Array Nat
  | 0 => idTab
  | 1 => stabTab T 0
  | 2 => ptMapT frobC
  | 3 => compTab (compTab (ptMapT dltC) (ptMapT frobC)) (invTab (ptMapT dltC))
  | _ => compTab (compTab (compTab (ptMapT dltC) (ptMapT dltC)) (ptMapT frobC))
      (invTab (compTab (ptMapT dltC) (ptMapT dltC)))

@[expose] def invPairOK (t r : Array Nat) : Bool :=
  allIn 0 693 fun x => decide (t[x]! < 693) && decide (r[x]! < 693) && r[t[x]!]! == x &&
    t[r[x]!]! == x

@[expose] def normOK (T : Array Table) (s : Array Nat) : Bool :=
  allIn 0 693 fun p => allIn 0 693 fun x => s[ap T[p]! x]! == ap T[s[p]!]! s[x]!

@[expose] def sArrT (W0 s : Array Nat) : Array Nat :=
  Array.ofFn (n := 21) fun k => uaPos W0 s[W0[k.val]!]!

@[expose] def key21 (s : Array Nat) : Nat := s.foldl (fun acc x => acc * 32 + x) 0

@[expose] def chkOrbitOK (T : Array Table) (P : Array (Array Nat)) (I : Array (Array Nat)) :
    Bool :=
  let W0 := P[0]!
  let F := uaFlags P
  let gen := stabWords.map (stabSig T W0)
  let genR := stabWords.map fun w => stabSig T W0 (w.2, w.1)
  let roots := (List.range 4).map fun j => sArrT W0 (liftTab T (j + 1))
  let H : Std.HashMap Nat Nat :=
    (List.range I.size).foldl (fun m k => m.insert (key21 I[k]!) k) {}
  let f := fun g u => H.getD (key21 (collComp (collComp gen[g]! I[u]!) genR[g]!)) I.size
  I.size == 675 &&
    allIn 0 675 (fun v => I[v]!.size == 21 && allIn 0 21 fun k => decide (I[v]![k]! < 21)) &&
    allIn 0 5 (fun j => let s := liftTab T j
      invPairOK s (invTab s) && normOK T s && allIn 0 21 fun k => F[0]![s[W0[k]!]!]!) &&
    uaTreeOK 675 stabWords.size (fun v => roots.any fun r => r == I[v]!)
      (fun g u v => collComp (collComp gen[g]! I[u]!) genR[g]! == I[v]!)
      (uaBFS 675 (Array.range stabWords.size) f
        ((List.range 4).map fun j => H.getD (key21 (sArrT W0 (liftTab T (j + 1)))) I.size))

@[expose] def xorSel : List Nat → Nat → Nat
  | [], _ => 0
  | b :: bs, m => (if m % 2 = 1 then b else 0) ^^^ xorSel bs (m / 2)

@[expose] def indepOK (bs : List Nat) : Bool :=
  allIn 0 (2 ^ bs.length) fun m => allIn 0 (2 ^ bs.length) fun m' =>
    m == m' || xorSel bs m % 2 ^ 20 != xorSel bs m' % 2 ^ 20

@[expose] def echRed (E : List (Nat × Nat)) (v : Nat × Nat) : Nat × Nat :=
  E.foldl (fun w e => if w.1 ^^^ e.1 < w.1 then (w.1 ^^^ e.1, w.2 ^^^ e.2) else w) v

@[expose] def echIns (E : List (Nat × Nat)) (w : Nat × Nat) : List (Nat × Nat) :=
  (E.filter fun e => e.1 > w.1) ++ [w] ++ E.filter fun e => e.1 < w.1

@[expose] def echOf (vs : List Nat) : List (Nat × Nat) × List Nat :=
  (vs.zipIdx).foldl (fun st vj =>
    let w := echRed st.1 (vj.1, 2 ^ vj.2)
    if w.1 == 0 then (st.1, st.2 ++ [w.2]) else (echIns st.1 w, st.2)) ([], [])

@[expose] def maskOf (E : List (Nat × Nat)) (v : Nat) : Nat := (echRed E (v, 0)).2

@[expose] def pickIndep (vs : List Nat) (k : Nat) : List Nat :=
  (vs.foldl (fun st v =>
    if st.2.length ≥ k then st else
    let w := echRed st.1 (v, 0)
    if w.1 == 0 then st else (echIns st.1 w, st.2 ++ [v])) (([] : List (Nat × Nat)), [])).2

@[expose] def candT (T : Array Table) (W0 s : Array Nat) (a : Nat) : Array Nat :=
  Array.ofFn (n := 693) fun x => uaAp T W0 a 9 s[x.val]!

@[expose] def isInvoT (c : Array Nat) : Bool := allIn 0 693 fun x => c[c[x]!]! == x

@[expose] def isIdT (c : Array Nat) : Bool := allIn 0 693 fun x => c[x]! == x

@[expose] def sigT (F : Array (Array Bool)) (PP P : Array (Array Nat)) (c : Array Nat) :
    Array Nat :=
  Array.ofFn (n := 891) fun i => uaPlaneOf F PP fun m => c[P[i.val]![m]!]!

@[expose] def sigOK (F : Array (Array Bool)) (P : Array (Array Nat)) (c sg : Array Nat) : Bool :=
  allIn 0 891 fun i => decide (sg[i]! < 891) && allIn 0 21 fun k => F[sg[i]!]![c[P[i]![k]!]!]!

@[expose] def dVec (W sg : Array Nat) (i : Nat) : Nat := W[sg[i]!]! ^^^ W[i]!

@[expose] def fixL (c : Array Nat) : List Nat := (List.range 693).filter fun x => c[x]! == x

@[expose] def tvAp (q v : Nat) : Nat := applyCols tvArr[q]! v

@[expose] def profC (PT : Array (Array Bool)) (fx : List Nat) (y : Nat) : Nat :=
  fx.foldl (fun acc f => 2 * acc + if PT[y]![f]! then 1 else 0) 0

@[expose] def closOrd (PT : Array (Array Bool)) (c : Array Nat) (fx : List Nat) (b : Nat) :
    Array Nat × Array Nat := Id.run do
  let mut ord : Array Nat := (fx ++ [b]).toArray
  let mut placed : Array Bool := Array.ofFn (n := 693) fun x => (fx ++ [b]).contains x.val
  let mut wit : Array Nat := Array.replicate 693 693
  let mut changed := true
  let mut rounds := 0
  while changed && rounds < 700 do
    changed := false
    rounds := rounds + 1
    for d in [0:693] do
      if !placed[d]! then
        if placed[c[d]!]! then
          ord := ord.push d
          placed := placed.set! d true
          changed := true
        else
          match ord.find? fun e => PT[d]![e]! != PT[c[d]!]![e]! with
          | some e =>
            ord := ord.push d
            placed := placed.set! d true
            wit := wit.set! d e
            changed := true
          | none => pure ()
  return (ord, wit)

@[expose] def posOf (ord : Array Nat) : Array Nat :=
  (List.range ord.size).foldl (fun r k => r.set! ord[k]! k) (Array.replicate 693 693)

@[expose] def closOK (PT : Array (Array Bool)) (c : Array Nat) (b : Nat) (ord wit pos : Array Nat) :
    Bool :=
  ord.size == 693 &&
    allIn 0 693 (fun x => decide (pos[x]! < 693) && ord[pos[x]!]! == x) &&
    allIn 0 693 fun k => let d := ord[k]!
      decide (d < 693) && (c[d]! == d || d == b || decide (pos[c[d]!]! < k) ||
        (decide (wit[d]! < 693) && decide (pos[wit[d]!]! < k) &&
          PT[d]![wit[d]!]! != PT[c[d]!]![wit[d]!]!))

@[expose] def fpCheck (T : Array Table) (PT : Array (Array Bool)) (W c sg : Array Nat)
    (bs : List Nat) (YQ : Array (Nat × Nat)) (b : Nat) (ord wit : Array Nat) : Bool :=
  let fx := fixL c
  let ys := bs.length
  let colq := fun q => (List.range 20).map fun m => tvAp q (2 ^ m) ^^^ 2 ^ m
  let pr := Array.ofFn (n := 693) fun y => profC PT fx y.val
  indepOK bs && decide (ys ≤ 8) &&
    bs.all (fun v => anyIn 891 fun i => dVec W sg i == v) &&
    allIn 0 891 (fun i => xorSel bs (maskOf (echOf bs).1 (dVec W sg i)) == dVec W sg i) &&
    fx.length % 4 == 3 &&
    fx.all (fun q =>
      let y := YQ[q]!.1
      let w := YQ[q]!.2
      decide (0 < y) && decide (y < 2 ^ ys) && tvAp q w ^^^ w == xorSel bs y &&
      allIn 1 (2 ^ ys) fun m => m == y || (echOf (colq q)).2.any fun k =>
        tvAp q k == k && fB (xorSel bs m) k) &&
    fx.all (fun q => fx.all fun q' => q == q' || YQ[q]!.1 != YQ[q']!.1) &&
    allIn 1 (2 ^ ys) (fun m => fx.any fun q => YQ[q]!.1 == m) &&
    uaTreeOK 693 fx.length (fun v => v == fx.headD 0 || c[v]! != v)
      (fun g u v => ap T[fx[g]!]! u == v)
      (uaBFS 693 (Array.range fx.length) (fun g u => ap T[fx[g]!]! u) [fx.headD 0]) &&
    decide (b < 693) && c[b]! != b &&
    allIn 0 693 (fun y => allIn 0 693 fun y' => pr[y]! != pr[y']! || y' == y || y' == c[y]!) &&
    closOK PT c b ord wit (posOf ord)

@[expose] def fpOK (T : Array Table) (PT : Array (Array Bool)) (W c sg : Array Nat) : Bool :=
  let ds := (List.range 891).map (dVec W sg)
  let bs := pickIndep ds 8
  let fx := fixL c
  let colq := fun q => (List.range 20).map fun m => tvAp q (2 ^ m) ^^^ 2 ^ m
  let yq := fun q =>
    let Eq := (echOf (colq q)).1
    let y := ((List.range (2 ^ bs.length)).find? fun m => m != 0 &&
      (echRed Eq (xorSel bs m, 0)).1 == 0).getD 0
    (y, (echRed Eq (xorSel bs y, 0)).2)
  let YQ : Array (Nat × Nat) := Array.ofFn (n := 693) fun x => yq x.val
  let b := ((List.range 693).find? fun x => c[x]! != x).getD 0
  let ow := closOrd PT c fx b
  fpCheck T PT W c sg bs YQ b ow.1 ow.2

@[expose] def candInvCheck (T : Array Table) (F PT : Array (Array Bool)) (P : Array (Array Nat))
    (W c sg : Array Nat) (bs : List Nat) : Bool :=
  sigOK F P c sg && indepOK bs && bs.length == 5 &&
    bs.all (fun v => anyIn 891 fun i => dVec W sg i == v) &&
    (anyIn 891 (fun i => fB W[sg[i]!]! W[i]!) ||
      anyIn 891 (fun j => allIn 0 21 fun k => c[P[j]![k]!]! == P[j]![k]!) ||
      fpOK T PT W c sg)

@[expose] def candInvOK (T : Array Table) (F PT : Array (Array Bool)) (PP P : Array (Array Nat))
    (W c : Array Nat) : Bool :=
  let sg := sigT F PP P c
  candInvCheck T F PT P W c sg (pickIndep ((List.range 891).map (dVec W sg)) 5)

@[expose] def candOK (T : Array Table) (F PT : Array (Array Bool)) (PP P : Array (Array Nat))
    (W c : Array Nat) : Bool :=
  !isInvoT c || isIdT c || candInvOK T F PT PP P W c

@[expose] def chkCandOK (T : Array Table) (P : Array (Array Nat)) (W : Array Nat) (j : Nat) :
    Bool :=
  let F := uaFlags P
  let PP := uaPtPlanes P
  let s := liftTab T j
  let PT := perpTab ()
  allIn 0 512 fun a => candOK T F PT PP P W (candT T P[0]! s a)

@[expose] def chkOrbit (_ : Unit) : Bool :=
  chkOrbitOK tvTabs uaPts (collInvs collS2 (collMeet collS2))

@[expose] def chkCand (j : Nat) : Bool := chkCandOK tvTabs uaPts wtArr j

end CFSG.SmithE
