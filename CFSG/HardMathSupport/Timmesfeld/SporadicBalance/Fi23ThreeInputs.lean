module

public import Certificates.Data.CFSGNative.Fi23.Certificate
public import Certificates.Data.E27Table
public meta import Certificates.Data.CFSGNative.Fi23.Certificate
public meta import Certificates.Data.E27Table

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Foote.E27

set_option compiler.extract_closed false

@[expose] def qWords : Array (List Nat) :=
  #[[3, 12, 7, 2, 0, 19, 9, 5, 9, 15, 12, 8, 8, 8, 15, 18, 12, 12, 17, 22, 17, 17, 17, 18, 22],
    [2, 17, 19, 7, 0, 15, 10, 19, 4, 20, 12, 17, 9, 13, 17, 22, 13, 22, 16, 16, 19, 17, 22, 20],
    [10, 3, 16, 7, 0, 14, 4, 17, 4, 10, 9, 13, 11, 12, 12, 16, 12, 18, 17, 17, 19, 16, 22, 20]]

@[expose] def fixHint : Array Nat := #[
  49, 140, 49, 140, 558, 2675, 782, 102, 657, 558, 39, 3011, 732, 805, 43, 2161, 342, 805, 1206,
  825, 40, 9, 39, 60, 39, 1219, 2505, 53, 1126, 216, 3011, 216, 2320, 805, 145, 836, 39, 94, 1126,
  626, 805, 1219, 308, 310, 1052, 216, 928, 1520, 367, 164, 39, 367, 1054, 722, 1618, 2505, 353,
  22, 39, 147, 350, 2218, 367, 2502, 1052, 59, 12, 770, 197, 342, 805, 139, 2365, 585, 51, 127,
  43, 805, 1275, 367, 782, 139, 471, 30, 6, 836, 805, 531, 353, 140, 342, 216, 531, 1219, 770,
  1219, 75, 531, 46, 805, 626, 2196, 183, 547, 2351, 29, 775, 1843, 1052, 2196, 805, 1114, 1275,
  1030, 133, 626, 2505, 78, 1253, 1264, 353, 268, 2999, 48, 437, 805, 102, 1126, 66, 248, 531,
  183, 1253, 1843, 626, 1126, 1052, 201, 216, 66, 342, 216, 805, 805, 531, 342, 308, 531, 1052,
  420, 805, 805, 805, 40, 222, 1866, 216, 140, 9, 228, 45, 775, 169, 128, 342, 342, 2196, 342, 16,
  1336, 216, 3011, 1052, 2196, 805, 574, 1336, 770, 206, 29, 66, 805, 70, 465, 3441, 59, 39, 79,
  805, 105, 805, 928, 1336, 74, 626, 39, 139, 39]

@[expose] def qN : Nat := 1594323

@[expose] def qLettersT (letters : Array Table) (w : List Nat) : Table :=
  w.foldr (fun l T => compT 31671 letters[l]! T) (idT 31671)

@[expose] def qGens (letters : Array Table) : Array Table := qWords.map (qLettersT letters)

@[expose] def qKeyAt (img : Array Nat) (s : Nat) : UInt64 × UInt64 :=
  ((img[s]!).toUInt64 + ((img[s + 1]!).toUInt64 <<< 16) + ((img[s + 2]!).toUInt64 <<< 32) +
    ((img[s + 3]!).toUInt64 <<< 48), (img[s + 4]!).toUInt64 + ((img[s + 5]!).toUInt64 <<< 16))

structure QEnum where
  par : Array (Nat × Nat)
  img : Array Nat
  L : Array (Array Nat)
  H : Std.HashMap (UInt64 × UInt64) Nat

@[expose] def qStepImg (T : Table) (img : Array Nat) (s : Nat) : Array Nat :=
  #[ap T img[s]!, ap T img[s + 1]!, ap T img[s + 2]!, ap T img[s + 3]!, ap T img[s + 4]!,
    ap T img[s + 5]!]

@[expose] def qEnum (G : Array Table) : QEnum := Id.run do
  let m := G.size
  let mut par : Array (Nat × Nat) := #[(0, 0)]
  let mut img : Array Nat := #[0, 1, 2, 3, 4, 5]
  let mut L : Array (Array Nat) := Array.replicate m #[]
  let mut H : Std.HashMap (UInt64 × UInt64) Nat := Std.HashMap.emptyWithCapacity (2 * qN)
  H := H.insert (qKeyAt img 0) 0
  for i in [0:qN] do
    if i < par.size then
      for j in [0:m] do
        let nb := qStepImg G[j]! img (6 * i)
        let k := qKeyAt nb 0
        match H.get? k with
        | some idx => L := L.modify j (·.push idx)
        | none =>
          let idx := par.size
          H := H.insert k idx
          img := img ++ nb
          par := par.push (i, j)
          L := L.modify j (·.push idx)
  return { par, img, L, H }

@[expose] def qInvIdx (G : Array Table) (E : QEnum) : Array Nat :=
  G.map fun T => (E.H.get? (qKeyAt (qStepImg (invT 31671 T) #[0, 1, 2, 3, 4, 5] 0) 0)).getD 0

structure QLab where
  lab : Array Nat
  wit : Array Nat
  rep : Array Nat

@[expose] def qLabels (P : Array (Nat × Nat)) (L : Array (Array Nat)) (N : Nat)
    (inv : Array Nat) (m : Nat) : QLab := Id.run do
  let mut lab : Array Nat := Array.replicate N N
  let mut wit : Array Nat := Array.replicate N 0
  let mut rep : Array Nat := #[]
  for i in [0:N] do
    if i != 0 && tabMul P L i (tabMul P L i i) == 0 && lab[i]! == N then
      let l := rep.size
      rep := rep.push i
      lab := lab.set! i l
      wit := wit.set! i 0
      let mut q : Array Nat := #[i]
      let mut h := 0
      for _ in [0:N] do
        if h < q.size then
          let u := q[h]!
          for j in [0:m] do
            let v := (L[j]!)[tabMul P L u inv[j]!]!
            if lab[v]! == N then
              lab := lab.set! v l
              wit := wit.set! v (tabMul P L wit[u]! inv[j]!)
              q := q.push v
          h := h + 1
  return { lab, wit, rep }

@[expose] def qTreeOK (G : Array Table) (P : Array (Nat × Nat)) (img : Array Nat) (N : Nat) :
    Bool :=
  allIn 0 6 (fun t => img[t]! == t) &&
    allIn 1 N fun i => decide ((P[i]!).1 < i) && decide ((P[i]!).2 < G.size) &&
      allIn 0 6 fun t => img[6 * i + t]! == ap G[(P[i]!).2]! img[6 * (P[i]!).1 + t]!

@[expose] def qLeftOK (G : Array Table) (L : Array (Array Nat)) (img : Array Nat) (N : Nat) :
    Bool :=
  allIn 0 G.size fun j => allIn 0 N fun i => decide ((L[j]!)[i]! < N) &&
    allIn 0 6 fun t => img[6 * (L[j]!)[i]! + t]! == ap G[j]! img[6 * i + t]!

@[expose] def qInjOK (H : Std.HashMap (UInt64 × UInt64) Nat) (img : Array Nat) (N : Nat) : Bool :=
  allIn 0 N fun i => (H.get? (qKeyAt img (6 * i))).getD N == i

@[expose] def qClassOK (P : Array (Nat × Nat)) (L : Array (Array Nat)) (N : Nat)
    (lab wit rep : Array Nat) : Bool :=
  allIn 0 N fun i => i == 0 || tabMul P L i (tabMul P L i i) != 0 ||
    (decide (lab[i]! < rep.size) && decide (wit[i]! < N) && decide (rep[lab[i]!]! < N) &&
      tabMul P L wit[i]! i == tabMul P L rep[lab[i]!]! wit[i]!)

@[expose] def qActPt (P : Array (Nat × Nat)) (G : Array Table) (r x : Nat) : Nat :=
  if _h : (P[r]!).1 < r then ap G[(P[r]!).2]! (qActPt P G (P[r]!).1 x) else x
termination_by r
decreasing_by exact _h

@[expose] def qFixOK (P : Array (Nat × Nat)) (G : Array Table) (rep fix : Array Nat) : Bool :=
  allIn 0 rep.size fun l => decide (fix[l]! < 31671) && qActPt P G rep[l]! fix[l]! == fix[l]!

@[expose] def q23Core (letters G : Array Table) (E : QEnum) (lb : QLab) : Bool :=
  qWords.size == 3 && qWords.all (fun w => w.all fun z => decide (z < letters.size)) &&
    G.size == 3 && E.par.size == qN && qTreeOK G E.par E.img qN && qLeftOK G E.L E.img qN &&
    qInjOK E.H E.img qN && qClassOK E.par E.L qN lb.lab lb.wit lb.rep &&
    qFixOK E.par G lb.rep fixHint

@[expose] def q23Labels (letters G : Array Table) (E : QEnum) : Bool :=
  q23Core letters G E (qLabels E.par E.L qN (qInvIdx G E) G.size)

@[expose] def q23Enum (letters G : Array Table) : Bool := q23Labels letters G (qEnum G)

@[expose] def q23OK (O : WOrbit) : Bool :=
  let letters := chainLetters O
  q23Enum letters (qGens letters)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
