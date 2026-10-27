module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2BridgeData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bmulVec)
open CFSG.EvenSmallLie.OmegaEight.Stage2 (urRows)

@[expose] def deg : Eps → ℕ
  | .plus => 120
  | .minus => 136

@[expose] def nsA : Eps → Array ℕ
  | .plus => OmegaEight.nsArr
  | .minus => OmegaEightMinus.nsArr

@[expose] def nsI : Eps → Array ℕ
  | .plus => OmegaEight.nsIdx
  | .minus => OmegaEightMinus.nsIdx

@[expose] def eich : Eps → ℕ → ℕ → ℕ → ℕ
  | .plus => OmegaEight.eichNat
  | .minus => OmegaEightMinus.eichNat

@[expose] def bpos : Eps → ℕ → ℕ
  | .plus, 0 => 1
  | .plus, 1 => 2
  | .plus, 2 => 3
  | .plus, 3 => 7
  | .plus, 4 => 6
  | .plus, 5 => 5
  | .minus, 0 => 1
  | .minus, 1 => 2
  | .minus, 2 => 6
  | .minus, 3 => 7
  | .minus, 4 => 5
  | .minus, 5 => 4
  | _, _ => 0

@[expose] def fromW (ε : Eps) (y : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc j => if y.testBit j then acc ^^^ 2 ^ bpos ε j else acc) 0

@[expose] def toW (ε : Eps) (x : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc j => if x.testBit (bpos ε j) then acc ^^^ 2 ^ j else acc) 0

@[expose] def leviMap (ε : Eps) (A : Array ℕ) (x : ℕ) : ℕ :=
  x ^^^ fromW ε (toW ε x) ^^^ fromW ε (bmulVec 6 6 A (toW ε x))

@[expose] def permArr (ε : Eps) (f : ℕ → ℕ) : Array ℕ :=
  Array.ofFn (n := deg ε) fun i => (nsI ε)[f (nsA ε)[i.val]!]!

@[expose] def psiArr (ε : Eps) (y : ℕ) : Array ℕ := permArr ε (eich ε 1 (fromW ε y))

@[expose] def pArr (ε : Eps) (i : ℕ) : Array ℕ := permArr ε (leviMap ε (genRows ε i))

@[expose] def uArr (ε : Eps) (k : ℕ) : Array ℕ := permArr ε (leviMap ε (urRows ε k))

@[expose] def conjA (n : ℕ) (g x : Array ℕ) : Array ℕ := compA n (compA n g x) (invCand n g)

@[expose] def isInvol (n : ℕ) (x : Array ℕ) : Bool :=
  !eqA n x (idA n) && eqA n (compA n x x) (idA n)

@[expose] def lS : Eps → Array (Array ℕ)
  | .plus => OmegaEight.omega1S
  | .minus => OmegaEightMinus.omegaS

@[expose] def lK : Eps → ℕ
  | .plus => 8
  | .minus => 10

@[expose] def lBase : (ε : Eps) → List (Fin (deg ε))
  | .plus => OmegaEight.omega1Base
  | .minus => OmegaEightMinus.omegaBase

@[expose] def lW : Eps → Array (List ℤ)
  | .plus => OmegaEight.wordsOf 8 OmegaEight.omegaWords
  | .minus => OmegaEight.wordsOf 10 OmegaEightMinus.omegaWords

@[expose] def lBaseA (ε : Eps) : Array ℕ := ((lBase ε).map Fin.val).toArray

@[expose] def lLevelsPlus : Array Level := rawLevels 120 OmegaEight.omega1S (lBaseA .plus)

@[expose] def lLevelsMinus : Array Level := rawLevels 136 OmegaEightMinus.omegaS (lBaseA .minus)

@[expose] def lLevels : Eps → Array Level
  | .plus => lLevelsPlus
  | .minus => lLevelsMinus

@[expose] def memL (ε : Eps) (g : Array ℕ) : Bool := siftA (deg ε) (lLevels ε) (lBaseA ε) 0 g

@[expose] def lWord (ε : Eps) (w : List ℤ) : Array ℕ :=
  wordA (deg ε) (lS ε) (rawInvs (deg ε) (lS ε)) w


@[expose] def pOrig (ε : Eps) : Array (Array ℕ) :=
  (Array.ofFn (n := 6) fun j => psiArr ε (2 ^ j.val)) ++ Array.ofFn (n := 6) fun i => pArr ε i.val

@[expose] def uOrig (ε : Eps) : Array (Array ℕ) :=
  (Array.ofFn (n := 6) fun j => psiArr ε (2 ^ j.val)) ++ Array.ofFn (n := 6) fun k => uArr ε k.val

@[expose] def pWords : Eps → List (List ℤ)
  | .plus => [[-7, 11], [-7, 12], [13, -14, 13], [-7, -8], [-7, -9],
      [-16, -13, -14, -17, -16, -7, -10], [-16, 18, 16], [-19, -15, -13, -7, -17, 11, 8, 18, 7]]
  | .minus => [[-7, 8], [-7, 9], [-13, 14, 13], [-7, 10], [15, 16, 15], [-7, 11]]

@[expose] def pSPlus : Array (Array ℕ) := OmegaEight.pushWords 120 (pOrig .plus) (pWords .plus)

@[expose] def pSMinus : Array (Array ℕ) := OmegaEight.pushWords 136 (pOrig .minus) (pWords .minus)

@[expose] def pS : Eps → Array (Array ℕ)
  | .plus => pSPlus
  | .minus => pSMinus

@[expose] def pBase : (ε : Eps) → List (Fin (deg ε))
  | .plus => ([0, 2, 1, 4, 32, 16] : List (Fin 120))
  | .minus => ([0, 8, 1, 16, 36, 2] : List (Fin 136))

@[expose] def pBaseA (ε : Eps) : Array ℕ := ((pBase ε).map Fin.val).toArray

@[expose] def pSizes : Eps → List ℕ
  | .plus => [64, 35, 18, 4, 4, 2]
  | .minus => [64, 27, 16, 5, 6, 2]

@[expose] def pLevelsPlus : Array Level := rawLevels 120 pSPlus (pBaseA .plus)

@[expose] def pLevelsMinus : Array Level := rawLevels 136 pSMinus (pBaseA .minus)

@[expose] def pLevels : Eps → Array Level
  | .plus => pLevelsPlus
  | .minus => pLevelsMinus

@[expose] def memP (ε : Eps) (g : Array ℕ) : Bool := siftA (deg ε) (pLevels ε) (pBaseA ε) 0 g

@[expose] def uSPlus : Array (Array ℕ) := uOrig .plus

@[expose] def uSMinus : Array (Array ℕ) := uOrig .minus

@[expose] def uS : Eps → Array (Array ℕ)
  | .plus => uSPlus
  | .minus => uSMinus

@[expose] def uBase : (ε : Eps) → List (Fin (deg ε))
  | .plus => ([0, 2, 4, 16, 32] : List (Fin 120))
  | .minus => ([0, 8, 16] : List (Fin 136))

@[expose] def uBaseA (ε : Eps) : Array ℕ := ((uBase ε).map Fin.val).toArray

@[expose] def uSizes : Eps → List ℕ
  | .plus => [64, 2, 4, 4, 2]
  | .minus => [64, 16, 4]

@[expose] def uLevelsPlus : Array Level := rawLevels 120 uSPlus (uBaseA .plus)

@[expose] def uLevelsMinus : Array Level := rawLevels 136 uSMinus (uBaseA .minus)

@[expose] def uLevels : Eps → Array Level
  | .plus => uLevelsPlus
  | .minus => uLevelsMinus

@[expose] def memU (ε : Eps) (g : Array ℕ) : Bool := siftA (deg ε) (uLevels ε) (uBaseA ε) 0 g

@[expose] def chainCheck (ε : Eps) : Bool :=
  rawChainOK (deg ε) ((pS ε).extract 0 12) (pS ε) (pBaseA ε) (OmegaEight.wordsOf 12 (pWords ε)) 4 &&
    rawOrbitSizes (deg ε) (pS ε) (pBaseA ε) == pSizes ε &&
    rawChainOK (deg ε) ((uS ε).extract 0 12) (uS ε) (uBaseA ε) (OmegaEight.wordsOf 12 []) 4 &&
    rawOrbitSizes (deg ε) (uS ε) (uBaseA ε) == uSizes ε

@[expose] def psiTabPlus : Array (Array ℕ) := Array.ofFn (n := 64) fun y => psiArr .plus y.val

@[expose] def psiTabMinus : Array (Array ℕ) := Array.ofFn (n := 64) fun y => psiArr .minus y.val

@[expose] def psiTab : Eps → Array (Array ℕ)
  | .plus => psiTabPlus
  | .minus => psiTabMinus

@[expose] def psiT (ε : Eps) (y : ℕ) : Array ℕ := (psiTab ε).getD y #[]

@[expose] def basicCheck (ε : Eps) : Bool :=
  let n := deg ε
  allLt 64 (fun y => isInvA n (psiT ε y) (invCand n (psiT ε y)) && memL ε (psiT ε y) &&
    memP ε (psiT ε y) && memU ε (psiT ε y)) &&
  allLt 64 (fun y => allLt 64 fun y' =>
    eqA n (psiT ε (y ^^^ y')) (compA n (psiT ε y) (psiT ε y')) &&
      (y == y' || !eqA n (psiT ε y) (psiT ε y'))) &&
  allLt 6 (fun i => isInvA n (pArr ε i) (invCand n (pArr ε i)) && memL ε (pArr ε i) &&
    allLt 64 fun y => eqA n (conjA n (pArr ε i) (psiT ε y))
      (psiT ε (bmulVec 6 6 (genRows ε i) y))) &&
  allLt 6 (fun k => isInvA n (uArr ε k) (invCand n (uArr ε k)) && memL ε (uArr ε k) &&
    allLt 64 fun y => eqA n (conjA n (uArr ε k) (psiT ε y))
      (psiT ε (bmulVec 6 6 (urRows ε k) y))) &&
  allLt 64 (fun y => !(allLt 6 fun k => bmulVec 6 6 (urRows ε k) y == y) || y == 0 || y == 1)

@[expose] def inO (ε : Eps) (z : ℕ) : Bool := allLt 63 fun y => (psiT ε (y + 1))[z]! != z

@[expose] def oMaskPlus : Array Bool := Array.ofFn (n := 120) fun z => inO .plus z.val

@[expose] def oMaskMinus : Array Bool := Array.ofFn (n := 136) fun z => inO .minus z.val

@[expose] def oMask : Eps → Array Bool
  | .plus => oMaskPlus
  | .minus => oMaskMinus

@[expose] def inOT (ε : Eps) (z : ℕ) : Bool := (oMask ε).getD z false

@[expose] def maskOf (ε : Eps) (g : Array ℕ) : Array Bool :=
  Array.ofFn (n := deg ε) fun z => inOT ε (invCand (deg ε) g)[z.val]!

@[expose] def oOrbitOf (ε : Eps) : Array (Array ℕ) := Id.run do
  let n := deg ε
  let gens := (lS ε).extract 0 (lK ε)
  let mut elts : Array (Array ℕ) := #[idA n]
  let mut masks : Array (Array Bool) := #[maskOf ε (idA n)]
  let mut h := 0
  for _ in [0:200] do
    if h < elts.size then
      let g := elts[h]!
      for s in gens do
        let g' := compA n s g
        let m := maskOf ε g'
        if !(masks.contains m) then
          elts := elts.push g'
          masks := masks.push m
      h := h + 1
  return elts

@[expose] def oOrbitPlus : Array (Array ℕ) := oOrbitOf .plus

@[expose] def oOrbitMinus : Array (Array ℕ) := oOrbitOf .minus

@[expose] def oOrbit : Eps → Array (Array ℕ)
  | .plus => oOrbitPlus
  | .minus => oOrbitMinus

@[expose] def nOrb : Eps → ℕ
  | .plus => 135
  | .minus => 119

@[expose] def oSetCheck (ε : Eps) : Bool :=
  let n := deg ε
  let T := oOrbit ε
  let M := T.map (maskOf ε)
  allLt n (fun z => inOT ε z == inO ε z) &&
    (pBaseA ε).all (inOT ε) &&
    allLt n (fun z => !(inOT ε z) || (List.range 64).any fun y => (psiT ε y)[0]! == z) &&
    T.size == nOrb ε &&
    allLt T.size (fun i => isInvA n T[i]! (invCand n T[i]!) && memL ε T[i]!) &&
    allLt T.size (fun i => allLt i fun j => (List.range n).any fun z => (M[i]!)[z]! != (M[j]!)[z]!)

@[expose] def uElem (ε : Eps) (i : ℕ) : Array ℕ := Id.run do
  let L := uLevels ε
  let n := deg ε
  let m := L.size
  let mut digs : Array ℕ := Array.replicate m 0
  let mut r := i
  for k in [0:m] do
    let lev := m - 1 - k
    let s := (L.getD lev default).pts.size
    digs := digs.set! lev (r % s)
    r := r / s
  let mut g := idA n
  for k in [0:m] do
    g := compA n g ((L.getD k default).tr.getD (digs.getD k 0) (idA n))
  return g

@[expose] def uListPlus : Array (Array ℕ) := Array.ofFn (n := 4096) fun i => uElem .plus i.val

@[expose] def uListMinus : Array (Array ℕ) := Array.ofFn (n := 4096) fun i => uElem .minus i.val

@[expose] def uList : Eps → Array (Array ℕ)
  | .plus => uListPlus
  | .minus => uListMinus

@[expose] def uIdx (ε : Eps) (y : Array ℕ) : ℕ := Id.run do
  let L := uLevels ε
  let n := deg ε
  let base := uBaseA ε
  let mut g := y
  let mut i := 0
  for k in [0:L.size] do
    let lev := L.getD k default
    let a := lev.pos.getD (g.getD (base.getD k 0) 0) n
    if a < lev.pts.size then
      i := i * lev.pts.size + a
      g := compA n (lev.trInv.getD a (idA n)) g
    else
      return 4096
  return i

@[expose] def uClassesOf (ε : Eps) : Array (Option (ℕ × ℕ)) × Array ℕ := Id.run do
  let n := deg ε
  let S := uList ε
  let gens := uOrig ε
  let mut cls : Array (Option (ℕ × ℕ)) := Array.replicate 4096 none
  let mut reps : Array ℕ := #[]
  for i in [0:4096] do
    if (cls.getD i (some (0, 0))).isNone && isInvol n (S.getD i #[]) then
      let c := reps.size
      reps := reps.push i
      cls := cls.set! i (some (c, 0))
      let mut queue : Array ℕ := #[i]
      let mut h := 0
      for _ in [0:4096] do
        if h < queue.size then
          let x := queue.getD h 0
          let cx := ((cls.getD x none).getD (0, 0)).2
          for g in gens do
            let y := uIdx ε (conjA n g (S.getD x #[]))
            if (cls.getD y (some (0, 0))).isNone then
              cls := cls.set! y (some (c, uIdx ε (compA n g (S.getD cx #[]))))
              queue := queue.push y
          h := h + 1
  return (cls, reps)

@[expose] def uClassesPlus : Array (Option (ℕ × ℕ)) × Array ℕ := uClassesOf .plus

@[expose] def uClassesMinus : Array (Option (ℕ × ℕ)) × Array ℕ := uClassesOf .minus

@[expose] def uClasses : Eps → Array (Option (ℕ × ℕ)) × Array ℕ
  | .plus => uClassesPlus
  | .minus => uClassesMinus

@[expose] def clsOf (ε : Eps) (i : ℕ) : Option (ℕ × ℕ) := (uClasses ε).1.getD i none

@[expose] def nCls (ε : Eps) : ℕ := (uClasses ε).2.size

@[expose] def repOf (ε : Eps) (c : ℕ) : ℕ := (uClasses ε).2.getD c 0

@[expose] def selB (d : Array Bool) : Option (ℕ × ℕ) → Bool
  | some (c, _) => d.getD c false
  | none => false

@[expose] def membersOf (ε : Eps) (c : ℕ) : List ℕ :=
  (List.range 4096).filter fun i => ((clsOf ε i).map Prod.fst) == some c

@[expose] def membersTab (ε : Eps) : Array (List ℕ) :=
  Array.ofFn (n := nCls ε) fun c => membersOf ε c.val

@[expose] def adjB (ε : Eps) (T : Array (List ℕ)) (c c' : ℕ) : Bool :=
  let n := deg ε
  let S := uList ε
  (T.getD c []).all fun i => (T.getD c' []).all fun i' =>
    eqA n (compA n (S.getD i #[]) (S.getD i' #[])) (compA n (S.getD i' #[]) (S.getD i #[]))

@[expose] def adjTabOf (ε : Eps) : Array (Array Bool) :=
  let T := membersTab ε
  Array.ofFn (n := nCls ε) fun c => Array.ofFn (n := nCls ε) fun c' => adjB ε T c c'

@[expose] def adjTabPlus : Array (Array Bool) := adjTabOf .plus

@[expose] def adjTabMinus : Array (Array Bool) := adjTabOf .minus

@[expose] def adjTab : Eps → Array (Array Bool)
  | .plus => adjTabPlus
  | .minus => adjTabMinus

@[expose] def adjT (ε : Eps) (c c' : ℕ) : Bool := ((adjTab ε).getD c #[]).getD c' false

@[expose] def okPre (ε : Eps) (d : List Bool) : Bool :=
  let da := d.toArray
  match d.getLast? with
  | some true => adjT ε (d.length - 1) (d.length - 1) &&
      allLt (d.length - 1) fun c' => !(da.getD c' false) || adjT ε c' (d.length - 1)
  | _ => true

@[expose] def enumAux (ok : List Bool → Bool) : ℕ → List Bool → List (List Bool)
  | 0, pre => [pre]
  | k + 1, pre =>
    (if ok (pre ++ [false]) then enumAux ok k (pre ++ [false]) else []) ++
      (if ok (pre ++ [true]) then enumAux ok k (pre ++ [true]) else [])

@[expose] def sumSel (ε : Eps) (d : List Bool) : ℕ :=
  let da := d.toArray
  ((List.range 4096).filter fun i => selB da (clsOf ε i)).length

@[expose] def finalOK (ε : Eps) (w : List ℤ) (d : List Bool) : Bool :=
  let n := deg ε
  let S := uList ε
  let da := d.toArray
  let l := lWord ε w
  let a := psiT ε 1
  memL ε l && isInvA n l (invCand n l) && !eqA n (conjA n l a) a &&
    allLt 4096 fun i => !(selB da (clsOf ε i)) ||
      (let y := conjA n l (S.getD i #[])
       let k := uIdx ε y
       decide (k < 4096) && eqA n y (S.getD k #[]) && selB da (clsOf ε k))

@[expose] def cands : Eps → List (List ℤ)
  | .plus => [[8, 4, 1, -8, -7, 3, -8, -3, -7, 8], [3, 2, 2, -4, 3, 4, 6],
      [-5, -6, -5, 1, 8, 4, 6, -5, 4, 4, 4, 1, -1, 8, 1, 3, 1, 6, 5, 7, 5, -5, -7, -5, 3, -7, 4,
        1, -3, 6, -1, -8, 1, 7, -5, 4, 5, -5],
      [-2, -7, 5, 5, 5, 3, -8, -5, 5, 8, 5, 3, 7, 5, 7, -2, -3, 2, 7, 4],
      [-5, 5, 6, -4, 1, 3, -6, 5, -2, 1, 7, -5, -1, -2, -7, 4, -5, 1, 8, 6, 4, 3, -3, -4, 3, 3, 5,
        -6, 3, 2, -7, -5, 7],
      [-7, -7, -8, -8, 4, -1, -3, -4, 7, -1]]
  | .minus => [[10, -2, 10, 5, -5, 8, -2, 5, 10, 2, -2, 4, 10, -3, 8, 4, 2, -7, -9, -8, -2, 6, 1,
        5, -8, -6],
      [-3, -1, 5, 8, 8, -1, -6, 10, -7, -7, -10, -4, -7, -2], [-2, 1, 2, 3, -1, 7, -5, -4, 7],
      [-3, 3, 5, -6, 2, 3, 6, 3, -4, -6]]

@[expose] def s5Check (ε : Eps) : Bool :=
  let n := deg ε
  let S := uList ε
  S.size == 4096 &&
    allLt 4096 (fun i => isInvA n (S.getD i #[]) (invCand n (S.getD i #[])) &&
      (S.getD i #[]).size == n && memU ε (S.getD i #[]) && uIdx ε (S.getD i #[]) == i) &&
    allLt 4096 (fun i => match clsOf ε i with
      | none => !(isInvol n (S.getD i #[]))
      | some (c, j) => decide (c < nCls ε) && decide (j < 4096) && isInvol n (S.getD i #[]) &&
          eqA n (S.getD i #[]) (conjA n (S.getD j #[]) (S.getD (repOf ε c) #[]))) &&
    allLt (nCls ε) (fun c => decide (repOf ε c < 4096)) &&
    (enumAux (okPre ε) (nCls ε) []).all fun d =>
      sumSel ε d != 63 || (cands ε).any fun w => finalOK ε w d

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
