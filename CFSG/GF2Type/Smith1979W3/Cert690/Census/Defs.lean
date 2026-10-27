module

public import CFSG.GF2Type.Smith1979W3.Cert690.Check
public import CFSG.GF2Type.Smith1979W3.Cert690.Dict

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

@[expose] def oGensC (minus : Bool) : List ℕ :=
  (oWords minus).map wordC

@[expose] def omegaGensC (minus : Bool) : List ℕ :=
  (omegaWords minus).map wordC

@[expose] def enumDataFast (gens : List ℕ) (fuel : ℕ := 1 <<< 17) :
    Array ℕ × Array (ℕ × ℕ) :=
  let gs := gens.toArray
  let rec go (fuel : ℕ) (front back : List ℕ) (par : List (ℕ × ℕ))
      (seen : Std.HashSet ℕ) (i : ℕ) (out : List ℕ) : Array ℕ × Array (ℕ × ℕ) :=
    match fuel with
    | 0 => (out.reverse.toArray, par.reverse.toArray)
    | f + 1 =>
      match front with
      | [] =>
        match back with
        | [] => (out.reverse.toArray, par.reverse.toArray)
        | _ => go f back.reverse [] par seen i out
      | x :: rest =>
        let st := (List.range gs.size).foldl
          (fun (st : List ℕ × List (ℕ × ℕ) × Std.HashSet ℕ) q =>
            let y := Code.mul x gs[q]!
            if st.2.2.contains y then st
            else (y :: st.1, (i, q) :: st.2.1, st.2.2.insert y))
          (back, par, seen)
        go f rest st.1 st.2.1 st.2.2 (i + 1) (x :: out)
  go fuel [Code.one] [] [(0, 0)] ((∅ : Std.HashSet ℕ).insert Code.one) 0 []

structure GrpData where
  O : Array ℕ
  par : Array (ℕ × ℕ)
  invI : Array ℕ
  idx : Std.HashMap ℕ ℕ
  Om : Array ℕ
  OmPar : Array (ℕ × ℕ)

@[expose] def grpData (minus : Bool) (_ : Unit := ()) : GrpData :=
  let d := enumData (oGensC minus)
  let O := d.1
  let idx := idxMapOf O
  let invI := (invArr O).map fun c => idx.getD c O.size
  let e := enumData (omegaGensC minus)
  { O := O, par := d.2, invI := invI, idx := idx, Om := e.1, OmPar := e.2 }

@[expose] def idxOK (D : GrpData) : Bool :=
  (List.range D.O.size).all fun i => D.idx.getD D.O[i]! D.O.size == i

@[expose] def invArrOK (D : GrpData) : Bool :=
  D.invI.size == D.O.size &&
  D.invI.all (fun j => j < D.O.size) &&
  (List.range D.O.size).all fun i =>
    Code.mul D.O[i]! D.O[D.invI[i]!]! == Code.one

@[expose] def groupOK (minus : Bool) (D : GrpData) : Bool :=
  enumOK (oGensC minus) D.O D.par &&
  enumOK (omegaGensC minus) D.Om D.OmPar &&
  D.O.size == (if minus then 51840 else 40320) &&
  D.Om.size == (if minus then 25920 else 20160) &&
  idxOK D && invArrOK D

@[expose] def singOf (minus : Bool) : Array ℕ :=
  ((List.range 64).filter fun n => n != 0 && !(qB minus n)).toArray

@[expose] def b0Of (minus : Bool) : ℕ := (singOf minus)[0]!

@[expose] def transWitOf (D : GrpData) (s : Array ℕ) (b : ℕ) : Array ℕ :=
  s.map fun e => (List.range D.O.size).find? (fun i => Code.act D.O[i]! e == b) |>.getD 0

@[expose] def transOK (D : GrpData) (s : Array ℕ) (b : ℕ) (w : Array ℕ) : Bool :=
  s.size != 0 && w.size == s.size && s[0]! == b &&
  (List.range s.size).all fun k =>
    let i := w[k]!
    i < D.O.size && Code.act D.O[i]! s[k]! == b

@[expose] def isA2Of (D : GrpData) (minus : Bool) (i : ℕ) : Bool :=
  i < D.O.size &&
  let c := D.O[i]!
  c != Code.one && Code.mul c c == Code.one &&
  let I := ((List.range 64).map fun v => Code.act c v ^^^ v).toArray
  (hashSetOfArray I).size == 4 && I.all (fun x => !(qB minus x))

@[expose] def a2FixOf (D : GrpData) (minus : Bool) (b : ℕ) : Array ℕ :=
  ((List.range D.O.size).filter fun i =>
    Code.act D.O[i]! b == b && isA2Of D minus i).toArray

@[expose] def conjIdxOf (D : GrpData) (a x : ℕ) : ℕ :=
  D.idx.getD (Code.mul (Code.mul D.O[a]! D.O[x]!) D.O[D.invI[a]!]!) D.O.size

@[expose] def lOK (D : GrpData) (minus : Bool) (b : ℕ) (L : Array ℕ) : Bool :=
  L.size != 0 && L.contains 0 && (hashSetOfArray L).size == L.size &&
  L.all (fun i =>
    i < D.O.size && Code.act D.O[i]! b == b &&
      (i == 0 || Code.mul D.O[i]! D.O[i]! == Code.one)) &&
  L.all (fun i => L.all fun j =>
    let p := Code.mul D.O[i]! D.O[j]!
    let y := D.idx.getD p D.O.size
    y < D.O.size && D.O[y]! == p && L.contains y) &&
  L.any (isA2Of D minus)

@[expose] def l2OK (D : GrpData) (minus : Bool) (b : ℕ) (Llist : Array (Array ℕ))
    (a2 : Array ℕ) (wit : Array (ℕ × ℕ)) : Bool :=
  wit.size == a2.size &&
  (List.range a2.size).all fun k =>
    let t := a2[k]!
    let j := (wit[k]!).1
    let c := (wit[k]!).2
    j < Llist.size && c < D.O.size && Code.act D.O[c]! b == b &&
    let L := Llist[j]!
    L.size == 2 && L.contains 0 &&
    (let ci := D.O[D.invI[c]!]!
     let cj := fun x =>
       let p := Code.mul (Code.mul D.O[c]! D.O[x]!) ci
       let y := D.idx.getD p D.O.size
       (y < D.O.size && D.O[y]! == p, y)
     L.all (fun x => (cj x).1 && ((cj x).2 == 0 || (cj x).2 == t)) &&
     L.any (fun x => (cj x).1 && (cj x).2 == 0) &&
     L.any (fun x => (cj x).1 && (cj x).2 == t))

@[expose] def l3OK (D : GrpData) (b : ℕ) (Llist : Array (Array ℕ))
    (tasks : Array (ℕ × ℕ)) (wit : Array (ℕ × ℕ)) : Bool :=
  wit.size == tasks.size &&
  (List.range tasks.size).all fun k =>
    let j := (tasks[k]!).1
    let u := (tasks[k]!).2
    let kk := (wit[k]!).1
    let c := (wit[k]!).2
    j < Llist.size && u < D.O.size && kk < Llist.size && c < D.O.size &&
    let L := Llist[j]!
    Code.act D.O[u]! b == b && isInvCode D.O[u]! && !(L.contains u) &&
    L.all (fun x => Code.mul D.O[u]! D.O[x]! == Code.mul D.O[x]! D.O[u]!) &&
    Code.act D.O[c]! b == b &&
    (let U := L ++ L.map (fun x => D.idx.getD (Code.mul D.O[x]! D.O[u]!) D.O.size)
     U.size == 2 * L.size && U.all (fun x => x < D.O.size) &&
     (hashSetOfArray U).size == U.size &&
     (let V := U.map (fun x => conjIdxOf D c x)
      (hashSetOfArray V).size == (Llist[kk]!).size &&
      V.all (fun y => (Llist[kk]!).contains y) &&
      (Llist[kk]!).all (fun y => V.contains y)))

@[expose] def l3TaskValid (D : GrpData) (b : ℕ) (Llist : Array (Array ℕ))
    (j u : ℕ) : Bool :=
  j < Llist.size && u < D.O.size &&
  Code.act D.O[u]! b == b && isInvCode D.O[u]! && !((Llist[j]!).contains u) &&
  (Llist[j]!).all fun x =>
    Code.mul D.O[u]! D.O[x]! == Code.mul D.O[x]! D.O[u]!

@[expose] def l3Complete (D : GrpData) (b : ℕ) (Llist : Array (Array ℕ))
    (tasks : Array (ℕ × ℕ)) : Bool :=
  (List.range Llist.size).all fun j =>
    (List.range D.O.size).all fun u =>
      if l3TaskValid D b Llist j u then tasks.contains (j, u) else true

@[expose] def minCandSize (minus : Bool) : ℕ := if minus then 8 else 4

@[expose] def candidatesOf (minus : Bool) (Llist : Array (Array ℕ)) : Array ℕ :=
  ((List.range Llist.size).filter fun j => (Llist[j]!).size >= minCandSize minus).toArray

structure KSub where
  elems : Array ℕ
  gens : Array ℕ
  par : Array (ℕ × ℕ)
  deriving Inhabited

inductive KClass where
  | normal (N : Array ℕ)
  | reducible (v : ℕ)
  | omega
  | whole
  | pgl (g : ℕ)
  deriving Inhabited

structure CloseWit where
  rep : ℕ
  k : ℕ
  n : ℕ
  words : Array (Array ℕ)
  deriving Inhabited

structure LData where
  Llist : Array (Array ℕ)
  l2wit : Array (ℕ × ℕ)
  l3tasks : Array (ℕ × ℕ)
  l3wit : Array (ℕ × ℕ)
  deriving Inhabited

structure CandData where
  L : Array ℕ
  flist : Array KSub
  bits : Array String
  closes : Array (Array CloseWit)
  classif : Array KClass
  deriving Inhabited

@[expose] def catN (as : Array (Array ℕ)) : Array ℕ :=
  as.foldl (fun acc a => acc ++ a) #[]

@[expose] def catP (as : Array (Array (ℕ × ℕ))) : Array (ℕ × ℕ) :=
  as.foldl (fun acc a => acc ++ a) #[]

@[expose] def catW (as : Array (Array CloseWit)) : Array CloseWit :=
  as.foldl (fun acc a => acc ++ a) #[]

@[expose] def catT (as : Array (Array (ℕ × ℕ × ℕ))) : Array (ℕ × ℕ × ℕ) :=
  as.foldl (fun acc a => acc ++ a) #[]

@[expose] def catK (as : Array (Array KSub)) : Array KSub :=
  as.foldl (fun acc a => acc ++ a) #[]

@[expose] def catC (as : Array (Array KClass)) : Array KClass :=
  as.foldl (fun acc a => acc ++ a) #[]

@[expose] def censusBaseOf (minus : Bool) (D : GrpData) (Ld : LData) : Bool :=
  groupOK minus D &&
  (let s := singOf minus
   let b := b0Of minus
   let tw := transWitOf D s b
   transOK D s b tw &&
   (let a2 := a2FixOf D minus b
    Ld.Llist.size == (if minus then 17 else 22) &&
    (candidatesOf minus Ld.Llist).size == (if minus then 11 else 20) &&
    Ld.Llist.all (fun L => lOK D minus b L) &&
    l2OK D minus b Ld.Llist a2 Ld.l2wit &&
    l3Complete D b Ld.Llist Ld.l3tasks &&
    l3OK D b Ld.Llist Ld.l3tasks Ld.l3wit))

@[expose] def normalizesIdx (D : GrpData) (L : Array ℕ) (a : ℕ) : Bool :=
  a < D.O.size &&
  (let ca := D.O[a]!
   let ai := D.O[D.invI[a]!]!
   L.all fun x =>
     let p := Code.mul (Code.mul ca D.O[x]!) ai
     let y := D.idx.getD p D.O.size
     y < D.O.size && D.O[y]! == p && L.contains y)

@[expose] def goodAt (D : GrpData) (minus : Bool) (b : ℕ) (L : Array ℕ) (i : ℕ) : Bool :=
  i < D.O.size &&
  (let c := D.O[i]!
   let fix := Code.act c b == b
   let nor := normalizesIdx D L i
   fix == nor &&
   (let cen := L.all fun x => Code.mul c D.O[x]! == Code.mul D.O[x]! c
    if cen then codePow c 128 == Code.one else true))

@[expose] def goodArr (D : GrpData) (minus : Bool) (L : Array ℕ) (b : ℕ)
    (_ : Unit := ()) : Array Bool :=
  Array.ofFn (n := D.O.size) fun i => goodAt D minus b L i.val

@[expose] def n0Of (D : GrpData) (L : Array ℕ) (b : ℕ) (_ : Unit := ()) : Array ℕ :=
  ((List.range D.O.size).filter fun i =>
    Code.act D.O[i]! b == b && normalizesIdx D L i).toArray

@[expose] def certOK (D : GrpData) (gens : Array ℕ) (elems : Array ℕ)
    (par : Array (ℕ × ℕ)) : Bool :=
  elems.size != 0 && elems[0]! == 0 && par.size == elems.size &&
  (hashSetOfArray elems).size == elems.size &&
  elems.all (fun x => x < D.O.size) &&
  gens.all (fun g => g < D.O.size && elems.contains g) &&
  (let eset := hashSetOfArray elems
   (List.range elems.size).all (fun i =>
     i == 0 || (let p := (par[i]!).1
                let q := (par[i]!).2
                p < i && q < gens.size &&
                (let y := D.idx.getD (Code.mul D.O[elems[p]!]! D.O[gens[q]!]!) D.O.size
                 y < D.O.size && D.O[y]! == Code.mul D.O[elems[p]!]! D.O[gens[q]!]! &&
                 y == elems[i]!))) &&
   (List.range elems.size).all (fun i => gens.all fun g =>
     let p := Code.mul D.O[elems[i]!]! D.O[g]!
     let y := D.idx.getD p D.O.size
     y < D.O.size && D.O[y]! == p && eset.contains y))

@[expose] def k0OK (D : GrpData) (L : Array ℕ) (good : Array Bool) (F : KSub) : Bool :=
  certOK D F.gens F.elems F.par &&
  F.elems.all (fun x => good[x]!) &&
  L.all (fun x => F.elems.contains x)

@[expose] def cosetData (D : GrpData) (F : KSub) (fset : Std.HashSet ℕ) :
    Array ℕ × Bool :=
  let N := D.O.size
  let st := (List.range N).foldl (fun (st : Std.HashSet ℕ × Array ℕ × Bool) g =>
      if st.1.contains g then st
      else
        let (cov', ok') := F.elems.foldl (fun (st : Std.HashSet ℕ × Bool) f =>
          let y := D.idx.getD (Code.mul D.O[f]! D.O[g]!) N
          if y < N && !(st.1.contains y) then (st.1.insert y, st.2) else (st.1, false))
          (st.1, true)
        if fset.contains g then (cov', st.2.1, st.2.2 && ok')
        else (cov', st.2.1.push g, st.2.2 && ok'))
    ((∅ : Std.HashSet ℕ), (#[] : Array ℕ), true)
  (st.2.1, st.2.2 && st.1.size == N)

@[expose] def boolsOfString (s : String) : Array Bool :=
  (s.toList.map fun c => c == '1').toArray

@[expose] def parseNat (s : String) : ℕ :=
  s.toList.foldl (fun a c => if '0' ≤ c && c ≤ '9' then a * 10 + (c.toNat - 48) else a) 0

@[expose] def parseNats (s : String) : Array ℕ :=
  (s.splitOn " ").filter (fun x => !x.isEmpty) |>.map parseNat |>.toArray

@[expose] def parsePairs (s : String) : Array (ℕ × ℕ) :=
  (s.splitOn ";").filter (fun x => !x.isEmpty) |>.map (fun p =>
    match p.splitOn "," with
    | [a, b] => (parseNat a, parseNat b)
    | _ => (0, 0)) |>.toArray

@[expose] def parseWord (s : String) : Array ℕ :=
  (s.splitOn " ").filter (fun x => !x.isEmpty) |>.map parseNat |>.toArray

@[expose] def parseCloseWit (s : String) : CloseWit :=
  match s.splitOn ":" with
  | [h, ws] =>
    match h.splitOn "," with
    | [a, b, c] =>
      { rep := parseNat a, k := parseNat b, n := parseNat c,
        words := (ws.splitOn "|").map parseWord |>.toArray }
    | _ => default
  | _ => default

@[expose] def parseCloseLine (s : String) : Array CloseWit :=
  if s.isEmpty then #[] else
    (s.splitOn ";").filter (fun x => !x.isEmpty) |>.map parseCloseWit |>.toArray

@[expose] def parseCloses (s : String) : Array (Array CloseWit) :=
  (s.splitOn "\n").map (fun line =>
    if line.isEmpty then #[] else
      (line.splitOn ";").filter (fun x => !x.isEmpty) |>.map parseCloseWit |>.toArray)
    |>.toArray

@[expose] def closeTable (R : Array ℕ) (cl : Array CloseWit) :
    Std.HashMap ℕ CloseWit × Bool :=
  cl.foldl (fun (st : Std.HashMap ℕ CloseWit × Bool) w =>
    if w.rep < R.size && !(st.1.contains w.rep) then
      (st.1.insert w.rep w, st.2)
    else (st.1, false))
    ((∅ : Std.HashMap ℕ CloseWit), true)

@[expose] def isBadCode (D : GrpData) (good : Array Bool) (x : ℕ) : Bool :=
  let i := D.idx.getD x D.O.size
  i < D.O.size && D.O[i]! == x && !(good[i]!)

@[expose] def schreierBad (D : GrpData) (gens : Array ℕ) (good : Array Bool) (b : ℕ) :
    Option ℕ :=
  let one := Code.one
  let rec go (fuel : ℕ) (orb : Array ℕ) (tr : Std.HashMap ℕ (ℕ × ℕ)) (i : ℕ) : Option ℕ :=
    match fuel with
    | 0 => none
    | f + 1 =>
      if i < orb.size then
        let p := orb[i]!
        let up := (tr.getD p (one, one)).1
        let rec step (gs : List ℕ) (orb : Array ℕ) (tr : Std.HashMap ℕ (ℕ × ℕ)) :
            Option ℕ × Array ℕ × Std.HashMap ℕ (ℕ × ℕ) :=
          match gs with
          | [] => (none, orb, tr)
          | h :: rest =>
            if h < D.O.size then
              let q := Code.act D.O[h]! p
              let w := Code.mul D.O[h]! up
              if tr.contains q then
                let s := Code.mul (tr.getD q (one, one)).2 w
                if isBadCode D good s then (some s, orb, tr)
                else step rest orb tr
              else if isBadCode D good w then (some w, orb, tr)
              else
                let wi := D.idx.getD w D.O.size
                if wi < D.O.size then
                  step rest (orb.push q) (tr.insert q (w, D.O[D.invI[wi]!]!))
                else (some w, orb, tr)
            else (none, orb, tr)
        let (res, orb', tr') := step gens.toList orb tr
        match res with
        | some x => some x
        | none => go f orb' tr' (i + 1)
      else none
  go 64 #[b] ((∅ : Std.HashMap ℕ (ℕ × ℕ)).insert b (one, one)) 0

@[expose] def abortOK (D : GrpData) (F : KSub) (good : Array Bool) (b : ℕ) (r : ℕ) : Bool :=
  r < D.O.size &&
  if !(good[r]!) then true
  else
    let gens := F.gens.push r
    match schreierBad D gens good b with
    | some x => isBadCode D good x
    | none =>
      let gcodes := gens.map fun i => D.O[i]!
      let d := enumDataFast gcodes.toList
      let S := d.1.map fun c => D.idx.getD c D.O.size
      certOK D gens S d.2 && S.all (fun x => x < D.O.size) &&
        S.any (fun x => !(good[x]!))

@[expose] def closeOK (D : GrpData) (Flist : Array KSub) (N0 : Array ℕ)
    (F : KSub) (r m : ℕ) (w : CloseWit) : Bool :=
  r < D.O.size && w.rep == m && w.k < Flist.size && w.n < D.O.size &&
  N0.contains w.n && F.elems.size < (Flist[w.k]!).elems.size &&
  w.words.size == (Flist[w.k]!).gens.size &&
  (List.range (Flist[w.k]!).gens.size).all fun i =>
    let word := w.words[i]!
    let g := (Flist[w.k]!).gens[i]!
    word.all (fun q => q < F.gens.size + 1) &&
    (word.foldl (fun acc q =>
        Code.mul acc (if q < F.gens.size then D.O[F.gens[q]!]! else D.O[r]!)) Code.one) ==
      Code.mul (Code.mul D.O[w.n]! D.O[g]!) D.O[D.invI[w.n]!]!

@[expose] def sameSetHash (A : Array ℕ) (B : List ℕ) : Bool :=
  A.size == B.length &&
  (let SA := hashSetOfArray A
   let SB := hashSetOfArray B.toArray
   B.all (fun x => SA.contains x) && A.all (fun x => SB.contains x))

@[expose] def classOK (D : GrpData) (minus : Bool) (Om : Array ℕ) (KP : Array ℕ)
    (F : KSub) (cls : KClass) : Bool :=
  match cls with
  | .normal N =>
    N.size != 0 && N.contains 0 && N.any (fun x => x != 0) &&
    (let fset := hashSetOfArray F.elems
     let nset := hashSetOfArray N
     N.all (fun n => n < D.O.size && fset.contains n) &&
     (hashSetOfArray N).size == N.size &&
     (List.range N.size).all (fun i => (List.range N.size).all fun j =>
       let p := Code.mul D.O[N[i]!]! D.O[N[j]!]!
       let y := D.idx.getD p D.O.size
       y < D.O.size && D.O[y]! == p && nset.contains y) &&
     N.all (fun n => codePow D.O[n]! 128 == Code.one) &&
     F.gens.all (fun g => N.all fun n =>
       let p := Code.mul (Code.mul D.O[g]! D.O[n]!) D.O[D.invI[g]!]!
       let y := D.idx.getD p D.O.size
       y < D.O.size && D.O[y]! == p && nset.contains y))
  | .reducible v =>
    v < 64 && v != 0 &&
    (let W := spanArr (F.elems.toList.map fun i => Code.act D.O[i]! v)
     W.size < 64 && W.contains v &&
     F.gens.all fun g => W.all fun w => W.contains (Code.act D.O[g]! w))
  | .omega => sameSetHash (F.elems.map fun i => D.O[i]!) Om.toList
  | .whole => sameSetHash (F.elems.map fun i => D.O[i]!) D.O.toList
  | .pgl g =>
    minus == false && g < D.O.size && KP.size == 336 &&
    sameSetHash (KP.map fun y => Code.mul (Code.mul D.O[g]! y) D.O[D.invI[g]!]!)
      (F.elems.map fun i => D.O[i]!).toList

@[expose] def sameSetA (A B : Array ℕ) : Bool :=
  A.size == B.size && A.all (fun x => B.contains x) && B.all (fun x => A.contains x)

@[expose] def censusLOf (minus : Bool) (D : GrpData) (CD : CandData) : Bool :=
  let b := b0Of minus
  let good := goodArr D minus CD.L b ()
  let N0 := n0Of D CD.L b ()
  let KP := enumGroup kPGLGens ()
  lOK D minus b CD.L &&
  CD.flist.size != 0 &&
  CD.bits.size == CD.flist.size &&
  CD.closes.size == CD.flist.size &&
  CD.classif.size == CD.flist.size &&
  (CD.flist[0]!).elems.size == CD.L.size &&
  sameSetA (CD.flist[0]!).elems CD.L &&
  (List.range CD.flist.size).all fun fi =>
    let F := CD.flist[fi]!
    let fset := hashSetOfArray F.elems
    let (R, cov) := cosetData D F fset
    let bits := boolsOfString CD.bits[fi]!
    let (tab, tabOK) := closeTable R CD.closes[fi]!
    k0OK D CD.L good F && cov && bits.size == R.size && tabOK &&
    (List.range R.size).all (fun m =>
      let r := R[m]!
      if bits[m]! then
        match tab.get? m with
        | some w => closeOK D CD.flist N0 F r m w
        | none => false
      else
        (!(tab.contains m)) && abortOK D F good b r) &&
    classOK D minus D.Om KP F CD.classif[fi]!

end CFSG.GF2Type.Smith1979W3.Cert690

end
