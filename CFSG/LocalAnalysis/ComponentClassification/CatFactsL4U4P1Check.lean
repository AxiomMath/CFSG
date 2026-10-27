module

public import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

inductive RowKind where
  | inner
  | noFive
  | small (gens : List Table) (ord : Nat)
  | five (gens : List Table) (ord : Nat)
  | a6 (l₁ l₂ : Table) (w : List (Option Table))

@[expose] def RowKind.isA6 : RowKind → Bool
  | .a6 _ _ _ => true
  | _ => false

structure Row where
  row : ClassRow
  kind : RowKind

structure Run where
  u : Table
  sylowGens : List Table
  sylowOrder : Nat
  rows : List Row

instance : Inhabited Run := ⟨⟨#[], [], 0, []⟩⟩

@[expose] def a6a : Table := #[1, 2, 0, 3, 4, 5]

@[expose] def a6b : Table := #[0, 2, 3, 4, 5, 1]

@[expose] def diagT (n : Nat) (x y : Table) : Table :=
  Array.ofFn (n := n + 6) fun i =>
    if i.val < n then x[i.val]! else y[i.val - n]! + UInt32.ofNat n

@[expose] def oddOK (n : Nat) (x : Table) : Bool :=
  !tblEq n x (idT n) && (tblEq n (powT n 3 x) (idT n) || tblEq n (powT n 5 x) (idT n))

@[expose] def ord8 (n : Nat) (x : Table) : Bool :=
  tblEq n (powT n 8 x) (idT n) && !tblEq n (powT n 4 x) (idT n)

@[expose] def inCOK (n : Nat) (sift : Table → Bool) (t g : Table) : Bool :=
  permOK n g && sift g && commTT n g t && invOK n g (invT n g)

@[expose] def pow2s : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

@[expose] def primeTD (q : Nat) : Bool := 2 ≤ q && (List.range q).all fun d => d < 2 || q % d != 0

@[expose] def oddPrimeDivs (N : Nat) : List Nat :=
  (List.range (N + 1)).filter fun q => 2 < q && N % q == 0 && primeTD q

@[expose] def configOK (n : Nat) (good : List (Array Table)) (L : Array Table) (v : Table) : Bool :=
  !involOK n v || !(L.any fun l => involOK n l && ord8 n (compT n v l)) ||
    good.any fun cl => memT n cl v

@[expose] def cosetOK (n : Nat) (sift : Table → Bool) (runs : List Run) (good : List (Array Table))
    (t : Table) (cl C L : Array Table) (w : List (Option Table)) (k : Nat) : Bool :=
  let u := (runs.getD (k - 1) default).u
  match w.getD k none with
  | some wk => permOK n wk && invOK n wk (invT n wk) &&
      (if k = 0 then sift wk else sift (compT n wk (invT n u))) &&
      commTT n wk t && C.all fun c => configOK n good L (compT n c wk)
  | none => k != 0 && !memT n cl (conjT n u (invT n u) t)

@[expose] def rowOK (n cap : Nat) (pg pgInv : Array Table) (sift : Table → Bool) (runs : List Run)
    (good : List (Array Table)) (first : Bool) (r : Row) : Bool :=
  let t := r.row.rep
  let N := r.row.centOrder
  let cg := r.row.centGens
  match r.kind with
  | .inner => !r.row.outer && !first
  | .noFive => r.row.outer && N % 5 != 0
  | .small gs ord => !r.row.outer && first && N % 5 != 0 && 288 % ord == 0 && N % ord == 0 &&
      pow2s.contains (N / ord) && gs.all (inCOK n sift t) && cg.all (inCOK n sift t) &&
      enumOK n cap ord gs && normOK n cap gs cg
  | .five gs ord => r.row.outer && 360 < ord && (N % 360 != 0 || N / 360 % 5 != 0) &&
      gs.all (fun g => inCOK n sift t g && !tblEq n g (idT n) && tblEq n (powT n 5 g) (idT n)) &&
      enumOK n cap ord gs
  | .a6 l₁ l₂ w =>
      let L := (mulClosureH n #[l₁, l₂] cap).1
      let Ce := mulClosureH n cg.toArray cap
      let cl := conjClosureH n pg pgInv t cap
      inCOK n sift t l₁ && inCOK n sift t l₂ && oddOK n l₁ && oddOK n l₂ &&
        cg.all (inCOK n sift t) && mulTreeOK n cg.toArray Ce.1 Ce.2.1 Ce.2.2 &&
        hkeysDistinct n Ce.1.toList && Ce.1.size == N &&
        enumOK n cap 360 [l₁, l₂] && normOK n cap [l₁, l₂] cg && N % 360 == 0 &&
        pow2s.contains (N / 360) && permOK (n + 6) (diagT n l₁ a6a) &&
        permOK (n + 6) (diagT n l₂ a6b) &&
        enumOK (n + 6) cap 360 [diagT n l₁ a6a, diagT n l₂ a6b] &&
        conjTreeOK n pg pgInv t cl.1 cl.2.1 cl.2.2 && hkeysDistinct n cl.1.toList &&
        cl.1.size == r.row.classSize && w.length == runs.length + 1 &&
        (List.range (runs.length + 1)).all (cosetOK n sift runs good t cl.1 Ce.1 L w)

@[expose] def extraOK (n : Nat) (pg : Array Table) (sift : Table → Bool) (u : Table) : Bool :=
  permOK n u && invOK n u (invT n u) && !sift (compT n u u) &&
    pg.all fun g => sift (conjT n u (invT n u) g)

@[expose] def goodClasses (n cap : Nat) (pg pgInv : Array Table) (runs : List Run) :
    List (Array Table) :=
  (runs.flatMap (·.rows)).filterMap fun r =>
    if r.kind.isA6 then some (conjClosureH n pg pgInv r.row.rep cap).1 else none

@[expose] def p1Check (n NP cap : Nat) (pg pgInv : Array Table) (sift : Table → Bool)
    (runs : List Run) (extra : List Table) : Bool :=
  let good := goodClasses n cap pg pgInv runs
  !runs.isEmpty && pg.all (fun g => invOK n g (invT n g)) &&
    runs.all (fun R => centDataOK n NP cap pg pgInv sift R.u R.sylowGens R.sylowOrder
      (R.rows.map (·.row)) && permOK n R.u && invOK n R.u (invT n R.u) && R.rows.all fun r =>
        0 < r.row.centOrder && r.row.oddPrimes == oddPrimeDivs r.row.centOrder) &&
    (List.range runs.length).all (fun i =>
      (runs.getD i default).rows.all (rowOK n cap pg pgInv sift runs good (i == 0))) &&
    extra.all (extraOK n pg sift) && permOK 6 a6a && permOK 6 a6b && oddOK 6 a6a && oddOK 6 a6b &&
    enumOK 6 cap 360 [a6a, a6b]

end CFSG.ComponentClassification.HarrisLit.P1
