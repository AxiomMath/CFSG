module

public import Certificates.Data.Kernel.Q47K
public import CFSG.Certificates.Kernel.HexaKSound

public section

namespace CFSG.KC.Q47K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Q47 CFSG.ComponentClassification.GrSLit.HeldFix

structure QD where
  form : Array ℕ
  trans : List (List (Array ℕ))
  yg : List (Array ℕ)
  w1 : Array ℕ
  w2 : Array ℕ
  l30 : List (Array ℕ)
  orb : List (ℕ × ℕ)
  orbRep : List (Array ℕ)
  g1 : List (Array ℕ)
  g2 : List (Array ℕ)
  u1 : List (Array ℕ)
  u2 : List (Array ℕ)
  wit : List (List (List ℕ))
  ng : List (Array ℕ)
  ymat : List (List ℕ)
  nmat : List (List ℕ)

structure MD where
  xg : List (Array ℕ)
  qg : List (Array ℕ)
  eg : List (Array ℕ)
  fg : List (Array ℕ)
  z : Array ℕ
  reps : List (Array ℕ)
  ne : List (Array ℕ)
  d : List (Array ℕ)
  eb : List (Array ℕ)
  fb : List (Array ℕ)
  ke : List (List (Array ℕ))
  kf : List (List (Array ℕ))
  c : List (Array ℕ)

@[expose] def formCheckG (form g : Array ℕ) : Bool :=
  (List.range 64).all fun v => form[g[v]!]! == form[v]!

@[expose] def isomCheckG (form g : Array ℕ) : Bool := validA 64 g && addCheck g && formCheckG form g

@[expose] def admKG (form : Array ℕ) (k x : ℕ) : Bool :=
  decide (2 ^ k ≤ x) && form[x]! == form[2 ^ k]! &&
    (List.range k).all fun i => form[2 ^ i ^^^ x]! == form[2 ^ i ^^^ 2 ^ k]!

@[expose] def transCheckOG (form : Array ℕ) (trans : List (List (Array ℕ))) : Bool :=
  trans.length == 6 && (List.range 6).all fun k =>
    trans[k]!.all (fun t => isomCheckG form t && (List.range k).all fun i => t[2 ^ i]! == 2 ^ i) &&
      (List.range 64).all fun x => !(admKG form k x) || trans[k]!.any fun t => t[2 ^ k]! == x

@[expose] def bilinG (form : Array ℕ) (u v : ℕ) : ℕ := (form[u ^^^ v]! + form[u]! + form[v]!) % 2

@[expose] def nondegCheckG (form : Array ℕ) : Bool :=
  (List.range 64).all fun c => (List.range 64).any fun u =>
    (List.range 6).all fun i => bilinG form (2 ^ i) u == (c >>> i) % 2

@[expose] def oAllG (trans : List (List (Array ℕ))) : List (Array ℕ) :=
  trans.foldr (fun T acc => T.flatMap fun t => acc.map fun a => compA 64 t a) [idA 64]

@[expose] def oOrd3G (trans : List (List (Array ℕ))) : List (Array ℕ) :=
  (oAllG trans).filter fun w => eqA 64 (powN 64 w 3) (idA 64) && !(eqA 64 w (idA 64))

@[expose] def l30TabG (l30 : List (Array ℕ)) : Array (Array Bool) := l30.toArray.map memTab

@[expose] def tsCheckG (form W : Array ℕ) : Bool :=
  eightCheck W && W[0]! == 0 &&
    W.toList.all (fun a => W.toList.all fun b => W.contains (a ^^^ b)) &&
    W.toList.all fun a => form[a]! == 0

@[expose] def swapCheckG (w1 w2 t : Array ℕ) : Bool :=
  (mapsIntoM t w1 (memTab w1) && mapsIntoM t w2 (memTab w2)) ||
    (mapsIntoM t w1 (memTab w2) && mapsIntoM t w2 (memTab w1))

@[expose] def evalWordG (gs : List (Array ℕ)) (w : List ℕ) : Array ℕ :=
  w.foldr (fun l acc => compA 64 gs[l - 1]! acc) (idA 64)

@[expose] def stabCheckG (form : Array ℕ) (yg : List (Array ℕ)) (O : List (Array ℕ))
    (W : Array ℕ) (U : List (Array ℕ)) : Bool :=
  let mW := memTab W
  let UL := eltsN 64 U
  enumCheckN 64 U 8 && U.all (isomCheckG form) && enumCheckN 64 (U ++ yg) 1344 &&
    (U ++ yg).all (fun t => mapsInto t W W) &&
    (O.filter fun t => mapsIntoM t W mW).length == 1344 &&
    yg.all (fun y => U.all fun u => inLN 64 UL (conjA 64 y u))

@[expose] def witCheckG (yg : List (Array ℕ)) (h : Array ℕ) (ws : List (List ℕ)) : Bool :=
  ws.all (·.all fun l => decide (1 ≤ l) && decide (l ≤ 3)) &&
    enumCheckN 64 (ws.map (evalWordG (yg ++ [h]))) 32

@[expose] def witsCheckG (d : QD) : Bool :=
  let U₁ := eltsN 64 d.u1
  let U₂ := eltsN 64 d.u2
  (List.range 2).all fun s => (List.range 4).all fun k => (List.range 8).all fun j =>
    let g := (if s == 0 then d.g1 else d.g2)[k]!
    let u := (if s == 0 then U₁ else U₂)[j]!
    witCheckG d.yg (compA 64 g u) d.wit[(s * 4 + k) * 8 + j]!

@[expose] def refCheckG (d : QD) : Bool :=
  let O := oAllG d.trans
  let Y := eltsN 64 d.yg
  enumCheckN 64 d.yg 168 && d.yg.all (isomCheckG d.form) &&
    tsCheckG d.form d.w1 && tsCheckG d.form d.w2 &&
    d.w1.toList.all (fun a => a == 0 || !(d.w2.contains a)) &&
    d.yg.all (fun y => mapsInto y d.w1 d.w1 && mapsInto y d.w2 d.w2) &&
    transCheck Y d.w1 && transCheck Y d.w2 &&
    d.l30.length == 30 && d.l30.all eightCheck &&
    O.all (fun t => (List.range 30).any (fun j => mapsIntoM t d.w1 (l30TabG d.l30)[j]!) &&
      (List.range 30).any (fun j => mapsIntoM t d.w2 (l30TabG d.l30)[j]!)) &&
    d.orbRep.length == 4 && d.orbRep.all eightCheck && d.orb.length == 30 &&
    (List.range 30).all (fun j =>
      let p := d.orb[j]!
      (p.1 == 4 && sameSet d.l30[j]! d.w1) || (p.1 == 5 && sameSet d.l30[j]! d.w2) ||
        (decide (p.1 < 4) && decide (p.2 < 168) && mapsInto Y[p.2]! d.orbRep[p.1]! d.l30[j]!)) &&
    d.g1.length == 4 && d.g2.length == 4 && d.g1.all (isomCheckG d.form) &&
    d.g2.all (isomCheckG d.form) &&
    (List.range 4).all (fun k =>
      mapsInto d.g1[k]! d.w1 d.orbRep[k]! && mapsInto d.g2[k]! d.w2 d.orbRep[k]!) &&
    stabCheckG d.form d.yg O d.w1 d.u1 && stabCheckG d.form d.yg O d.w2 d.u2 &&
    d.wit.length == 64 && witsCheckG d &&
    enumCheckN 64 d.ng 336 && d.ng.all (isomCheckG d.form) &&
    d.yg.all (inLN 64 (eltsN 64 d.ng)) && d.ng.all (swapCheckG d.w1 d.w2) &&
    (O.filter (swapCheckG d.w1 d.w2)).length == 336

@[expose] def tableCheckG (d : QD) : Bool :=
  tableOK (certN 64 d.yg).pts d.ymat 3 2 [1, 0, 0, 0, 1, 0, 0, 0, 1] (· == ·)
      (· == [1, 0, 0, 0, 1, 0, 0, 0, 1]) &&
    tableOK (certN 64 d.ng).pts d.nmat 2 7 [1, 0, 0, 1] projEq7
      (fun m => m[1]! == 0 && m[2]! == 0 && m[0]! == m[3]!) &&
    d.nmat.all fun m => det7 m != 0

@[expose] def repCheckG (form : Array ℕ) (n : ℕ) (Qg reps : List (Array ℕ)) (z : Array ℕ) : Bool :=
  let Q := eltsN n Qg
  reps.length == 64 && eqA n reps[0]! (idA n) && reps.all (inLN n Q) &&
    (List.range 64).all (fun u => (List.range 64).all fun v =>
      eqA n (mulN n reps[u]! reps[v]!) reps[u ^^^ v]! ||
        eqA n (mulN n reps[u]! reps[v]!) (mulN n reps[u ^^^ v]! z)) &&
    Q.all (fun x => (List.range 64).any fun v => eqA n x reps[v]! || eqA n x (mulN n reps[v]! z)) &&
    (List.range 64).all fun v =>
      (eqA n (mulN n reps[v]! reps[v]!) (idA n) && form[v]! == 0) ||
        (eqA n (mulN n reps[v]! reps[v]!) z && form[v]! == 1)

@[expose] def classCheckG (trans : List (List (Array ℕ))) (D Eb K₁ K₂ : List (Array ℕ)) : Bool :=
  let EL := eltsN 64 Eb
  let L₁ := eltsN 64 K₁
  let L₂ := eltsN 64 K₂
  enumCheckN 64 Eb 4 && enumCheckN 64 K₁ 24 && enumCheckN 64 K₂ 24 &&
    D.all (inLN 64 L₁) && D.all (inLN 64 L₂) &&
    (oOrd3G trans).all fun w => !(Eb.all fun e => inLN 64 EL (conjA 64 w e)) ||
      inLN 64 L₁ w || inLN 64 L₂ w || enumCheckN 64 (D ++ [w]) 96

@[expose] def modelCheckG (d : QD) (n : ℕ) (m : MD) : Bool :=
  let XL := eltsN n m.xg
  let EL := eltsN n m.eg
  let FL := eltsN n m.fg
  repCheckG d.form n m.qg m.reps m.z && enumCheckN n m.ne 1024 && m.ne.all (inLN n XL) &&
    m.ne.all (fun g => m.eg.all fun q => inLN n EL (conjA n g q)) &&
    m.ne.all (fun g => m.fg.all fun q => inLN n FL (conjA n g q)) &&
    imgsOK n m.reps m.z m.ne m.d && imgsOK n m.reps m.z m.eg m.eb &&
    imgsOK n m.reps m.z m.fg m.fb &&
    enumCheckN 64 m.d 8 && m.ke.length == 2 && m.kf.length == 2 &&
    classCheckG d.trans m.d m.eb m.ke[0]! m.ke[1]! && classCheckG d.trans m.d m.fb m.kf[0]! m.kf[1]! &&
    m.c.length == 4 && m.c.all (isomCheckG d.form) &&
    (List.range 2).all fun i => (List.range 2).all fun j =>
      let YL := eltsN 64 (m.ke[i]! ++ m.kf[j]!)
      enumCheckN 64 (m.ke[i]! ++ m.kf[j]!) 168 &&
        d.yg.all fun y => inLN 64 YL (conjA 64 m.c[2 * i + j]! y)

@[expose] def q47CheckG (d : QD) (m16 m32 : MD) : Bool :=
  transCheckOG d.form d.trans && nondegCheckG d.form && refCheckG d && tableCheckG d &&
    modelCheckG d 16 m16 && modelCheckG d 32 m32

@[expose] def q47D : QD :=
  ⟨q47Form, q47Trans, q47YGens, q47W1, q47W2, q47L30, q47Orb, q47OrbRep, q47G1, q47G2, q47U1Gens,
    q47U2Gens, q47Wit, q47NGens, q47YMat, q47NMat⟩

@[expose] def q47M16 : MD :=
  ⟨heSyl16, heSylQ16, heSylE16, heSylF16, heSylZ16, q47Rep16, heSyl16, q47D16, q47Eb16, q47Fb16,
    q47KE16, q47KF16, q47C16⟩

@[expose] def q47M32 : MD :=
  ⟨hfT0Tabs32.toList, heAutQ32, heAutE32, heAutF32, heAutZ32, q47Rep32, q47NE32, q47D32, q47Eb32,
    q47Fb32, q47KE32, q47KF32, q47C32⟩

theorem q47Check_eq : q47Check = q47CheckG q47D q47M16 q47M32 := rfl

@[expose] def transElG (form : Array ℕ) (k : ℕ) (t : Array ℕ) : Bool :=
  formCheckG form t && (List.range k).all fun i => t[2 ^ i]! == 2 ^ i

@[expose] def modelDirectG (d : QD) (m : MD) : Bool :=
  m.reps.length == 64 && m.ke.length == 2 && m.kf.length == 2 && m.c.length == 4 &&
    m.c.all (formCheckG d.form) &&
    m.ne.length == m.d.length && m.eg.length == m.eb.length && m.fg.length == m.fb.length

@[expose] def directTransG (d : QD) : Bool :=
  d.trans.length == 6 &&
    (List.range 6).all (fun k => d.trans[k]!.all (transElG d.form k) &&
      (List.range 64).all fun x => !(admKG d.form k x) || d.trans[k]!.any fun t => t[2 ^ k]! == x) &&
    nondegCheckG d.form

@[expose] def directRefG (d : QD) : Bool :=
  d.yg.length == 2 && d.ng.length == 2 && d.u1.length == 3 && d.u2.length == 3 &&
    d.yg.all (transElG d.form 0) && tsCheckG d.form d.w1 && tsCheckG d.form d.w2 &&
    d.w1.toList.all (fun a => a == 0 || !(d.w2.contains a)) &&
    d.yg.all (fun y => mapsInto y d.w1 d.w1 && mapsInto y d.w2 d.w2) &&
    d.l30.length == 30 && d.l30.all eightCheck &&
    d.orbRep.length == 4 && d.orbRep.all eightCheck && d.orb.length == 30 &&
    (List.range 30).all (fun j => decide (d.orb[j]!.1 < 4) ||
      (d.orb[j]!.1 == 4 && sameSet d.l30[j]! d.w1) || (d.orb[j]!.1 == 5 && sameSet d.l30[j]! d.w2)) &&
    d.g1.length == 4 && d.g2.length == 4 && d.g1.all (transElG d.form 0) &&
    d.g2.all (transElG d.form 0) &&
    (List.range 4).all (fun k =>
      mapsInto d.g1[k]! d.w1 d.orbRep[k]! && mapsInto d.g2[k]! d.w2 d.orbRep[k]!) &&
    d.u1.all (transElG d.form 0) && d.u2.all (transElG d.form 0) &&
    (d.u1 ++ d.yg).all (fun t => mapsInto t d.w1 d.w1) &&
    (d.u2 ++ d.yg).all (fun t => mapsInto t d.w2 d.w2) &&
    d.wit.length == 64 && d.wit.all (·.all (·.all fun l => decide (1 ≤ l) && decide (l ≤ 3))) &&
    d.ng.all (transElG d.form 0)

@[expose] def directMatG (d : QD) : Bool :=
  d.ymat.length == 168 && d.ymat.all (fun m => m.length == 9 && m.all fun x => decide (x < 2)) &&
    d.ymat[0]! == [1, 0, 0, 0, 1, 0, 0, 0, 1] &&
    d.nmat.length == 336 && d.nmat.all (fun m => m.length == 4 && m.all fun x => decide (x < 7)) &&
    d.nmat[0]! == [1, 0, 0, 1] && d.nmat.all (fun m => det7 m != 0)

@[expose] def q47DirectG (d : QD) (m16 m32 : MD) : Bool :=
  directTransG d && directRefG d && directMatG d && modelDirectG d m16 && modelDirectG d m32

@[expose] def Bound (n w : Nat) (gs : List (Array ℕ)) (G : Nat → Nat) : Prop :=
  ∀ k < gs.length, gs[k]! = unpack n w (G k) ∧
    permOK n w (mask w) (n * w) (G k) (pinvS n w (mask w) (G k)) = true

structure ModelK where
  REP : Nat → Nat
  PZ : Nat
  GX : Nat → Nat
  NX : Nat
  TX : Nat → Nat
  EX : Nat → Nat
  SX : Nat → Nat
  GQ : Nat → Nat
  NQ : Nat
  TQ : Nat → Nat
  EQ : Nat → Nat
  SQ : Nat → Nat
  GE : Nat → Nat
  NE : Nat
  TE : Nat → Nat
  EE : Nat → Nat
  SE : Nat → Nat
  GF : Nat → Nat
  NF : Nat
  TF : Nat → Nat
  EF : Nat → Nat
  SF : Nat → Nat
  GNE : Nat → Nat
  NNE : Nat
  TNE : Nat → Nat
  ENE : Nat → Nat
  SNE : Nat → Nat
  GD : Nat → Nat
  GEb : Nat → Nat
  GFb : Nat → Nat
  GK : Nat → Nat → Nat
  CP : Nat → Nat
  cX : Nat

@[expose] noncomputable def kefG (m : MD) (k : ModelK) (c i : Nat) : Nat :=
  nIf(Nat.blt i (m.ke.getD (c / 2) []).length, k.GK (c / 2) i,
    k.GK (2 + c % 2) (i - (m.ke.getD (c / 2) []).length))

@[expose] noncomputable def clsOf (m : MD) (k : ModelK) (f : Bool) : Cls :=
  Bool.rec (motive := fun _ => Cls)
    ⟨m.eb.length, k.GEb, runK 64 7 m.eb.length k.GEb 100,
      runK 64 7 (m.ke.getD 0 []).length (k.GK 0) 100, runK 64 7 (m.ke.getD 1 []).length (k.GK 1) 100,
      m.d.length, k.GD⟩
    ⟨m.fb.length, k.GFb, runK 64 7 m.fb.length k.GFb 100,
      runK 64 7 (m.kf.getD 0 []).length (k.GK 2) 100, runK 64 7 (m.kf.getD 1 []).length (k.GK 3) 100,
      m.d.length, k.GD⟩ f

@[expose] def kListG (m : MD) (i : Nat) : List (Array ℕ) :=
  Bool.rec (motive := fun _ => List (Array ℕ)) (m.kf.getD (i - 2) []) (m.ke.getD i []) (decide (i < 2))

@[expose] noncomputable def kPts (m : MD) (k : ModelK) (i : Nat) : List Nat :=
  runK 64 7 (kListG m i).length (k.GK i) 100

@[expose] noncomputable def kefPts (m : MD) (k : ModelK) (c : Nat) : List Nat :=
  runK 64 7 ((m.ke.getD (c / 2) []).length + (m.kf.getD (c % 2) []).length) (kefG m k c) 200

@[expose] noncomputable def runsB (m : MD) (k : ModelK) : Bool :=
  Nat.beq (runK 64 7 m.d.length k.GD 100).length 8 && Nat.beq (runK 64 7 m.eb.length k.GEb 100).length 4 &&
    Nat.beq (runK 64 7 m.fb.length k.GFb 100).length 4 &&
    allN 4 (fun i => Nat.beq (kPts m k i).length 24) && allN 4 fun c => Nat.beq (kefPts m k c).length 168

@[expose] noncomputable def modelB (n w : Nat) (m : MD) (k : ModelK) (GY : Nat → Nat) : Bool :=
  modelYK n w m.ne.length k.GNE k.NX k.TX m.eg.length k.GE k.NE k.TE m.fg.length k.GF k.NF k.TF
    m.d.length k.GD (kPts m k) 2 GY k.CP (kefPts m k)

structure ModelOK (d : QD) (n w : Nat) (m : MD) (k : ModelK) (GY : Nat → Nat) : Prop where
  reps : Bound n w m.reps k.REP
  z : m.z = unpack n w k.PZ ∧ permOK n w (mask w) (n * w) k.PZ (pinvS n w (mask w) k.PZ) = true
  pX : Pin n w m.xg k.cX k.GX k.NX k.TX k.EX k.SX
  pQ : Pin n w m.qg m.qg.length k.GQ k.NQ k.TQ k.EQ k.SQ
  pE : Pin n w m.eg m.eg.length k.GE k.NE k.TE k.EE k.SE
  pF : Pin n w m.fg m.fg.length k.GF k.NF k.TF k.EF k.SF
  pNE : Pin n w m.ne m.ne.length k.GNE k.NNE k.TNE k.ENE k.SNE
  sNE : k.NNE = 1024
  dB : Bound 64 7 m.d k.GD
  eb : Bound 64 7 m.eb k.GEb
  fb : Bound 64 7 m.fb k.GFb
  ks : ∀ i < 4, Bound 64 7 (kListG m i) (k.GK i)
  c : Bound 64 7 m.c k.CP
  runs : runsB m k = true
  rep : repK n w k.REP k.NQ k.TQ k.PZ d.form = true
  img : (imgK n w k.REP k.PZ m.ne.length k.GNE k.GD && imgK n w k.REP k.PZ m.eg.length k.GE k.GEb &&
    imgK n w k.REP k.PZ m.fg.length k.GF k.GFb) = true
  model : modelB n w m k GY = true

end CFSG.KC.Q47K

end
