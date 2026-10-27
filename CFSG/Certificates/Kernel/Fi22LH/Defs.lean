module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Data.Kernel.Fi22.Letters
public import Certificates.Data.CFSGNative.Fi22.LH

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.Fi22L

structure LHData where
  R : Nat → Nat
  Z : Nat → Nat
  QA : Nat → Nat
  QB : Nat → Nat
  P : Nat → Nat
  X : Nat → Nat
  Y : Nat → Nat
  C : Nat → Nat
  M : Nat → Nat
  G : Nat → Nat
  TF : Nat → Nat
  ph : Nat → Nat
  al : Nat
  be : Nat
  bi : Nat
  op : Nat
  ol : Nat
  u : Nat
  lb0 : Nat
  lb1 : Nat
  eb : Nat
  h0 : Nat
  h1 : Nat
  h2 : Nat
  up : Nat
  pd : Nat
  qa : Nat
  qb : Nat
  qbi : Nat
  rq0 : Nat
  rq1 : Nat
  cq0 : Nat
  cq1 : Nat
  mq : Nat
  ml : Nat
  mt : Nat

@[expose] def LHChecks (D : LHData) : Prop :=
  D.al = orbT 0 ∧ D.be = orbT 1 ∧ D.op = orbT 2 ∧ D.ol = orbT 3 ∧
  (∀ j < 351, ent D.lb0 j = ((lhData ())[0]!)[j]!) ∧
  (∀ j < 351, ent D.lb1 j = ((lhData ())[1]!)[j]!) ∧
  (∀ i < 693, fld(D.pd, 10 * i, 1023) = phiData[i]!) ∧
  (∀ s < 26, tallSl D.R D.al D.be D.bi D.op D.ol s = true) ∧ (∀ s < 6, fixSl D.R D.Z s = true) ∧
  biK D.be D.bi = true ∧
  (∀ s < 20, setSl D.QA D.al D.be s = true) ∧ (∀ s < 20, setSl D.QB D.al D.be s = true) ∧
  orbBfsK D.QA = true ∧ orbBfsK D.QB = true ∧
  walkOK D.QA D.lb0 (fd D.mt 14 16383) = true ∧ walkOK D.QB D.lb1 (fd D.mt 28 16383) = true ∧
  notInK D.QA D.lb1 = true ∧ flatK D.QA D.qa D.qb D.qbi = true ∧
  (∀ l < 7, phiK D.op D.ol D.qa D.qb D.qbi D.ph l = true) ∧
  rootW D.R D.X D.lb0 D.rq0 = true ∧ rootW D.R D.Y D.lb1 D.rq1 = true ∧
  commK D.R D.X D.lb0 D.cq0 = true ∧ commK D.R D.Y D.lb1 D.cq1 = true ∧
  (∀ s < 4, domSlW D.R D.lb1 s = true) ∧ (∀ s < 8, rowSlW D.R D.P D.QA D.lb0 s = true) ∧
  rowInvK D.P D.QA (bs D.lb0) = true ∧ upK D.up = true ∧
  starW D.al D.eb D.lb0 D.lb1 D.h0 D.h1 D.h2 D.up D.pd = true ∧ failK D.R D.al D.eb D.h1 = true ∧
  swapK D.R D.C D.QA D.QB D.u D.lb0 D.lb1 (fd D.mt 42 16383) (fd D.mt 56 16383) = true ∧
  farW D.QA D.TF D.ph D.lb0 (fd D.mt 0 16383) (fd D.mt 80 16383) = true ∧
  (∀ s < 4, muSlW D.R D.Z D.P D.QA D.lb0 (fd D.mt 0 16383) s = true) ∧
  muTreeW D.R D.Z D.P D.QA D.M D.G D.mq (fd D.mt 70 1023) = true ∧
  mlK D.mq D.ml (fd D.mt 70 1023) = true ∧
  (∀ s < 8, edSlW D.R D.Z D.P D.QA D.G D.mq D.ml (fd D.mt 0 16383) s = true)

@[expose] def OrbOK : Prop :=
  orbL.alpha.size = 3510 ∧ orbL.beta.size = 3510 ∧ orbL.par.size = 3510 ∧ orbL.lab.size = 3510 ∧
  ∀ k < 3510, ap orbL.alpha k = ent (orbT 0) k ∧ ap orbL.beta k = ent (orbT 1) k ∧
    ap orbL.par k = ent (orbT 2) k ∧ ap orbL.lab k = ent (orbT 3) k ∧
    ent (orbT 0) k < 3510 ∧ ent (orbT 1) k < 3510 ∧ ent (orbT 0) (ent (orbT 0) k) = k ∧
    (0 < k → ent (orbT 2) k < k ∧ ((ent (orbT 3) k = 1 ∧ ent (orbT 0) (ent (orbT 2) k) = k) ∨
      (ent (orbT 3) k = 2 ∧ ent (orbT 1) (ent (orbT 2) k) = k)))

@[expose] def bitsOfNat (n : Nat) : Bits :=
  Array.ofFn (n := 55) fun w => UInt64.ofNat (n >>> (64 * w.val))

@[expose] def tabDec (n none : Nat) (f : Nat → Nat) : Table :=
  Array.ofFn (n := n) fun x => if f x.val = none then none32 else UInt32.ofNat (f x.val)

@[expose] noncomputable def orbDec (Q : Nat → Nat) : LHOrb :=
  ⟨Array.ofFn (n := 14080) fun k => bitsOfNat (sb (Q k.val)),
    Array.ofFn (n := 14080) fun k => fd (Q k.val) 7722 16383,
    Array.ofFn (n := 14080) fun k => fd (Q k.val) 7736 16383,
    Array.ofFn (n := 14080) fun k => fd (Q k.val) 7750 16383,
    Array.ofFn (n := 14080) fun k => fd (Q k.val) 7764 3,
    (List.range 14080).foldl (fun t k => t.insert (bitsOfNat (sb (Q k))) k) ∅⟩

@[expose] noncomputable def rootDec (X : Nat → Nat) (rq : Nat) : Tree :=
  ⟨tabDec 351 4096 (fun k => fd (X k) 0 4095), tabDec 3510 4095 (fun x => ent rq x),
    tabDec 351 4096 (fun k => fd (X k) 12 511), tabDec 351 4096 (fun k => fd (X k) 21 511)⟩

@[expose] noncomputable def farDec (QA TF : Nat → Nat) (nf : Nat) : Tree :=
  ⟨tabDec nf 16384 (fun k => fd (TF k) 0 16383), tabDec 14080 16383 (fun m => fd (QA m) 7792 16383),
    tabDec nf 16384 (fun k => fd (TF k) 14 16383), tabDec nf 16384 (fun k => fd (TF k) 28 7)⟩

@[expose] noncomputable def phiDec (ph : Nat → Nat) : Array Table :=
  Array.ofFn (n := 7) fun l => tabDec 14080 16384 (fun m => e14 (ph l.val) m)

@[expose] noncomputable def rowRD (D : LHData) : Array Nat :=
  Array.ofFn (n := 3510) fun f => fd (D.P f.val) 0 16383

@[expose] noncomputable def rowInvD (D : LHData) : Array Nat :=
  Array.ofFn (n := 14080) fun m => fd (D.QA m.val) 7780 4095

@[expose] noncomputable def muWD (D : LHData) : Array Nat :=
  Array.ofFn (n := 3510) fun f => fd (D.P f.val) 14 4095

@[expose] noncomputable def edWD (D : LHData) : Array Nat :=
  Array.ofFn (n := 3510) fun f => fd (D.P f.val) 26 16383

@[expose] noncomputable def closDec (C : Nat → Nat) : Tree :=
  ⟨tabDec 3510 4096 (fun k => fd (C k) 0 4095), tabDec 3510 4095 (fun x => fd (C x) 27 4095),
    tabDec 3510 4096 (fun k => fd (C k) 12 4095), tabDec 3510 4096 (fun k => fd (C k) 24 7)⟩

@[expose] noncomputable def lhDec (D : LHData) : LHComp :=
  let T := tauAll orbL
  let orb := #[orbDec D.QA, orbDec D.QB]
  let nm := fd D.mt 70 1023
  ⟨lhData.map bitsOf, orb, orb.map fun o => keyTable o.sets,
    lhData.map fun S => S.map fun s => T[s]!,
    #[rootDec D.X D.rq0, rootDec D.Y D.rq1],
    #[Array.ofFn (n := 351) fun k => fd (D.X k.val) 30 4095,
      Array.ofFn (n := 351) fun k => fd (D.Y k.val) 30 4095],
    #[Array.ofFn (n := 351) fun k => fd (D.X k.val) 42 511,
      Array.ofFn (n := 351) fun k => fd (D.Y k.val) 42 511],
    #[fd D.mt 42 16383, fd D.mt 56 16383],
    rowRD D,
    rowInvD D,
    phiDec D.ph,
    fd D.mt 0 16383,
    farDec D.QA D.TF (fd D.mt 80 16383),
    muWD D,
    Array.ofFn (n := nm) fun k => fd (D.M k.val) 0 4095,
    Array.ofFn (n := nm) fun k => fd (D.M k.val) 12 1023,
    Array.ofFn (n := nm) fun k => fd (D.M k.val) 22 4095,
    edWD D,
    Array.ofFn (n := 3510) fun f => fd (D.P f.val) 40 4095,
    Array.ofFn (n := 3510) fun f => fd (D.P f.val) 52 4095⟩

end CFSG.KS.Fi22LH
