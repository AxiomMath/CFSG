module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporPermCode

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporPerm

open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def PD.wd (D : PD) : Array (List Nat) := mkWd D.G D.Ts D.par

@[expose] def PD.iv (D : PD) : Array Nat := mkIv D.B.length D.L D.wd D.Ts

@[expose] def PD.ivMap (D : PD) : Std.HashMap Nat Nat := mkIvMap D.n D.B.length D.Ts D.iv

@[expose] def PD.fs (D : PD) : Array Bool := mkFs D.n D.Ts D.iv

@[expose] def PD.ptab (D : PD) : Array Nat :=
  mkPtab D.n D.B.length D.L D.wd D.Ts D.iv D.ivMap D.fs

@[expose] def PD.conj (D : PD) : Array Nat × Array (List Nat) :=
  mkConj D.n D.B.length D.L D.G.length (ptsOf D.B D.G) D.wd D.iv D.ivMap

@[expose] def PD.fxr (D : PD) : Array (List Nat) := mkFxR D.n D.L D.wd D.iv D.conj.1

@[expose] def PD.fx (D : PD) : Array (List Nat) := mkFx D.L D.conj.1 D.conj.2 D.fxr

@[expose] def PD.mem (D : PD) : Array (Array Bool) := mkMem D.n D.fx

@[expose] def PD.ctab (D : PD) : Array Nat := mkCtab D.iv.size D.fx D.mem D.ptab

@[expose] def PD.nbr (D : PD) : Array (List Nat) := mkNbr D.iv.size D.ptab

@[expose] def PD.Tables (D : PD) : Prop :=
  D.B ≠ [] ∧ WdOK D.G D.Ts D.par D.wd ∧ MapOK D.n D.B.length D.Ts D.iv D.ivMap ∧
    FsOK D.Ts D.iv D.fs ∧ ConjOK D.L D.G.length (ptsOf D.B D.G) D.wd D.Ts D.iv D.conj.1 D.conj.2 ∧
    dfsB D.iv.size (prAt D.iv.size D.ptab) (ctAt D.iv.size D.ctab) (fun i => D.nbr[i]!) = true

instance (D : PD) : Decidable D.Tables := by
  unfold PD.Tables
  infer_instance

@[expose] def PD.Check (D : PD) : Prop :=
  BaseEnumOK D.n D.B D.G D.Gi D.Ts D.par D.cl ∧ D.Tables

instance (D : PD) : Decidable D.Check := by
  unfold PD.Check
  infer_instance

end CFSG.QuasithinUnique.A5.Kc3SporPerm
