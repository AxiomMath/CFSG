module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace BinaryRepresentations

open Subgroup

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def centerIn (H : Subgroup G) : Subgroup G := (Subgroup.center H).map H.subtype

@[expose] def commOn (ρ : Representation (ZMod 2) G V) (X : Subgroup G) (W : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {w | ∃ x ∈ X, ∃ u ∈ W, w = ρ x u - u}

@[expose] def conjClass (H X : Subgroup G) : Set (Subgroup G) :=
  {Y | ∃ h ∈ H, Y = X.map (MulAut.conj h).toMonoidHom}

end BinaryRepresentations

end CFSG.LocalAnalysis.RankThreeUC
