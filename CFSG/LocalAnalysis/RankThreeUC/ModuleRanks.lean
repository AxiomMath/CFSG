module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Subgroup Module

section

variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def fixedSubmodule (ρ : Representation (ZMod 2) A V) (E : Subgroup A) : Submodule (ZMod 2) V :=
  Representation.invariants (ρ.comp E.subtype)

@[expose] def involutionDisplacements (ρ : Representation (ZMod 2) A V) : Set ℕ :=
  {n | ∃ t : A, orderOf t = 2 ∧
    n = finrank (ZMod 2) (V ⧸ fixedSubmodule ρ (Subgroup.zpowers t))}

open Classical in
@[expose] noncomputable def moduleM (ρ : Representation (ZMod 2) A V) : ℕ :=
  if Even (Nat.card A) then sInf (involutionDisplacements ρ) else finrank (ZMod 2) V

end

end CFSG.LocalAnalysis.RankThreeUC
