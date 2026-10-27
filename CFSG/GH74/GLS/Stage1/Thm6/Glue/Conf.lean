module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG

@[expose] def IsL2Model (Kb : Type) [Group Kb] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), IVK.L2Field F ∧ Nonempty (Kb ≃* IVK.L2 F)

@[expose] def IsA7Model (Kb : Type) [Group Kb] : Prop :=
  Nonempty (Kb ≃* alternatingGroup (Fin 7))

structure Conf12B (G : Type) [Group G] [Finite G] (x : G) (Kb : Subgroup (CentralizerBar x)) :
    Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  x_order : orderOf x = 2
  comp : IsComponent Kb
  normal : Kb.Normal
  rankC : pRank 2 ↥(centralizer ({x} : Set G)) = 3

variable {G : Type} [Group G] [Finite G] {x : G}

theorem Conf12B.not_solvable {Kb : Subgroup (CentralizerBar x)} (c : Conf12B G x Kb) :
    ¬ Group.IsSolvable ↥(centralizer ({x} : Set G)) := by
  intro hsol
  have h1 : Group.IsSolvable (CentralizerBar x) := inferInstance
  have h2 : Group.IsSolvable ↥Kb :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective Kb)
  exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple c.comp.1 h2

end CFSG.GH74.GLS.Stage1.Thm6.Glue
