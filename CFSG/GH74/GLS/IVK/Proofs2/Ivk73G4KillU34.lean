module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Core

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG Blueprint

theorem ivk73_u34 :
    Ivk73Empty (fun X _ => LieModel X .PSU 3 2 2) := by
  intro N _ _ L K Q h hL
  have hS : Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 2 2 := by
    rcases hL with ⟨-, hS⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hS
    all_goals exact absurd ht (by decide)
  obtain ⟨e⟩ := (RankTwoShapes.statedClassicalModel_PSU_three_two_iff ↥L 2 le_rfl).1 hS
  have hB : GH74.Uniqueness.Bender.BenderType ↥L 2 3 _ := .unitary 2 le_rfl e
  exact h.false_of_autRank fun E hE => by
    have := (hB.card_le_of_sq_eq_one_aut E hE).1
    omega

end CFSG.GH74.GLS.IVK
