module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Fixed
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.GH74.KGroups.CoverEven

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG Blueprint

theorem ivk73_l216 : Ivk73Empty (fun X _ => LieModel X .PSL 2 2 4) := by
  intro N _ _ L K Q h hL
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := ↥L) (f := 4) (by norm_num) hL
  have hB : GH74.Uniqueness.Bender.BenderType ↥L 4 1 1 := .linear 4 (by norm_num) e
  have hcyc : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) := hB.outer_linear.1
  refine h.false_of_inner_solvable (fun E hE => GHInv.card_le_two_of_isCyclic hcyc E hE)
    (fun y hy2 hy1 M hM => ?_)
  have hP : IsPGroup 2 (centralizer ({y} : Set ↥L)) := hB.centralizer_involution_isPGroup hy2 hy1
  have hM2 : IsPGroup 2 ↥M := hP.to_le hM
  have := hM2.isNilpotent
  infer_instance

end CFSG.GH74.GLS.IVK
