module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Fixed
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

theorem ivk73_l33 :
    Ivk73Empty (fun X _ => LieModel X .PSL 3 3 1) := by
  intro N _ _ L K Q h hL
  obtain ⟨e⟩ := KGroups.L33.equiv_of_lieModel hL
  exact h.false_of_fixed_solvable fun α hα2 hα1 M hM =>
    KGroups.L33.fixed_solvable e α hα2 hα1 M hM

theorem ivk73_u33 :
    Ivk73Empty (fun X _ => LieModel X .PSU 3 3 1) := by
  intro N _ _ L K Q h hL
  obtain ⟨e⟩ := KGroups.U33.equiv_of_lieModel hL
  exact h.false_of_fixed_solvable fun α hα2 hα1 M hM =>
    KGroups.U33.fixed_solvable e α hα2 hα1 M hM

end CFSG.GH74.GLS.IVK
