module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Fixed
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.GH74.KGroups.Sz8

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG Blueprint

theorem ivk73_l28 :
    Ivk73Empty (fun X _ => LieModel X .PSL 2 2 3) := by
  intro N _ _ L K Q h hL
  exact h.false_of_fixed_solvable fun α hα2 hα1 M hM =>
    KGroups.L28.fixed_solvable hL α hα2 hα1 M hM

theorem ivk73_m11 :
    Ivk73Empty (fun X _ => NativeSporadic.IsSporadic X .M11) := by
  intro N _ _ L K Q h hL
  exact h.false_of_fixed_solvable fun α hα2 hα1 M hM =>
    KGroups.M11.fixed_solvable hL α hα2 hα1 M hM

theorem ivk73_sz8 :
    Ivk73Empty (fun X _ => LieModel X .twistedB2 0 2 3) := by
  intro N _ _ L K Q h hL
  obtain ⟨e⟩ := KGroups.Sz8.equiv_of_lieModel hL
  exact h.false_of_fixed_solvable fun α hα2 hα1 M hM =>
    KGroups.Sz8.fixed_solvable e α hα2 hα1 M hM

end CFSG.GH74.GLS.IVK
