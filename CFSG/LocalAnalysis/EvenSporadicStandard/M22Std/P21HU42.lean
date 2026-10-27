module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21HCommCheck
public import Certificates.Certificate26121

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21H

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.Exceptional

theorem no_commuting_five_u42
    {E : Type} [Group E] (h : Blueprint.LieModel E .PSU 4 2 1) (u y : E) (hu : u * u = 1)
    (hu1 : u ≠ 1) (hy : orderOf y = 5) : u * y ≠ y * u := by
  obtain ⟨e⟩ := equiv_of_lieModel (lieModel_PSp_two_three_of_lieModel_PSU_four_two h)
  intro hcomm
  refine Certificates.certificate26121 _ _ (e u).2 (e y).2 ?_ ?_ ?_ ?_
  · have := congrArg (fun z => ((e z : QP45.originalSubgroup) : Equiv.Perm (Fin 45))) hu
    simpa using this
  · intro h1
    refine hu1 (e.injective (Subtype.ext ?_))
    simpa using h1
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hy
  · have := congrArg (fun z => ((e z : QP45.originalSubgroup) : Equiv.Perm (Fin 45))) hcomm
    simpa using this

end CFSG.EvenSporadicStandard.M22Std.P21H
