module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

@[expose] noncomputable def lcL {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (u : Y) : Subgroup Y :=
  (coreHull (Om R) u).map (Subgroup.centralizer ({u} : Set Y)).subtype

theorem lcL_le_cu {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (u : Y) :
    lcL R u ≤ Subgroup.centralizer ({u} : Set Y) := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
