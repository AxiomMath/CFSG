module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8I1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23RE78
public import CFSG.ClassicalInvolution.Sp62Rec.RecPkg

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Q3.AE.Wr

theorem twinE4_of_lieModel_psp32 {Y : Type} [Group Y]
    (h : CFSG.Blueprint.LieModel Y .PSp 3 2 1) : TwinE4 Y :=
  ⟨Y, inferInstance, MonoidHom.id Y, Function.surjective_id,
    fun y => ⟨0, by rw [pow_zero, pow_one]; exact Subtype.ext (by simpa using y.2)⟩, Or.inl h⟩

section Pkg



variable {n : ℕ}

theorem p23E8Z_of_pkg (hL : P23E8ZPkg n) : P23E8Z n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hz hAE
  obtain ⟨Z, T, A, X, hpkg⟩ := p23E8ZPkg_toPkg hL hcit hP Y R S t K' W u e g hc hno hz hAE
  exact twinE4_of_lieModel_psp32 hpkg.lieModel

end Pkg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
