module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOrth3Aux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOrth3Aux2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_orth3_series (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 3) :
    ∃ (N : Subgroup (OGroup Q)) (_ : N.Normal), IsPGroup 2 N ∧
      IsPGroup 3 ↥(twoRes (⊤ : Subgroup (OGroup Q ⧸ N))) :=
  ff_orth3_series_aux hQ hdim

theorem ff_orth3_solvable (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 3) :
    Group.IsSolvable (OGroup Q) :=
  ff_orth3_solvable_aux hQ hdim

theorem ff_xTwoCore_of_prod {H₁ H₂ : Type} [Group H₁] [Group H₂] [Finite H₁] [Finite H₂]
    (h₁ : ∃ (N : Subgroup H₁) (_ : N.Normal), IsPGroup 2 N ∧
      IsPGroup 3 ↥(twoRes (⊤ : Subgroup (H₁ ⧸ N))))
    (h₂ : ∃ (N : Subgroup H₂) (_ : N.Normal), IsPGroup 2 N ∧
      IsPGroup 3 ↥(twoRes (⊤ : Subgroup (H₂ ⧸ N))))
    {B : Type} [Group B] (f : B →* H₁ × H₂) (hf : Function.Injective f) : XTwoCore B :=
  ff_xTwoCore_of_prod_aux h₁ h₂ f hf

end CFSG.OddStandard.SmallF3.Omega
