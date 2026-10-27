module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private noncomputable def conjEquiv (L : Subgroup G) (g : G) : ↥L ≃* ↥(CFSG.conjugate L g) :=
  Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

theorem isPSp43_conjugate {L : Subgroup G} (h : IsPSp43 L) (g : G) :
    IsPSp43 (CFSG.conjugate L g) :=
  LieModel.of_mulEquiv (conjEquiv L g) h

theorem isQuasisimple_conjugate {L : Subgroup G} (h : IsQuasisimple ↥L) (g : G) :
    IsQuasisimple ↥(CFSG.conjugate L g) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (conjEquiv L g) h

end CFSG.OddStandard.SmallF3.Omega
