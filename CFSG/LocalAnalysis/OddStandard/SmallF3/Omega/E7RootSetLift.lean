module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetRoots
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetLiftAux2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega.E7RootSet

open Certificates.OmegaSevenMax CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_weyl_of_image_rootSet
    (g : OGroup qForm) (hg : rootSet.image (g : V ≃ₗ[ZMod 3] V) = rootSet) :
    ∃ w : WeylGroup Tag.E7, ∀ v : Fin Tag.E7.rank → ℤ,
      (g : V ≃ₗ[ZMod 3] V) (redV v) = redV (w • v) :=
  CFSG.StandardType.e7LiftP11_exists_weyl_of_image_rootSet g hg

end CFSG.OddStandard.SmallF3.Omega.E7RootSet

end
