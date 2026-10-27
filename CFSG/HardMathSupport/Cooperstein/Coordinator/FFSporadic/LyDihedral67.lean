module

public import Certificates.Certificate1037001
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Blueprint

theorem ly_dihedral67 :
    ∀ t : NativeSporadic.Ly, t * t = 1 → t ≠ 1 →
      ∃ c : NativeSporadic.Ly, orderOf (t * (c * t * c⁻¹)) = 67 :=
  Certificates.certificate1037001

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
