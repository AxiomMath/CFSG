module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.J4SylowThreeIrr
public meta import Certificates.Data.J4SylowThreeIrr
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate1015335
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.SectionRank.Native
open scoped commutatorElement

theorem j4_sylow3_irr_check :
    (ops2 112).cubicCheck j4Sylow3IrrData = true :=
  Certificates.certificate1015335

theorem J4_sylow3_irr_cubic_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.J4,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.J4)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 1 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 2 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 :=
  (spec2 112).cubic_of_check j4Sylow3IrrData j4_sylow3_irr_check

end CFSG.SectionRank
