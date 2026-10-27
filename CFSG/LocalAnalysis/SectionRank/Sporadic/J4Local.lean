
module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.SectionRank.J4Local
public meta import Certificates.Data.CFSGNative.SectionRank.J4Local
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8024

public section

namespace CFSG.SectionRank

open CFSG.SectionRank.Native
open scoped commutatorElement

theorem j4_sylow3_check :
    (ops2 112).cubicCheck j4Sylow3Data = true :=
  Certificates.certificate8024.1

theorem J4_sylow3_cubic_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.J4,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.J4)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 2 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 :=
  (spec2 112).cubic_of_check j4Sylow3Data j4_sylow3_check

theorem j4_sylow11_check :
    (ops2 112).cubicCheck j4Sylow11Data = true :=
  Certificates.certificate8024.2

theorem J4_sylow11_cubic_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.J4,
      x ^ 11 = 1 ∧ y ^ 11 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.J4)) = 11 ^ 3 ∧
      h * x * h⁻¹ = x ^ 10 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 10 * ⁅x, y⁆ ^ 5 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 :=
  (spec2 112).cubic_of_check j4Sylow11Data j4_sylow11_check

end CFSG.SectionRank
