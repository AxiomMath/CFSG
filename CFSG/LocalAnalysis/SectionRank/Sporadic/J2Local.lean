module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Data.CFSGNative.SectionRank.J2Local
public meta import Certificates.Data.CFSGNative.SectionRank.J2Local
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8020
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.SectionRank.Native
open scoped commutatorElement

theorem J2_sylow3_cubic_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.J2,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.J2)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 1 * ⁅x, y⁆ ^ 2 ∧
      h * y * h⁻¹ = x ^ 1 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 2 :=
  Certificates.certificate8020.1

theorem J2_sylow5_square_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.J2,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.J2)) = 5 ^ 2 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 4 ∧ h * y * h⁻¹ = x ^ 4 * y ^ 0 :=
  Certificates.certificate8020.2

end CFSG.SectionRank
