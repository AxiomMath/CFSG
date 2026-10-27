module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.SectionRank.HSLocal
public meta import Certificates.Data.CFSGNative.SectionRank.HSLocal
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8018
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.SectionRank.Native
open scoped commutatorElement

theorem HS_sylow3_square_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.HS,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.HS)) = 3 ^ 2 ∧
      h * x * h⁻¹ = x ^ 1 * y ^ 0 ∧ h * y * h⁻¹ = x ^ 2 * y ^ 2 :=
  Certificates.certificate8018.1

theorem HS_sylow5_cubic_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.HS,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.HS)) = 5 ^ 3 ∧
      h * x * h⁻¹ = x ^ 3 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 3 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 4 :=
  Certificates.certificate8018.2

end CFSG.SectionRank
