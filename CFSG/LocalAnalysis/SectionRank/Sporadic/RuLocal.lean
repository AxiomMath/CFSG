module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.SectionRank.RuLocal
public meta import Certificates.Data.CFSGNative.SectionRank.RuLocal
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8029
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.SectionRank.Native
open scoped commutatorElement

theorem Ru_sylow3_cubic_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.Ru,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.Ru)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 1 * ⁅x, y⁆ ^ 1 ∧
      h * y * h⁻¹ = x ^ 2 * y ^ 2 * ⁅x, y⁆ ^ 1 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 2 :=
  Certificates.certificate8029.1

theorem Ru_sylow5_cubic_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.Ru,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.Ru)) = 5 ^ 3 ∧
      h * x * h⁻¹ = x ^ 3 * y ^ 0 * ⁅x, y⁆ ^ 3 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 3 * ⁅x, y⁆ ^ 4 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 4 :=
  Certificates.certificate8029.2

end CFSG.SectionRank
