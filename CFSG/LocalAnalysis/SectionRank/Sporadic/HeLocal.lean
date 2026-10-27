module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Data.CFSGNative.SectionRank.HeLocal
public meta import Certificates.Data.CFSGNative.SectionRank.HeLocal
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8019
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.SectionRank.Native
open scoped commutatorElement

theorem He_sylow3_cubic_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.He,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.He)) = 3 ^ 3 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 2 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 1 * y ^ 0 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 1 :=
  Certificates.certificate8019.1

theorem He_sylow5_square_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.He,
      x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.He)) = 5 ^ 2 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 4 ∧ h * y * h⁻¹ = x ^ 4 * y ^ 0 :=
  Certificates.certificate8019.2.1

theorem He_sylow7_cubic_witness :
    ∃ x y h : CFSG.Blueprint.NativeSporadic.He,
      x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.He)) = 7 ^ 3 ∧
      h * x * h⁻¹ = x ^ 2 * y ^ 0 * ⁅x, y⁆ ^ 3 ∧
      h * y * h⁻¹ = x ^ 0 * y ^ 1 * ⁅x, y⁆ ^ 0 ∧
      h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 2 :=
  Certificates.certificate8019.2.2

end CFSG.SectionRank
