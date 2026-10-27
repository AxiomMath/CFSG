module

public import CFSG.GH74.Generic.S1.TQ3BadSys
public import CFSG.GH74.Generic.S1.TQ3BarMain
public import CFSG.GH74.Generic.S1.SymNbhd
public import CFSG.GH74.Generic.S45.LLift
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.S3.PumpLift
public import CFSG.GH74.Generic.S1.TLeafA
public import CFSG.GH74.Generic.S1.DecompCore
public import CFSG.GH74.Generic.S1.TFrame
public import CFSG.GH74.Generic.S1.TLeafBar

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open CFSG.ClassicalInvolution.WeakCT CFSG.GH74.Filter.ClassicalOdd
open scoped MatrixGroups commutatorElement

theorem normal_subgroupOf_of_decomp {H : Type*} [Group H] {P A' R : Subgroup H}
    (hdec : ∀ p ∈ P, ∃ a ∈ A', a⁻¹ * p ∈ R) (hcomm : ∀ a ∈ A', ∀ w ∈ R, a * w = w * a) :
    (A'.subgroupOf P).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : H) ∈ A' := hn
  obtain ⟨a₀, ha₀, hw⟩ := hdec (g : H) g.2
  have hcw := hcomm (n : H) hn' _ hw
  show (g : H) * (n : H) * (g : H)⁻¹ ∈ A'
  have hg : (g : H) = a₀ * (a₀⁻¹ * (g : H)) := by group
  have h1 : (g : H) * (n : H) * (g : H)⁻¹ = a₀ * (n : H) * a₀⁻¹ := by
    set w : H := a₀⁻¹ * (g : H) with hwdef
    have hgw : (g : H) = a₀ * w := hg
    rw [hgw]
    calc a₀ * w * (n : H) * (a₀ * w)⁻¹ = a₀ * (w * (n : H) * w⁻¹) * a₀⁻¹ := by group
      _ = a₀ * ((n : H) * w * w⁻¹) * a₀⁻¹ := by rw [← hcw]
      _ = a₀ * (n : H) * a₀⁻¹ := by group
  rw [h1]
  exact A'.mul_mem (A'.mul_mem ha₀ hn') (A'.inv_mem ha₀)

end CFSG.GH74.Generic.S1
