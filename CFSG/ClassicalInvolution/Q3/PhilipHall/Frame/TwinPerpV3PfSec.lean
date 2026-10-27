module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnTransportLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

section Lift

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {t : Y}

theorem longFundSetE3_of_lifts (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hz : IsUniqueInvolution (tightCore R) t)
    (hodd : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (Λ : Subgroup Y → Subgroup Y)
    (h1 : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      J ≤ Λ J ∧ IsClassicalMember3 (Λ J) t)
    (h2 : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), J ≠ J' →
        ∀ x ∈ Λ J, ∀ y ∈ Λ J', x * y = y * x) :
    LongFundSetE3 R t := by
  refine ⟨Λ, h1, h2, ?_⟩
  intro J hJ c hc
  have hct : c * t * c⁻¹ = t := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hJc := conj_mem_twinSet hz hJ hc
  have hcj := (h1 J hJ).2.conj c
  rw [hct] at hcj
  exact TwinConnT.liftUnique_in hΩ hJc.1 (isUniqueInvolution_of_mem_twinSet hz hJc)
    (Subgroup.map_mono (h1 J hJ).1) (h1 _ hJc).1 hcj (h1 _ hJc).2 hodd

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
