module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Four
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem layerX_eq_coreLayer (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) :
    layerX Ω c = coreLayer Ω c := by
  apply le_antisymm
  · unfold layerX
    rw [Subgroup.closure_le]
    rintro x ⟨R₀, hR₀, hR₀c, hxR₀⟩
    obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR₀
    have hJtq : J ∈ tqMembers3 Ω c := ⟨hJ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ ⟨R₀, hRJ, hR₀c⟩⟩
    have hR₀core : R₀ ≤ TwinADescent.coreAt c J :=
      le_tightCore_of_isPGroup (le_inf hRJ.1 hR₀c) hRJ.2.1
    exact coreAt_le_coreLayer hJtq (hR₀core hxR₀)
  · refine coreLayer_le_of_forall fun J hJ => ?_
    have hcore : TwinADescent.coreAt c J ≤ layerX Ω c := by
      unfold TwinADescent.coreAt tightCore
      rw [Subgroup.closure_le]
      rintro x ⟨hxJ, hx2⟩
      have hxcore : x ∈ TwinADescent.coreAt c J := Subgroup.subset_closure ⟨hxJ, hx2⟩
      have hzp : IsPGroup 2 ↥(Subgroup.zpowers x) := hx2
      obtain ⟨V, hV, hxV⟩ := IsSylow2In.exists_ge (P := TwinADescent.coreAt c J)
        (T := Subgroup.zpowers x) hzp ((Subgroup.zpowers_le).mpr hxcore)
      obtain ⟨hVJ, hVc⟩ := (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mp hV
      exact Subgroup.subset_closure ⟨V, mem_RSet_of_isSylow2In hJ.1 hVJ, hVc,
        hxV (Subgroup.mem_zpowers x)⟩
    exact hcore
  
end Layer

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
