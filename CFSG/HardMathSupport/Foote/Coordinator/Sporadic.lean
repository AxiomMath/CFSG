module

public import CFSG.HardMathSupport.Foote.Coordinator.SporadicBase
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporX
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.Sporadic.SmallOddCore.HeLocal

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG CFSG.Blueprint

theorem end415K_M
    :
    End415K (NativeSporadic.Carrier .M) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_M

theorem end415K_M11 :
    End415K (NativeSporadic.Carrier .M11) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_M11

theorem end415K_M22 :
    End415K (NativeSporadic.Carrier .M22) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_M22

theorem end415K_M23 :
    End415K (NativeSporadic.Carrier .M23) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_M23

theorem end415K_M24 :
    End415K (NativeSporadic.Carrier .M24) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_M24

theorem end415K_Ru :
    End415K (NativeSporadic.Carrier .Ru) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_Ru

theorem end415K_McL :
    End415K (NativeSporadic.Carrier .McL) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_McL

theorem end415K_Co2 :
    End415K (NativeSporadic.Carrier .Co2) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_Co2

theorem end415K_Co3 :
    End415K (NativeSporadic.Carrier .Co3) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_Co3

theorem end415K_Th :
    End415K (NativeSporadic.Carrier .Th) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_Th

theorem end415K_Fi23 :
    End415K (NativeSporadic.Carrier .Fi23) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_Fi23

theorem end415K_B :
    End415K (NativeSporadic.Carrier .B) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_B

theorem end415K_Co1 :
    End415K (NativeSporadic.Carrier .Co1) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_Co1

theorem end415K_Fi22 :
    End415K (NativeSporadic.Carrier .Fi22) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_Fi22

theorem end415K_Fi24Prime :
    End415K (NativeSporadic.Carrier .Fi24Prime) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_Fi24Prime

theorem end415K_Ly :
    End415K (NativeSporadic.Carrier .Ly) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_Ly

theorem end415K_J4 :
    End415K (NativeSporadic.Carrier .J4) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_J4

theorem end415K_HN :
    End415K (NativeSporadic.Carrier .HN) :=
  end415K_of_sporCompData CFSG.ComponentClassification.HarrisLit.sporCompData_HN

theorem end415K_HS
    {Q : Type} [Group Q] (eQ : Q ≃* NativeSporadic.HS) : End415K Q := by
  refine end415K_of_innerComp5_false fun _ _ w K h => ?_
  obtain ⟨e⟩ := h.sl5
  have h360 := (CFSG.Sporadic.SmallOddCore.cti_hs_involution_local_components_simple_order_360
    ⟨eQ⟩ h.orderOf_eq h.isComponentOf).2.2
  have h120 : Nat.card ↥K = 120 := CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e.symm
  omega

theorem end415K_He
    {Q : Type} [Group Q] (eQ : Q ≃* NativeSporadic.He) : End415K Q := by
  refine end415K_of_innerComp5_false fun _ _ w K h => ?_
  obtain ⟨e⟩ := h.sl5
  have h1 := CFSG.Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order
    ⟨eQ⟩ h.orderOf_eq h.isComponentOf
  rw [card_quotient_center_of_sl25 e] at h1
  omega

theorem end415K_ONan
    {Q : Type} [Group Q] (eQ : Q ≃* NativeSporadic.ON) : End415K Q := by
  refine end415K_of_innerComp5_false fun _ _ w K h => ?_
  obtain ⟨e⟩ := h.subgroupOf_equiv
  have h1 :=
    CFSG.Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
      ⟨eQ⟩ w h.orderOf_eq _ h.comp
  rw [card_quotient_center_of_sl25 e] at h1
  omega

theorem end415K_Suz
    {Q : Type} [Group Q] (eQ : Q ≃* NativeSporadic.Suz) : End415K Q := by
  refine end415K_of_innerComp5_false fun _ _ w K h => ?_
  obtain ⟨e⟩ := h.subgroupOf_equiv
  have h1 := CFSG.Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order
    eQ w h.orderOf_eq _ h.comp
  rw [card_quotient_center_of_sl25 e] at h1
  omega

theorem sporTarget_of_four
    (hJ1 : End415K (NativeSporadic.Carrier .J1)) (hJ2 : End415K (NativeSporadic.Carrier .J2))
    (hJ3 : End415K (NativeSporadic.Carrier .J3)) (hM12 : End415K (NativeSporadic.Carrier .M12)) :
    SporTarget := by
  intro s
  cases s
  exacts [end415K_M11, hM12, end415K_M22, end415K_M23, end415K_M24, hJ1, hJ2, hJ3, end415K_J4,
    end415K_HS (MulEquiv.refl _), end415K_McL, end415K_He (MulEquiv.refl _), end415K_Ru,
    end415K_Suz (MulEquiv.refl _), end415K_ONan (MulEquiv.refl _), end415K_Co1,
    end415K_Co2, end415K_Co3, end415K_Fi22, end415K_Fi23, end415K_Fi24Prime, end415K_HN,
    end415K_Ly, end415K_Th, end415K_B, end415K_M]

end CFSG.HardMathSupport.Foote.Coordinator
