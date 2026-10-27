module

public import CFSG.ClassicalInvolution.Asc77.AscT7HC4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Dich
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section Gen

theorem eq_of_mk_eq_of_involutions {H : Type} [Group H] [Finite H] {x y : H} (hx2 : x * x = 1)
    (hy2 : y * y = 1) (hxy : x * y = y * x)
    (h : QuotientGroup.mk' (classicalInvolutionOddCore H) x =
      QuotientGroup.mk' (classicalInvolutionOddCore H) y) : x = y := by
  have hw : x⁻¹ * y ∈ classicalInvolutionOddCore H := QuotientGroup.eq.mp h
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hw2 : (x⁻¹ * y) * (x⁻¹ * y) = 1 := by
    rw [hxi]
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, mul_one]
  have := CFSG.ClassicalInvolution.Asc77.T7H.eq_one_of_mem_odd_of_sq
    (CFSG.ComponentClassification.OddCore.odd_card H) hw hw2
  rw [hxi] at this
  exact (inv_eq_of_mul_eq_one_right this : x⁻¹ = y).symm.trans hxi |>.symm

end Gen

section Dist

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem secImg_ne_of_twins (hΩ : HypOmegaGen Ω) (hc2' : IsPGroup 2 (Subgroup.zpowers c))
    {J₁ J₂ : Subgroup G} (hKtq : J₁ ∈ tqMembers3 Ω c) (hK'tq : J₂ ∈ tqMembers3 Ω c)
    (hne : J₂ ≠ J₁) {w : G} (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w) :
    secImg Ω c J₁ ≠ secImg Ω c J₂ := by
  intro heq
  have hΛ : HypOmegaGen (cFam Ω c) := TwinADescent.hypOmegaGen_coreFamily hΩ hc2'
  have hcore_ne : (TwinADescent.coreAt c J₁).subgroupOf (Subgroup.centralizer ({c} : Set G)) ≠
      (TwinADescent.coreAt c J₂).subgroupOf (Subgroup.centralizer ({c} : Set G)) := by
    intro he
    have := congrArg (Subgroup.map (Subgroup.centralizer ({c} : Set G)).subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J₁),
      Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J₂)] at this
    exact hne (eq_of_coreAt_eq hΩ hc2' hKtq hK'tq this).symm
  exact TwinExitPf2.false_of_imgOf_eq hΛ
    ⟨TwinADescent.coreAt c J₁, TwinADescent.coreAt_mem_coreFamily hKtq,
      TwinADescent.coreAt_le_centralizer c J₁, rfl⟩
    ⟨TwinADescent.coreAt c J₂, TwinADescent.coreAt_mem_coreFamily hK'tq,
      TwinADescent.coreAt_le_centralizer c J₂, rfl⟩
    hcore_ne
    (isUniqueInvolution_subgroupOf
      (isUniqueInvolution_coreAt_of_tq hΩ hc2' hKtq hw₁)
      (TwinADescent.coreAt_le_centralizer c J₁))
    (isUniqueInvolution_subgroupOf
      (isUniqueInvolution_coreAt_of_tq hΩ hc2' hK'tq hw₂)
      (TwinADescent.coreAt_le_centralizer c J₂))
    (le_coreHull hKtq) (le_coreHull hK'tq) heq

end Dist

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
