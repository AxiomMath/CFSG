module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigBrB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigBrC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigNC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigHat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigXB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigMove
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigX0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform


variable {n : ℕ}

namespace ZSig.ZCtx

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g x : Y}

theorem x0 (H : ZCtx n Y R S t K' W u e g x) (hT : Thm4RTwinBelow 3 n) (hP : TL4.TightBelowRPlus 3 n)
    (mv : E4ModelMove) :
    ∃ x₀ ∈ p23XE R e x, x₀ * t = t * x₀ ∧ IsPGroup 3 (Subgroup.zpowers x₀) ∧ x₀ * e * x₀⁻¹ ≠ e := by
  have hoc := H.oc mFA_holds
  have hOc : ∀ o ∈ oddCoreOf (p23XE R e x), ∀ y ∈ p23XE R e x, o * y = y * o := by
    intro o ho y hy
    obtain ⟨o', ho', rfl⟩ := ho
    have hc := Subgroup.mem_center_iff.mp (hoc ho') ⟨y, hy⟩
    exact (congrArg Subtype.val hc).symm
  have heb : ∀ J ∈ Om R, J ≤ conjSub x (rLayer (Om R) e) →
      ∃ y ∈ p23XE R e x, conjSub y (tightCore R) = J := by
    intro J hJ hJx
    obtain ⟨y, hy⟩ := H.trans_N hT hoc hJ (hJx.trans le_sup_right)
    exact ⟨y, y.2, hy⟩
  rcases H.outcome hT mFA_holds hP with h | h | h
  · exact p23E8ZSigX0_of_inO2 hP hT H.cfg H.ae6 H.ne H.two heb H.t_mem_N hOc h
  · by_cases hno : TightInO2 (secInv (p23XE R e x) ⟨t, H.t_mem_N⟩)
    · exact p23E8ZSigX0_of_inO2 hP hT H.cfg H.ae6 H.ne H.two heb H.t_mem_N hOc hno
    · exact H.x0_of_twinE4 mv hT mFA_holds H.e_not_central H.et_not_central hno h
  · exact H.x0_of_longFund h

end ZSig.ZCtx

theorem p23E8ZSigX0_of_e4 (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hN : P23E8ZNormT n) (mv : ZSig.E4ModelMove) : P23E8ZSigX0 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hz hA6 x hx hxN
  have hZ2 : P23E8ZTwo n := ZTwo.p23E8ZTwo_proved hT (p23Two_of_thmEQ8 hE hcit hP) hα
  exact (ZSig.zCtx_of_inputs hE hT hα hN hZ2 hcit hP hc hno hz hA6 hx hxN).x0 hT hP mv

theorem p23E8ZSigX0_proved (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hN : P23E8ZNormT n) : P23E8ZSigX0 n :=
  p23E8ZSigX0_of_e4 hE hT hα hN ZSig.e4ModelMove_of_certs

theorem p23E8ZSig_proved (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n) (hα : P23Alpha n)
    (hN : P23E8ZNormT n) : P23E8ZSig n :=
  p23E8ZSig_of_x0 hE hT hα hN (p23E8ZSigX0_proved hE hT hα hN)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
