module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeZStar
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConn
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeAlpha
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerpMainR

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace Perp23

namespace Three

section Main


variable {r n : ℕ}

theorem twinPerp233R_of_noQ16E4 (hr : 4 ≤ r) (hNo : NoQ16E4) (hE : TwinThmER r n)
    (h4 : Thm4TwinSupplyR r n) : TwinPerp233R r n := by
  intro Y _ _ R S t hP h2 W hW htW hS4 hwc
  obtain ⟨K', hK', hne, ⟨D⟩⟩ := Two.exists_twoFrame hP h2 hW htW hS4
  let d : Data r n Y R S t := ⟨hP, h2, W, hW, htW, hS4, K', hK', hne, D⟩
  have h4' : Thm4RTwinBelow r n := h4 hP.core.below hP.core.tbelow hP.core.twinBelow
  have hT : Thm1RTwinInO2 r n := thm1RTwinInO2_of_below hr hNo hP.core.twinBelow
  have he1 : D.ce ≠ 1 := ce_ne_one_of_wCentral D hP.core.hyp hW d.ctx hwc
  have hH : Hyp51 (bGrp D) := d.hyp51_bGrp h4' hT he1
  have hZ := d.zStar_u hr h4' hT he1
  have hStar := d.starT hr
  have hG : Subgroup.centralizer ({D.u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤ :=
    Two.sup_centralizer_eq_top_of_thmE hr hE hP h2 hW htW hS4 hK' hne d.u_mem_sup D.u_mem_W
      (u_mul_self D d.hc) (d.u_ne_one he1) d.u_ne_t
  exact d.false_of_zStar hH he1 hZ hStar hG

end Main

section Final


variable {r n : ℕ}

theorem twinPerp233R_of_thmE (hr : 4 ≤ r) (hE : TwinThmER r n) (h4 : Thm4TwinSupplyR r n) :
    TwinPerp233R r n :=
  twinPerp233R_of_noQ16E4 hr noQ16E4_holds hE h4

end Final

end Three

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
