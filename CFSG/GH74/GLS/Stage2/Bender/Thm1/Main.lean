module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Axb
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.QpExists
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der73
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der611
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der612
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der614
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der75Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Tail69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.L63
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67J1

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

theorem thm1_of (hQ : QP_exists) (h71 : Prop7_1) : Thm1PrimePower := by
  intro G _ _ z k S ctx hodd M hM
  by_contra hnp
  have hyp : Hyp6A z := hyp6A_of_odd hodd hM hnp
  obtain ⟨M', p, hch⟩ := exists_choice6 ctx.orderOf_z hyp
  have c6 : Ctx6 G z k S M' p := ⟨ctx, hyp, hch⟩
  have hpz : z ∈ normalizer ((Op p M' : Subgroup G) : Set G) := le_normalizer_Op p M' c6.z_mem
  obtain ⟨Q, hQm⟩ := hQ G z p (Op p M') c6.prime c6.p_ne_two ctx.orderOf_z
    (isPGroup_Op p c6.prime M') hpz c6.not_cen
  have h2 := h71 G z k S M' p c6 Q hQm
  have h3 := CFSG.GH74.GLS.Stage2.Final.Thm4.three_le_pRank_S ctx
  omega

structure Thm1Leaves : Prop

theorem thm1_primePower
    (h34 : Leaf_Prop34) (h33 : IVK_3_3_lift) (hB12 : Bender12) (hB13 : Bender13)
    (hB14 : Bender14) (h64 : Lemma6_4) (h67cf : CF67NonAltJ1) (_L : Thm1Leaves) : Thm1PrimePower := by
  have hI1123 : IG_11_23 := ig_11_23_thm
  have hPlane : OddNoncyclicPlane := oddNoncyclicPlane_thm
  have h67 : Prop6_7 := prop6_7_of hB12 hB13 (prop6_7E_of_cf67 (cf67_of_nonAlt (cf67NonAlt_of_nonAltJ1 h67cf)))
  have h61 : Prop6_1 := prop6_1_of hB12 hB13 ig_11_8_thm
  have h62 : Prop6_2 := prop6_2_of (L63.lemma6_3_of_6_4 h64) h64 hB13
  have h65 : Prop6_5 := prop6_5_of h62
  have h66 : Prop6_6 := prop6_6_of h61 h65
  have h610 : Lemma6_10 := lemma6_10_of h62 h66
  have h611 : Lemma6_11 := lemma6_11_of h61 h610 ig_11_8_thm
  have h612 : Lemma6_12 := lemma6_12_of h611 h67 hPlane
  have h613 : Lemma6_13 := lemma6_13_of h61 h610 h611 h612 h67 hPlane
  have h614 : Lemma6_14 := lemma6_14_of h61 h610 h611 h612 h613
  have h615 : Lemma6_15 := lemma6_15_of h61 h610 h612 h613 h67 hPlane
  have h68 : Prop6_8 := prop6_8_of h65 h66 h67 hPlane
  have h69 : Prop6_9 := prop6_9_of h68 h612 h614 h615 (tail6_9_of h33)
  have h72 : Lemma7_2 := lemma7_2_of h62 h66 h69 hB12 hI1123
  have h73 : Lemma7_3 := lemma7_3_of hB14 hI1123
  have h74 : Lemma7_4 := lemma7_4_of h72 h73 h34
  exact thm1_of qp_exists_thm (prop7_1_of (v7_exists_of h33) h72 h74 (lemma7_5_of h72 h73 h34) h34)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
