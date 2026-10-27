module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Stmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4d5

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l411_four_holds : L411FourStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau _ _ hc h4
  have c0 : W4Ctx0 t L S x₁ x₂ lam rho tau := { toCtx10 := hc, tM := S4B.w4_tM_of_ncard hc h4 }
  have hM : Nat.card (ctxM t tau x₁ x₂) = 3 * 2 ^ 9 := S4B.w4_card_M c0
  have hV : NormalIn (fourGrp x₁ x₂) (ctxM t tau x₁ x₂) := S4B.w4_normal_V c0
  have ca : W4Ctxa t L S x₁ x₂ lam rho tau :=
    { toW4Ctx0 := c0, card_M := hM, normal_V := hV, normal_E := S4B.w4_normal_E c0 hV }
  have cb : W4Ctxb t L S x₁ x₂ lam rho tau :=
    { toW4Ctxa := ca, O_eq_C := S4B.w4_O_eq_C ca, card_O := S4B.w4_card_O ca,
      lam_not_mem_O := S4B.w4_lam_not_mem_O ca }
  have cc : W4Ctxc t L S x₁ x₂ lam rho tau :=
    { toW4Ctxb := cb, M_eq := S4B.w4_M_eq cb, S_le_U := S4B.w4_S_le_U cb,
      U_sylow := S4B.w4_U_sylow cb }
  exact
    { toCtx10 := hc, tM := c0.tM, tG_X := S4B.w4_tG_X c0, normal_V := hV,
      normal_E := ca.normal_E, normal_N := S4B.w4_normal_N cc, normal_tN := S4B.w4_normal_tN cc,
      card_M := hM, card_O := cb.card_O, M_eq := cc.M_eq, O_eq_R := S4B.w4_O_eq_R cb,
      O_eq_CV := cb.O_eq_C, O_quot := S4B.w4_O_quot cb, CO_rho := S4B.w4_CO_rho cb,
      tauM := S4B.w4_tauM cc, ttauM := S4B.w4_ttauM cc, cent_E := S4B.w4_cent_E cb,
      normal_centE := S4B.w4_normal_centE cb, normal_Q := S4B.w4_normal_Q cc,
      base_le_Q := S4B.w4_base_le_Q cb, S_le_U := cc.S_le_U, U_sylow := cc.U_sylow }

end CFSG.OddStandard.SmallF3.HarrisU33
