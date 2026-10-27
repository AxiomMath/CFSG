module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0h
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0j
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbStmt1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem ctx11_of_tm : Ctx11OfTMStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hc h8
  have c8 : Ctx8 t L S x₁ x₂ lam rho tau := { toCtx10 := hc, tM := h8 }
  have hM : Nat.card (ctxM t tau x₁ x₂) = 3 * 2 ^ 10 := S4B.p0_card_M c8
  have hN : NormalIn (ctxN tau x₁ x₂) (ctxM t tau x₁ x₂) := S4B.p0_normal_N c8
  have c8a : Ctx8a t L S x₁ x₂ lam rho tau :=
    { toCtx8 := c8, card_M := hM, normal_N := hN, normal_V := S4B.p0_normal_V c8 hM hN }
  have c8b : Ctx8b t L S x₁ x₂ lam rho tau :=
    { toCtx8a := c8a, O_eq_C := S4B.p0_O_eq_C c8a, card_O := S4B.p0_card_O c8a,
      lam_not_mem_O := S4B.p0_lam_not_mem_O c8a }
  have c8c : Ctx8c t L S x₁ x₂ lam rho tau :=
    { toCtx8b := c8b, M_eq := S4B.p0_M_eq c8b, S_le_U := S4B.p0_S_le_U c8b,
      U_sylow := S4B.p0_U_sylow c8b }
  have c8d : Ctx8d t L S x₁ x₂ lam rho tau :=
    { toCtx8c := c8c, X_le_R := S4B.p0_X_le_R c8c, R_le_O := S4B.p0_R_le_O c8c,
      card_R := S4B.p0_card_R c8c, normal_R := S4B.p0_normal_R c8c,
      R_quot := S4B.p0_R_quot c8c, coset := S4B.p0_coset c8c }
  have c8e : Ctx8e t L S x₁ x₂ lam rho tau :=
    { toCtx8d := c8d, CR_rho := S4B.p0_CR_rho c8d, tR := S4B.p0_tR c8d,
      ttauR := S4B.p0_ttauR c8d, tauR := S4B.p0_tauR c8d, tM_O := S4B.p0_tM_O c8d,
      tauM := S4B.p0_tauM c8d, tauO := S4B.p0_tauO c8d }
  exact
    { toCtx10 := hc, tM := h8, card_M := hM, normal_N := hN, normal_V := c8a.normal_V,
      card_O := c8b.card_O, M_eq := c8c.M_eq, tM_O := c8e.tM_O, tauM := c8e.tauM,
      tauO := c8e.tauO, center_O := S4B.p0_center_O c8e,
      cent_trho := S4B.p0_cent_trho hc.toCtx4, CO_dihedral := S4B.p0_CO_dihedral c8e,
      CO_center := S4B.p0_CO_center c8e, S_le_U := c8c.S_le_U, U_sylow := c8c.U_sylow,
      X_le_R := c8d.X_le_R, R_le_O := c8d.R_le_O, card_R := c8d.card_R,
      normal_R := c8d.normal_R, R_quot := c8d.R_quot, R_eq := S4B.p0_R_eq c8e,
      normal_Q := S4B.p0_normal_Q c8e, base_le_Q := S4B.p0_base_le_Q c8e,
      phi_Q := S4B.p0_phi_Q c8e, O_eq := S4B.p0_O_eq c8e, CR_rho := c8e.CR_rho,
      tR := c8e.tR, ttauR := c8e.ttauR, tauR := c8e.tauR }

end CFSG.OddStandard.SmallF3.HarrisU33
