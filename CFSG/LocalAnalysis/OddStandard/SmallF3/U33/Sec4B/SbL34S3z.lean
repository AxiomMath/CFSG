module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Open
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3c2b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3f3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

theorem l34_s3_of_input (h : L34SigmaFourInput) : L34S3Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau W v hG hI ha hv
  obtain ⟨φ, hsurj, hker⟩ := h hG hI ha hv
  let σ : Sig4 t tau x₁ x₂ := ⟨φ, hsurj, hker⟩
  exact
    { toCtx4A := ha
      card_L := card_LO_of_sig ha σ
      P_core := pCoreOf_eq_ctxPL ha σ
      L_eq := LO_eq_sup ha σ
      O_le_P := O_le_ctxPL ha
      card_P := card_ctxPL_sig ha σ
      P_quot := P_quot_sig ha σ
      CP_rho := CP_rho_sig ha σ
      X_not_normal_P := X_not_normal_ctxPL ha σ
      syl_P := syl_ctxPL ha σ
      Z_P := exists_Z_P ha σ }

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
