module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalFixed

public section

namespace CFSG.ComponentClassification.J2Cover.External

open CFSG.Monster.B.Co2

@[expose] noncomputable def fusionModel : Models.P :=
  ⟨permC, by rw [Models.P_eq_autP]; exact QC_le_P permC_mem_QC⟩

theorem coe_fusionModel : (fusionModel : Equiv.Perm (Fin 315)) = permC := rfl

theorem decomp_fusion (i : Fin 4725) :
    ∃ (_ : fusionP[(i : ℕ)]! < 128) (hc : fusionI[(i : ℕ)]! < 4725),
      Models.factor i fusionModel = Models.elt fusionP[(i : ℕ)]! ∧
        Models.cosetAct i fusionModel = ⟨fusionI[(i : ℕ)]!, hc⟩ := by
  obtain ⟨h1, h2, h3⟩ := lamCheck_parts.1 i i.isLt
  have h := eq_of_eqA (rep_compA (Models.rep_repArrs i.isLt) rep_permC)
    (rep_compA (Models.rep_eltArrs h1) (Models.rep_repArrs h2)) h3
  have h' : Models.rep i * (fusionModel : Equiv.Perm (Fin 315)) =
      (Models.elt fusionP[(i : ℕ)]! : Equiv.Perm (Fin 315)) *
        Models.rep ((⟨fusionI[(i : ℕ)]!, h2⟩ : Fin 4725) : ℕ) := h
  exact ⟨h1, h2, Models.decomp_unique h'⟩

open Models in
theorem cCoef_fusion (i : Fin 4725) : cCoef i fusionModel = if fusionBit i then 1 else 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := decomp_fusion i
  obtain ⟨-, hs, -⟩ := outerCheck_parts.2.2.2.2.2.1 i i.isLt
  obtain ⟨-, hs', -⟩ := outerCheck_parts.2.2.2.2.2.1 fusionI[(i : ℕ)]! h2
  have hsi : (elt aCoefT[(i : ℕ)]!)⁻¹ = elt (invIdx aCoefT[(i : ℕ)]!) := (elt_inv hs).2
  have hsi' : invIdx aCoefT[(i : ℕ)]! < 128 := (elt_inv hs).1
  have hbp := betaIdx_lt h1
  obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := invIdx aCoefT[(i : ℕ)]!) hbp
  rw [cCoef, cMul, h3, h4]
  simp only [CocExt.mul_e, CocExt.mul_g, CocExt.inv_e, CocExt.inv_g, tauR_e, tauR_g, aRf,
    aElt, fNorm_toFun, zero_add, add_zero]
  rw [hsi, betaS_elt h1, ← hm2, fCoc, tbl_elt _ hsi' hs, tbl_elt _ hsi' hbp,
    tbl_elt _ hm1 hs', lamCoch, mk1_elt _ h1]
  have hc : fusionBit i = (bitAt fRows (invIdx aCoefT[(i : ℕ)]!) aCoefT[(i : ℕ)]! ^^
      maskBit lamMask fusionP[(i : ℕ)]! ^^
      bitAt fRows (invIdx aCoefT[(i : ℕ)]!) (betaIdx fusionP[(i : ℕ)]!) ^^
      bitAt fRows (mulIdx (invIdx aCoefT[(i : ℕ)]!) (betaIdx fusionP[(i : ℕ)]!))
        aCoefT[fusionI[(i : ℕ)]!]!) := by
    rw [fusionBit, invTab_get hs, betaTab_get h1, mulTab_get hsi' hbp]
    rfl
  rw [hc]
  cases bitAt fRows (invIdx aCoefT[(i : ℕ)]!) aCoefT[(i : ℕ)]! <;>
    cases maskBit lamMask fusionP[(i : ℕ)]! <;>
    cases bitAt fRows (invIdx aCoefT[(i : ℕ)]!) (betaIdx fusionP[(i : ℕ)]!) <;>
    cases bitAt fRows (mulIdx (invIdx aCoefT[(i : ℕ)]!) (betaIdx fusionP[(i : ℕ)]!))
      aCoefT[fusionI[(i : ℕ)]!]! <;>
    decide

theorem bigLam_fusion : Models.bigLam fusionModel = 1 := by
  rw [Models.bigLam, Finset.sum_congr rfl fun i _ => cCoef_fusion i,
    Models.sum_ite_xorFold (fun n => fusionBit n) 4725, lamCheck_parts.2]
  rfl

end CFSG.ComponentClassification.J2Cover.External
