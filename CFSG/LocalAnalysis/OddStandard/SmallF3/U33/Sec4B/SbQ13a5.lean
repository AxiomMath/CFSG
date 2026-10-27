module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a4b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

theorem q13a_famA : Q13FamA := by
  intro G _ _ t L S x₁ x₂ lam rho tau hq
  obtain ⟨om, hom⟩ := q13a_exists_om hq
  refine ⟨om, ?_⟩
  exact
    { om_sq := by rw [pow_two]; exact hom.om_sq
      om_not_mem := hom.om_not_mem
      t_om := hom.t_om
      CO_eq := hom.CO_eq
      X_om := q13a_X_om hom
      U_eq := q13a_U_eq hom
      Q_comm := q13a_Q_comm hom
      Q_fpf := fun g hg hgr => l12_cent_Q_rho hq.c11 g hg hgr.symm
      CQt_ne := q13a_CQt_ne hom
      CQt_om := q13a_CQt_om hom
      tauQ := q13a_tauQ hom
      card_A := q13a_card_A hom
      V_le_A := q13a_V_le_A hom
      A_iso := q13a_A_iso hom
      A_inv := q13a_A_inv hom
      t_inv_A := q13a_t_inv_A hom
      A_dich := q13a_A_dich hom
      lam_om := q13a_lam_om hom
      card_CQ_tlam := q13a_card_CQ_tlam hom
      card_CA_tlam := q13a_card_CA_tlam hom }

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
