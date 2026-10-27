module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41GPh
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AS3Rec

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem l41_basic_of (h : L41GCtx t L S x₁ x₂ lam rho) : L41Basic t S x₁ x₂ lam rho := by
  have hSle : S ≤ twoCore t ⊔ L := by
    rw [← h.eq_PL]
    exact h.le_invCent
  have hS : S = twoCore t ⊔ wreathGrp x₁ x₂ lam := by
    rw [← h.inf_PL]
    exact (inf_eq_left.mpr hSle).symm
  have hlam : lam * lam = 1 := by
    rw [← pow_two, ← h.wreath.ord_lam]
    exact pow_orderOf_eq_one lam
  have h0 : Ctx0 t L S x₁ x₂ lam rho := h.toCtx0
  have hPL : invCent t = twoCore t ⊔ L := h.eq_PL
  subst hS
  exact
    { S_eq := rfl
      card_S := pt_card h0
      normal_W := pt_normalIn_W h0
      index_W := pt_relIndex_W h0
      center_S := pt_center h0
      center_omega := pt_center_omega h0
      deriv_S := pt_deriv h0
      omega_deriv := pt_omega_deriv h0
      A_elem := pt_ctxE_elem h0
      m2_S := pt_m2 h0
      rank_S := pt_rank h0
      normal_elem_le := fun E hE hEe => pt_normal_elem_le h0 hE hEe
      invol_S := pt_invol h0
      norm_S_le := fun n hn => by
        have hn' := CFSG.normalizer_le_normalizer_ambientMaxCardThompson _ hn
        rwa [h0.J0_eq] at hn'
      cent_A := b1_cent_A h0 hPL
      cent_W := b1_cent_W h0 hPL
      norm_A := b1_norm_A h0 hPL
      norm_W := b1_norm_W h0 hPL
      sigma3 := nonempty_closure_mulEquiv_perm_three h0.ord_rho hlam h0.lam_rho }

end S4A

theorem l41_basic_holds : L41BasicStmt :=
  fun h => S4A.l41_basic_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
