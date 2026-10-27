module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41E8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR10E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41U
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ14G

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

theorem fzc_ns_ph14 {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : FzCCtx G t L S x₁ x₂ lam rho) (hA : CorAStatement)
    (hV : 2 ∣ (l41V S t x₁ x₂).index) : L41GPh14 t L S x₁ x₂ lam rho := by
  have p0 : L41GCtx t L S x₁ x₂ lam rho := ⟨h.ctx, h.eq_PL⟩
  have p1 : L41GPh1 t L S x₁ x₂ lam rho := ⟨p0, S4A.l41_basic_of p0⟩
  have p2 : L41GPh2 t L S x₁ x₂ lam rho := ⟨p1, S4A.l41_sylow_of p1 h.ass⟩
  have p3 : L41GPh3 t L S x₁ x₂ lam rho := ⟨p2, S4A.l41_fusion_of p2⟩
  have p4 : L41GPh4 t L S x₁ x₂ lam rho := ⟨p3, S4A.l41_normalizer_of p3 hV⟩
  have p5 : L41GPh5 t L S x₁ x₂ lam rho := ⟨p4, S4A.l41_p2_of p4⟩
  have p6 : L41GPh6 t L S x₁ x₂ lam rho := ⟨p5, S4A.l41_e8_of p5 (hA G h.ass)⟩
  have p7 : L41GPh7 t L S x₁ x₂ lam rho := ⟨p6, S4A.l41_nbar_of p6⟩
  have p8 : L41GPh8 t L S x₁ x₂ lam rho := ⟨p7, S4A.l41_r_of p7⟩
  have p9 : L41GPh9 t L S x₁ x₂ lam rho := ⟨p8, S4A.l41_hs29_of p8⟩
  have p10 : L41GPh10 t L S x₁ x₂ lam rho := ⟨p9, S4A.l41_rabelian_of p9⟩
  have p11 : L41GPh11 t L S x₁ x₂ lam rho := ⟨p10, S4A.l41_y_of p10⟩
  have p12 : L41GPh12 t L S x₁ x₂ lam rho := ⟨p11, S4A.l41_uy_of p11⟩
  have p13 : L41GPh13 t L S x₁ x₂ lam rho := ⟨p12, S4A.l41_mbasic_of p12⟩
  exact ⟨p13, S4A.l41_q_of p13⟩

end CFSG.OddStandard.SmallF3.FritzII
