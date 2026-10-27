module

public import CFSG.GH74.Generic.S3.Prop21
public import CFSG.GH74.Generic.S3.SL2Out
public import CFSG.GH74.Generic.S3.Lem26Z
public import CFSG.GH74.Generic.S3.Comps24Proof
public import CFSG.GH74.Generic.S3.V1InnerUni

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

theorem b_S3_prop21_of_griess (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    B_S3_prop21_lin ∧ B_S3_prop21_uni := by
  have hcov : B_L3_cover := b_L3_cover_of_griess hGA
  have hJ : B_S3_J_contain := b_S3_J_contain_of_in_Iw b_S3_J_in_Iw
  have hsl3l : B_S3_sl3pair_lin := b_S3_sl3pair_lin_of_cover hcov hJ
  have hsl3u : B_S3_sl3pair_uni := b_S3_sl3pair_uni_of_cover hcov hJ
  have hlay : B_S3_layers := b_S3_layers_of_cover hcov
  have hcomps : B_S3_comps24 := b_S3_comps24_of_cover hcov
  have h2425 : B_S3_lemma24_25 := b_S3_lemma24_25_of_comps hcov hcomps
  have hv₁ : B_S3_lemma22_v1 :=
    b_S3_lemma22_v1_of_inner (b_S3_v1_inner_of_neg (b_S3_v1_inner_neg_of_uni b_S3_v1_inner_neg_uni))
  have htr : B_S3_lemma26_transfer := b_S3_lemma26_transfer_of_sylow b_L3_sylow
  exact ⟨b_S3_prop21_lin_of_leaves hv₁ b_L3_fourgroup hlay hsl3l h2425 b_SL2_outAbelian htr,
    b_S3_prop21_uni_of_leaves hv₁ b_L3_fourgroup hlay hsl3u h2425 b_SL2_outAbelian htr⟩

end CFSG.GH74.Generic.S3
