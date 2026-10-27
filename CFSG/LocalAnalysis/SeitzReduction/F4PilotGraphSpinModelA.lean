module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinFinalA3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelGen

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.Timmesfeld.LieEmbed (a5Root)

local instance f4PilotGraphSpinModelANeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Iota

variable {K : Type} [Field K]

theorem sp6ToSL6_x_single_two (c : K) :
    sp6ToSL6 (Sp.x 3 K (Pi.single 2 1) c) =
      SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 5 by decide) c := by
  apply Subtype.ext
  rw [coe_sp6ToSL6, mat_sp_x_single_two, SpecialLinearGroup.transvection_coe, map_add, map_one,
    map_smul, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_single_equiv,
    smul_single, smul_eq_mul, mul_one]
  rfl

theorem sp6ToSL6_x_neg_single_two (c : K) :
    sp6ToSL6 (Sp.x 3 K (-Pi.single 2 1) c) =
      SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 2 by decide) c := by
  apply Subtype.ext
  rw [coe_sp6ToSL6, mat_sp_x_neg_single_two, SpecialLinearGroup.transvection_coe, map_add,
    map_one, map_smul, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_single_equiv, smul_single, smul_eq_mul, mul_one]
  rfl

theorem sp6ToSL6_x_single_one (c : K) :
    sp6ToSL6 (Sp.x 3 K (Pi.single 1 1) c) =
      SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 2 by decide) c *
        SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) (-c) := by
  apply Subtype.ext
  change _ = (SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 2 by decide) c :
      Matrix (Fin 6) (Fin 6) K) *
    (SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) (-c) :
      Matrix (Fin 6) (Fin 6) K)
  rw [coe_sp6ToSL6, mat_sp_x_single_one,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, map_add, map_one,
    map_smul, map_sub, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_single_equiv, Matrix.submatrix_single_equiv]
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    single_mul_single_of_ne (h := (by decide : (2 : Fin 6) ≠ 5)), add_zero]
  simp only [smul_sub, smul_single, smul_eq_mul, mul_one, Equiv.symm_symm]
  change (1 : Matrix (Fin 6) (Fin 6) K) + (single 1 2 c - single 5 4 c) =
    1 + single 5 4 (-c) + single 1 2 c
  rw [← single_neg]
  abel

theorem sp6ToSL6_x_neg_single_one (c : K) :
    sp6ToSL6 (Sp.x 3 K (-Pi.single 1 1) c) =
      SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 1 by decide) c *
        SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) (-c) := by
  apply Subtype.ext
  change _ = (SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 1 by decide) c :
      Matrix (Fin 6) (Fin 6) K) *
    (SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) (-c) :
      Matrix (Fin 6) (Fin 6) K)
  rw [coe_sp6ToSL6, mat_sp_x_neg_single_one,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, map_add, map_one,
    map_smul, map_sub, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_single_equiv, Matrix.submatrix_single_equiv]
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    single_mul_single_of_ne (h := (by decide : (1 : Fin 6) ≠ 4)), add_zero]
  simp only [smul_sub, smul_single, smul_eq_mul, mul_one, Equiv.symm_symm]
  change (1 : Matrix (Fin 6) (Fin 6) K) + (single 2 1 c - single 4 5 c) =
    1 + single 4 5 (-c) + single 2 1 c
  rw [← single_neg]
  abel

end Iota

section Theta


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem a5Root_graphSwapPerm_check :
    a5Root (graphSwapPerm.symm 2) (graphSwapPerm.symm 5) = Pi.single 3 1 ∧
      a5Root (graphSwapPerm.symm 5) (graphSwapPerm.symm 2) = -Pi.single 3 1 ∧
      a5Root (graphSwapPerm.symm 1) (graphSwapPerm.symm 2) = Pi.single 2 1 ∧
      a5Root (graphSwapPerm.symm 5) (graphSwapPerm.symm 4) = Pi.single 4 1 ∧
      a5Root (graphSwapPerm.symm 2) (graphSwapPerm.symm 1) = -Pi.single 2 1 ∧
      a5Root (graphSwapPerm.symm 4) (graphSwapPerm.symm 5) = -Pi.single 4 1 := by
  decide +kernel

theorem graphParamHom_sp6ToSL6_x_single_two (c : K) :
    graphParamHom K (RingEquiv.refl K) (sp6ToSL6 (Sp.x 3 K (Pi.single 2 1) c)) =
      e6Data_valid.xm K (Pi.single 3 1) c := by
  rw [sp6ToSL6_x_single_two, graphParamHom_transvection, a5Root_graphSwapPerm_check.1]
  rfl

theorem graphParamHom_sp6ToSL6_x_neg_single_two (c : K) :
    graphParamHom K (RingEquiv.refl K) (sp6ToSL6 (Sp.x 3 K (-Pi.single 2 1) c)) =
      e6Data_valid.xm K (-Pi.single 3 1) c := by
  rw [sp6ToSL6_x_neg_single_two, graphParamHom_transvection, a5Root_graphSwapPerm_check.2.1]
  rfl

theorem graphParamHom_sp6ToSL6_x_single_one (c : K) :
    graphParamHom K (RingEquiv.refl K) (sp6ToSL6 (Sp.x 3 K (Pi.single 1 1) c)) =
      e6Data_valid.xm K (Pi.single 2 1) c * e6Data_valid.xm K (Pi.single 4 1) c := by
  rw [sp6ToSL6_x_single_one, map_mul, graphParamHom_transvection, graphParamHom_transvection,
    a5Root_graphSwapPerm_check.2.2.1, a5Root_graphSwapPerm_check.2.2.2.1]
  change e6Data_valid.xm K (Pi.single 2 1) c * e6Data_valid.xm K (Pi.single 4 1) (-c) = _
  rw [CharTwo.neg_eq c]

theorem graphParamHom_sp6ToSL6_x_neg_single_one (c : K) :
    graphParamHom K (RingEquiv.refl K) (sp6ToSL6 (Sp.x 3 K (-Pi.single 1 1) c)) =
      e6Data_valid.xm K (-Pi.single 2 1) c * e6Data_valid.xm K (-Pi.single 4 1) c := by
  rw [sp6ToSL6_x_neg_single_one, map_mul, graphParamHom_transvection, graphParamHom_transvection,
    a5Root_graphSwapPerm_check.2.2.2.2.1, a5Root_graphSwapPerm_check.2.2.2.2.2]
  change e6Data_valid.xm K (-Pi.single 2 1) c * e6Data_valid.xm K (-Pi.single 4 1) (-c) = _
  rw [CharTwo.neg_eq c]

theorem mem_closure_sp4Gens_of_mem_A3 {s : StatedSp 3 K}
    (hs : graphParamHom K (RingEquiv.refl K) (sp6ToSL6 s) ∈ e6ScLevi K e6A3Nodes) :
    s ∈ closure (sp4Gens K) := by
  rw [e6ScLevi_A3_eq_map_blockSpecialLinear] at hs
  obtain ⟨b, hb, hbs⟩ := hs
  have hb' : b = sp6ToSL6 s := graphParamHom_injective (RingEquiv.refl K) hbs
  subst hb'
  exact mem_closure_sp4Gens_of_sp6ToSL6_mem hb

end Theta

end CFSG.SeitzReduction.F4Pilot
