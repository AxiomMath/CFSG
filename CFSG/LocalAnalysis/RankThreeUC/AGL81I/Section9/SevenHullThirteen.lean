module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThree
import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.SevenHull
public import CFSG.Quasithin.Background.A1cSL2Facts

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix
open scoped MatrixGroups

private theorem matSevenTwo_pow :
    (!![0, -1; 1, 7] : Matrix (Fin 2) (Fin 2) (ZMod 13)) ^ 7 = 1 := by
  decide

private theorem matSevenTwo_det :
    (!![0, -1; 1, 7] : Matrix (Fin 2) (Fin 2) (ZMod 13)).det = 1 := by
  rw [Matrix.det_fin_two_of]
  decide

private theorem matSevenThree_pow :
    (!![0, -1, 0; 1, 7, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 13)) ^ 7 = 1 := by
  decide

private theorem matSevenThree_det :
    (!![0, -1, 0; 1, 7, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 13)).det = 1 := by
  rw [Matrix.det_fin_three]
  decide

private noncomputable def slTwoSeven : SL(2, ZMod 13) := ⟨!![0, -1; 1, 7], matSevenTwo_det⟩

private noncomputable def slThreeSeven : SL(3, ZMod 13) :=
  ⟨!![0, -1, 0; 1, 7, 0; 0, 0, 1], matSevenThree_det⟩

private theorem slTwoSeven_pow : slTwoSeven ^ 7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact matSevenTwo_pow

private theorem slTwoSeven_not_mem_center : slTwoSeven ∉ Subgroup.center SL(2, ZMod 13) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have h := congrFun (congrFun hr 0) 1
  simp [slTwoSeven] at h
  exact absurd h (by decide)

private theorem slThreeSeven_pow : slThreeSeven ^ 7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact matSevenThree_pow

private theorem slThreeSeven_not_mem_center :
    slThreeSeven ∉ Subgroup.center SL(3, ZMod 13) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  have h := congrFun (congrFun hr 0) 1
  simp [slThreeSeven] at h
  exact absurd h (by decide)

theorem oPPrimeHull_seven_sl2_thirteen : oPPrimeHull 7 (⊤ : Subgroup SL(2, ZMod 13)) = ⊤ := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine oPPrimeHull_top_eq_top_of_dichotomy (by norm_num) (fun N hN => ?_) slTwoSeven_pow
    slTwoSeven_not_mem_center
  have := hN
  exact CFSG.Quasithin.A1c.normal_le_center_or_eq_top (by norm_num) N

theorem oPPrimeHull_seven_sl3_thirteen : oPPrimeHull 7 (⊤ : Subgroup SL(3, ZMod 13)) = ⊤ := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact oPPrimeHull_top_eq_top_of_dichotomy (by norm_num)
    (CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.normal_le_center_or_eq_top
      (Group.isPerfect_def.mp
        (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl))
      (CFSG.LinearGroups.linear_projective_simple (by norm_num) (Or.inl le_rfl)).2.1)
    slThreeSeven_pow slThreeSeven_not_mem_center

theorem oPPrimeHull_seven_psl2_thirteen : oPPrimeHull 7 (⊤ : Subgroup PSL(2, ZMod 13)) = ⊤ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h1 := oPPrimeHull_range_eq_of_top (QuotientGroup.mk' (Subgroup.center SL(2, ZMod 13)))
    oPPrimeHull_seven_sl2_thirteen
  rwa [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1

theorem oPPrimeHull_seven_of_sixThreeOneList_thirteen {X : Type} [Group X]
    (h : SixThreeOneList 13 X) (h1 : Nat.card X ≠ 1) : oPPrimeHull 7 (⊤ : Subgroup X) = ⊤ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rcases h with (h | h | h | h) | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Nonempty.elim h fun e =>
      oPPrimeHull_top_eq_top_of_mulEquiv e.symm oPPrimeHull_seven_sl2_thirteen
  · exact Nonempty.elim h fun e =>
      oPPrimeHull_top_eq_top_of_mulEquiv e.symm oPPrimeHull_seven_sl3_thirteen
  · exact Nonempty.elim h fun e =>
      oPPrimeHull_top_eq_top_of_mulEquiv e.symm oPPrimeHull_seven_psl2_thirteen
  · exact absurd h h1
  all_goals exact absurd h (by norm_num)

theorem sq_eq_one_of_mem_center_sl2_thirteen {z : SL(2, ZMod 13)}
    (hz : z ∈ Subgroup.center SL(2, ZMod 13)) : z ^ 2 = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hrz, ← map_pow, hr,
    map_one]

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
