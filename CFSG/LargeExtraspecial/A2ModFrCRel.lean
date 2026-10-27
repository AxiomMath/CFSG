module

public import CFSG.LargeExtraspecial.A2ModFrCMat
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LargeExtraspecial.A2ModCfg

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrC

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic

variable {k : ℕ} {F : Type} [Field F]

theorem transpose_single_self (i : Fin k) : (single i i (1 : F))ᵀ = single i i 1 :=
  transpose_single i i 1

theorem transpose_single_add (i j : Fin k) :
    (single i j (1 : F) + single j i 1)ᵀ = single i j 1 + single j i 1 := by
  rw [transpose_add, transpose_single, transpose_single, add_comm]

@[expose] noncomputable def longPos (i : Fin k) : StatedSp k F :=
  upper (single i i 1) (transpose_single_self i)

@[expose] noncomputable def longNeg (i : Fin k) : StatedSp k F :=
  lower (single i i 1) (transpose_single_self i)

@[expose] noncomputable def sumPos (i j : Fin k) : StatedSp k F :=
  upper (single i j 1 + single j i 1) (transpose_single_add i j)

@[expose] noncomputable def sumNeg (i j : Fin k) : StatedSp k F :=
  lower (single i j 1 + single j i 1) (transpose_single_add i j)

@[expose] noncomputable def longWeyl (i : Fin k) : StatedSp k F :=
  longPos i * longNeg i * longPos i

@[simp]
theorem mat_longPos (i : Fin k) :
    SpExtras.mat k F (longPos i) = fromBlocks 1 (single i i 1) 0 1 :=
  rfl

@[simp]
theorem mat_longNeg (i : Fin k) :
    SpExtras.mat k F (longNeg i) = fromBlocks 1 0 (single i i 1) 1 :=
  rfl

@[simp]
theorem mat_sumPos (i j : Fin k) :
    SpExtras.mat k F (sumPos i j) = fromBlocks 1 (single i j 1 + single j i 1) 0 1 :=
  rfl

@[simp]
theorem mat_sumNeg (i j : Fin k) :
    SpExtras.mat k F (sumNeg i j) = fromBlocks 1 0 (single i j 1 + single j i 1) 1 :=
  rfl

theorem sumPos_comm (i j : Fin k) : (sumPos i j : StatedSp k F) = sumPos j i :=
  ext_mat (by rw [mat_sumPos, mat_sumPos, add_comm])

theorem sumNeg_comm (i j : Fin k) : (sumNeg i j : StatedSp k F) = sumNeg j i :=
  ext_mat (by rw [mat_sumNeg, mat_sumNeg, add_comm])

theorem single_mul_single_ite {ι : Type*} [DecidableEq ι] [Fintype ι] (i j l m : ι) (a b : F) :
    single i j a * single l m b = if j = l then single i m (a * b) else 0 := by
  split_ifs with h
  · subst h
    exact single_mul_single_same (c := a) i j m b
  · exact single_mul_single_of_ne (c := a) i j l h b

local macro "unit_simp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp [mul_add, add_mul, single_mul_single_ite, fromBlocks_multiply, $hs,*]
  try abel_nf
  try simp [smul_single, ofNat_two_eq_zero, ofNat_three_eq_one, ofNat_four_eq_zero]))

section CharTwo

variable [CharP F 2]

theorem longPos_inv (i : Fin k) : (longPos i : StatedSp k F)⁻¹ = longPos i :=
  upper_inv _

theorem mat_longWeyl (m : Fin k) :
    SpExtras.mat k F (longWeyl m) =
      fromBlocks (1 + single m m 1) (single m m 1) (single m m 1) (1 + single m m 1) := by
  rw [longWeyl, map_mul, map_mul, mat_longPos, mat_longNeg]
  unit_simp []

theorem longWeyl_mul_self (m : Fin k) : (longWeyl m : StatedSp k F) * longWeyl m = 1 := by
  refine ext_mat ?_
  rw [map_mul, mat_longWeyl, map_one, ← fromBlocks_one]
  unit_simp []

theorem longWeyl_inv (m : Fin k) : (longWeyl m : StatedSp k F)⁻¹ = longWeyl m :=
  inv_eq_of_mul_eq_one_right (longWeyl_mul_self m)

theorem commute_longWeyl_levZ {i j m : Fin k} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m) :
    Commute (longWeyl m : StatedSp k F) (levZ (elemTv i j)) := by
  refine ext_mat ?_
  rw [map_mul, map_mul, mat_longWeyl, mat_levZ_elemTv hij]
  unit_simp [him, hjm, him.symm, hjm.symm]

theorem longWeyl_conj_levZ_left {i m : Fin k} (him : i ≠ m) :
    longWeyl m * levZ (elemTv i m) * (longWeyl m)⁻¹ = (sumPos i m : StatedSp k F) := by
  rw [longWeyl_inv]
  refine ext_mat ?_
  rw [map_mul, map_mul, mat_longWeyl, mat_levZ_elemTv him, mat_sumPos]
  unit_simp [him, him.symm]

theorem longWeyl_conj_levZ_right {i m : Fin k} (him : i ≠ m) :
    longWeyl m * levZ (elemTv m i) * (longWeyl m)⁻¹ = (sumNeg i m : StatedSp k F) := by
  rw [longWeyl_inv]
  refine ext_mat ?_
  rw [map_mul, map_mul, mat_longWeyl, mat_levZ_elemTv him.symm, mat_sumNeg]
  unit_simp [him, him.symm]

theorem commute_longPos_levZ {i j m : Fin k} (hij : i ≠ j) (hjm : j ≠ m) :
    Commute (longPos m : StatedSp k F) (levZ (elemTv i j)) := by
  refine ext_mat ?_
  rw [map_mul, map_mul, mat_longPos, mat_levZ_elemTv hij]
  unit_simp [hjm, hjm.symm]

theorem longPos_conj_levZ {i m : Fin k} (him : i ≠ m) :
    longPos m * levZ (elemTv i m) * (longPos m)⁻¹ =
      (levZ (elemTv i m) * sumPos i m * longPos i : StatedSp k F) := by
  rw [longPos_inv]
  refine ext_mat ?_
  rw [map_mul, map_mul, map_mul, map_mul, mat_longPos, mat_levZ_elemTv him, mat_sumPos,
    mat_longPos]
  unit_simp [him, him.symm]

theorem longPos_conj_sumNeg {i m : Fin k} (him : i ≠ m) :
    longPos m * sumNeg i m * (longPos m)⁻¹ =
      (levZ (elemTv m i) * sumNeg i m * longNeg i : StatedSp k F) := by
  rw [longPos_inv]
  refine ext_mat ?_
  rw [map_mul, map_mul, map_mul, map_mul, mat_longPos, mat_sumNeg, mat_levZ_elemTv him.symm,
    mat_longNeg]
  unit_simp [him, him.symm]

theorem commute_sumPos_levZ {i j p m : Fin k} (hij : i ≠ j) (hpm : p ≠ m)
    (h₁ : j = p → i = m) (h₂ : j = m → i = p) :
    Commute (sumPos p m : StatedSp k F) (levZ (elemTv i j)) := by
  refine ext_mat ?_
  rw [map_mul, map_mul, mat_sumPos, mat_levZ_elemTv hij]
  rcases eq_or_ne j p with rfl | hjp
  · obtain rfl := h₁ rfl
    unit_simp [hpm, hpm.symm]
  rcases eq_or_ne j m with rfl | hjm
  · obtain rfl := h₂ rfl
    unit_simp [hpm, hpm.symm]
  unit_simp [hjp, hjm, hjp.symm, hjm.symm]

theorem commute_sumNeg_levZ {i j p m : Fin k} (hij : i ≠ j) (hpm : p ≠ m)
    (h₁ : i = p → j = m) (h₂ : i = m → j = p) :
    Commute (sumNeg p m : StatedSp k F) (levZ (elemTv i j)) := by
  refine ext_mat ?_
  rw [map_mul, map_mul, mat_sumNeg, mat_levZ_elemTv hij]
  rcases eq_or_ne i p with rfl | hip
  · obtain rfl := h₁ rfl
    unit_simp [hpm, hpm.symm]
  rcases eq_or_ne i m with rfl | him
  · obtain rfl := h₂ rfl
    unit_simp [hpm, hpm.symm]
  unit_simp [hip, him, hip.symm, him.symm]

end CharTwo

end CFSG.LargeExtraspecial.A2Mod.FrC
