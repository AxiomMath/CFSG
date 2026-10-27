module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFourModel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp coe_leviSp)
open CFSG.AGLEmbedding.KlingenSpFour

section Matrix

variable {F : Type} [Field F]

@[expose] def L2 (s : F) : Matrix (Fin 2) (Fin 2) F := !![1, 0; s, 1]

theorem L2_det (s : F) : (L2 s).det = 1 := by simp [L2, Matrix.det_fin_two]

theorem L2_isUnit (s : F) : IsUnit (L2 s).det := by rw [L2_det]; exact isUnit_one

@[expose] noncomputable def gA (s : F) : GL (Fin 2) F := nonsingInvUnit (A2 s) (A2_isUnit s)

@[expose] noncomputable def gL (s : F) : GL (Fin 2) F := nonsingInvUnit (L2 s) (L2_isUnit s)

theorem coe_gA (s : F) : ((gA s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = A2 s := rfl

theorem coe_gL (s : F) : ((gL s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = L2 s := rfl

theorem A2_mul_S2_mul_transpose (s a b c : F) :
    A2 s * S2 a b c * (A2 s)ᵀ = S2 (a + 2 * s * b + s ^ 2 * c) (b + s * c) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A2, S2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem L2_mul_S2_mul_transpose (s a b c : F) :
    L2 s * S2 a b c * (L2 s)ᵀ = S2 a (b + s * a) (c + 2 * s * b + s ^ 2 * a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L2, S2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[expose] def leviS2 (M : GL (Fin 2) F) (a b c : F) : Matrix (Fin 2) (Fin 2) F :=
  (M : Matrix (Fin 2) (Fin 2) F) * S2 a b c * (M : Matrix (Fin 2) (Fin 2) F)ᵀ

theorem leviS2_symm (M : GL (Fin 2) F) (a b c : F) : (leviS2 M a b c)ᵀ = leviS2 M a b c := by
  rw [leviS2, transpose_mul, transpose_mul, transpose_transpose, S2_symm, Matrix.mul_assoc]

theorem leviSp_conj_xEl (M : GL (Fin 2) F) (a b c : F) :
    leviSp M * xEl a b c * (leviSp M)⁻¹ =
      xEl (leviS2 M a b c 0 0) (leviS2 M a b c 0 1) (leviS2 M a b c 1 1) := by
  have hAD : (M : Matrix (Fin 2) (Fin 2) F)ᵀ *
      ((M⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ = 1 := by
    rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_xEl, coe_xEl,
    coe_leviSp, ← eq_S2_of_transpose_eq (leviS2_symm M a b c)]
  exact fromBlocks_mul_siegel hAD _

theorem leviSp_conj_xEl_gA (s a b c : F) :
    leviSp (gA s) * xEl a b c * (leviSp (gA s))⁻¹ =
      xEl (a + 2 * s * b + s ^ 2 * c) (b + s * c) c := by
  rw [leviSp_conj_xEl, leviS2, coe_gA, A2_mul_S2_mul_transpose]
  simp [S2]

theorem leviSp_conj_xEl_gL (s a b c : F) :
    leviSp (gL s) * xEl a b c * (leviSp (gL s))⁻¹ =
      xEl a (b + s * a) (c + 2 * s * b + s ^ 2 * a) := by
  rw [leviSp_conj_xEl, leviS2, coe_gL, L2_mul_S2_mul_transpose]
  simp [S2]

end Matrix

section Model

variable (p : ℕ) [Fact p.Prime]

@[expose] noncomputable def xS : XData p (PSp4 p) where
  x a b c := proj 2 (ZMod p) (xEl a b c)
  x_mul a b c a' b' c' := by rw [← map_mul, xEl_mul]
  x_inj a b c a' b' c' h := xEl_inj (proj_injOn_unipotent (by norm_num)
    (xEl_mem_unipotent _ _ _) (xEl_mem_unipotent _ _ _) h)

theorem xS_x (a b c : ZMod p) : (xS p).x a b c = proj 2 (ZMod p) (xEl a b c) := rfl

@[expose] noncomputable def levG : GL (Fin 2) (ZMod p) →* PSp4 p :=
  (proj 2 (ZMod p)).comp leviSp

theorem levG_conj_xS (M : GL (Fin 2) (ZMod p)) (a b c : ZMod p) :
    levG p M * (xS p).x a b c * (levG p M)⁻¹ =
      (xS p).x (leviS2 M a b c 0 0) (leviS2 M a b c 0 1) (leviS2 M a b c 1 1) := by
  simp only [levG, xS_x, MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul, leviSp_conj_xEl]

theorem levG_conj_xS_gA (s a b c : ZMod p) :
    levG p (gA s) * (xS p).x a b c * (levG p (gA s))⁻¹ =
      (xS p).x (a + 2 * s * b + s ^ 2 * c) (b + s * c) c := by
  simp only [levG, xS_x, MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul, leviSp_conj_xEl_gA]

theorem levG_conj_xS_gL (s a b c : ZMod p) :
    levG p (gL s) * (xS p).x a b c * (levG p (gL s))⁻¹ =
      (xS p).x a (b + s * a) (c + 2 * s * b + s ^ 2 * a) := by
  simp only [levG, xS_x, MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul, leviSp_conj_xEl_gL]

theorem levG_conj_mem_U (M : GL (Fin 2) (ZMod p)) {u : PSp4 p} (hu : u ∈ (xS p).U) :
    levG p M * u * (levG p M)⁻¹ ∈ (xS p).U := by
  obtain ⟨a, b, c, rfl⟩ := hu
  rw [levG_conj_xS]
  exact ⟨_, _, _, rfl⟩

theorem levG_mem_normalizer (M : GL (Fin 2) (ZMod p)) :
    levG p M ∈ Subgroup.normalizer ((xS p).U : Set (PSp4 p)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hu => levG_conj_mem_U p M hu, fun hu => ?_⟩
  have h2 := levG_conj_mem_U p M⁻¹ hu
  rw [map_inv, inv_inv] at h2
  have h3 : (levG p M)⁻¹ * (levG p M * h * (levG p M)⁻¹) * levG p M = h := by group
  rwa [h3] at h2

end Model

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
