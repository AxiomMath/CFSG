module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscB3C1
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Asc77.B3C
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped Matrix MatrixGroups

section Swap

variable {F : Type} [Field F]

theorem swap_conj_le {k l : Fin 2} (hcompl : ∀ t : Fin 2 ⊕ Fin 2, t ∉ coords l → t ∈ coords k)
    (w : StatedSp 2 F)
    (hw : ∀ r t : Fin 2 ⊕ Fin 2, r ∈ coords k → t ∈ coords k → mat 2 F w⁻¹ r t = 0) :
    ((longBlock F 2 k).range).map (MulAut.conj w).toMonoidHom ≤ (longBlock F 2 l).range := by
  rintro _ ⟨y, hy, rfl⟩
  rw [range_longBlock] at hy ⊢
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [mem_suppGroup_iff (parClosed_coords l)]
  intro t ht r
  have ht1 : t ∈ coords k := hcompl t ht
  have hW1 : mat 2 F w * mat 2 F w⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hY : ∀ u v : Fin 2 ⊕ Fin 2, ¬(u ∈ coords k ∧ v ∈ coords k) →
      mat 2 F y u v = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) u v := hy
  have hYW : ∀ u, (mat 2 F y * mat 2 F w⁻¹) u t = mat 2 F w⁻¹ u t := by
    intro u
    rw [Matrix.mul_apply]
    have h : ∀ v, mat 2 F y u v * mat 2 F w⁻¹ v t =
        (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) u v * mat 2 F w⁻¹ v t := by
      intro v
      by_cases hv : v ∈ coords k
      · rw [hw v t hv ht1, mul_zero, mul_zero]
      · rw [hY u v (fun h => hv h.2)]
    rw [Finset.sum_congr rfl (fun v _ => h v), ← Matrix.mul_apply, Matrix.one_mul]
  rw [map_mul, map_mul, Matrix.mul_assoc, Matrix.mul_apply]
  have h : ∀ u, mat 2 F w r u * (mat 2 F y * mat 2 F w⁻¹) u t = mat 2 F w r u * mat 2 F w⁻¹ u t :=
    fun u => by rw [hYW u]
  rw [Finset.sum_congr rfl (fun u _ => h u), ← Matrix.mul_apply, hW1]

theorem compl_coords_one :
    ∀ t : Fin 2 ⊕ Fin 2, t ∉ coords (0 : Fin 2) → t ∈ coords (1 : Fin 2) := by
  intro t ht
  rcases t with j | j <;> fin_cases j <;> simp [mem_coords] at ht ⊢

theorem compl_coords_zero :
    ∀ t : Fin 2 ⊕ Fin 2, t ∉ coords (1 : Fin 2) → t ∈ coords (0 : Fin 2) := by
  intro t ht
  rcases t with j | j <;> fin_cases j <;> simp [mem_coords] at ht ⊢

@[expose] def PinvMat (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![2⁻¹, 0; 2⁻¹, 0] !![0, -2⁻¹; 0, 2⁻¹] !![0, 1; 0, -1] !![1, 0; 1, 0]

theorem Pmat_mul_PinvMat (h2 : (2 : F) ≠ 0) : Pmat F * PinvMat F = 1 := by
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Pmat, PinvMat, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type]
  all_goals first | ring1 | linear_combination h22

theorem mat_Pel_inv (h2 : (2 : F) ≠ 0) : mat 2 F (Pel h2)⁻¹ = PinvMat F := by
  have h1 : mat 2 F (Pel h2)⁻¹ * Pmat F = 1 := by
    rw [← mat_Pel h2, ← map_mul, inv_mul_cancel, map_one]
  exact left_inv_eq_right_inv h1 (Pmat_mul_PinvMat h2)

theorem mat_twShort (h2 : (2 : F) ≠ 0) (A : SL(2, F)) :
    mat 2 F (twShort h2 A) = PinvMat F * kronMat (A : Matrix (Fin 2) (Fin 2) F) * Pmat F := by
  rw [twShort_apply, map_mul, map_mul, mat_Pel_inv, mat_kron2, mat_Pel]

theorem mat_twShort_vanish (h2 : (2 : F) ≠ 0) (B : SL(2, F))
    (hsym : (B : Matrix (Fin 2) (Fin 2) F) 0 1 = (B : Matrix (Fin 2) (Fin 2) F) 1 0)
    (htr : (B : Matrix (Fin 2) (Fin 2) F) 1 1 = -(B : Matrix (Fin 2) (Fin 2) F) 0 0)
    (k : Fin 2) :
    ∀ r t : Fin 2 ⊕ Fin 2, r ∈ coords k → t ∈ coords k → mat 2 F (twShort h2 B) r t = 0 := by
  intro r t hr ht
  rw [mat_twShort]
  have h22 : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  fin_cases k <;> simp only [mem_coords] at hr ht <;> 
    rcases hr with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp [PinvMat, Pmat, kronMat, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks] <;>
    (try rw [hsym]) <;> (try rw [htr]) <;> ring


theorem inv_symm_trace_zero (B : SL(2, F))
    (hsym : (B : Matrix (Fin 2) (Fin 2) F) 0 1 = (B : Matrix (Fin 2) (Fin 2) F) 1 0)
    (htr : (B : Matrix (Fin 2) (Fin 2) F) 1 1 = -(B : Matrix (Fin 2) (Fin 2) F) 0 0) :
    ((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
        ((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 ∧
      ((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        -((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [hsym, htr]

theorem twShort_swap_eq (h2 : (2 : F) ≠ 0) (B : SL(2, F))
    (hsym : (B : Matrix (Fin 2) (Fin 2) F) 0 1 = (B : Matrix (Fin 2) (Fin 2) F) 1 0)
    (htr : (B : Matrix (Fin 2) (Fin 2) F) 1 1 = -(B : Matrix (Fin 2) (Fin 2) F) 0 0) :
    ((longBlock F 2 1).range).map (MulAut.conj (twShort h2 B)).toMonoidHom =
      (longBlock F 2 0).range := by
  have hBi := inv_symm_trace_zero B hsym htr
  apply le_antisymm
  · refine swap_conj_le (k := 1) (l := 0) compl_coords_one _ ?_
    intro r t hr ht
    rw [← map_inv]
    exact mat_twShort_vanish h2 B⁻¹ hBi.1 hBi.2 1 r t hr ht
  · have h := swap_conj_le (k := 0) (l := 1) compl_coords_zero (twShort h2 B)⁻¹ (by
      intro r t hr ht
      rw [inv_inv]
      exact mat_twShort_vanish h2 B hsym htr 0 r t hr ht)
    intro y hy
    have hy' : (MulAut.conj (twShort h2 B)⁻¹).toMonoidHom y ∈ (longBlock F 2 1).range :=
      h ⟨y, hy, rfl⟩
    refine ⟨_, hy', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

@[expose] def swapMat3 (h3 : (3 : F) = 0) : SL(2, F) :=
  ⟨!![1, 1; 1, -1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * h3⟩

@[expose] noncomputable def swapElt3 (h2 : (2 : F) ≠ 0) (h3 : (3 : F) = 0) : StatedSp 2 F :=
  twShort h2 (swapMat3 h3)

theorem swapElt3_conj (h2 : (2 : F) ≠ 0) (h3 : (3 : F) = 0) :
    ((longBlock F 2 1).range).map (MulAut.conj (swapElt3 h2 h3)).toMonoidHom =
      (longBlock F 2 0).range :=
  twShort_swap_eq h2 (swapMat3 h3) rfl rfl

end Swap

end CFSG.ClassicalInvolution.Q3.Q3T7S23
