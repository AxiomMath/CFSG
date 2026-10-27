module

public import CFSG.ClassicalInvolution.Asc77.AscC25W11

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (mat_longInv_rev)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def negOne (F : Type) [Field F] : StatedSp 2 F :=
  longInv F 2 0 * longInv F 2 1

theorem neg_one_eq_diagonal :
    (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Matrix.diagonal (fun _ => -1) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.neg_apply, Matrix.one_apply_ne h, neg_zero]

theorem mat_negOne : mat 2 F (negOne F) = -1 := by
  rw [negOne, map_mul, mat_longInv, mat_longInv, Matrix.diagonal_mul_diagonal,
    neg_one_eq_diagonal]
  congr 1
  funext a
  rcases a with a | a <;> fin_cases a <;> simp [mem_coords]

theorem negOne_mul_self : negOne F * negOne F = 1 :=
  mat_injective (by rw [map_mul, mat_negOne, map_one]; simp)

theorem negOne_ne_one (h2 : (2 : F) ≠ 0) : negOne F ≠ 1 := by
  intro h
  have e := congrFun (congrFun (congrArg (mat 2 F) h) (Sum.inl 0)) (Sum.inl 0)
  rw [mat_negOne, map_one] at e
  apply h2
  have e' : (-1 : F) = 1 := by simpa using e
  linear_combination -e'

theorem negOne_mem_spScalars : negOne F ∈ spScalars 2 F := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  refine ⟨-1, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, ← mat_apply, mat_negOne, neg_one_eq_diagonal]
  rfl

theorem negOne_mem_center : negOne F ∈ Subgroup.center (StatedSp 2 F) := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq]
  exact negOne_mem_spScalars

theorem negOne_comm (x : StatedSp 2 F) : negOne F * x = x * negOne F :=
  (Subgroup.mem_center_iff.mp negOne_mem_center x).symm

theorem mem_spScalars_iff {x : StatedSp 2 F} : x ∈ spScalars 2 F ↔ x = 1 ∨ x = negOne F := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := C25W.Sp.scalar_of_mem_spScalars hx
    have hs := mat_transpose_mul_gram_mul x
    rw [hc] at hs
    have e := congrFun (congrFun hs (Sum.inl 0)) (Sum.inr 0)
    simp [gram, Matrix.fromBlocks, Matrix.transpose_smul] at e
    rcases mul_self_eq_one_iff.mp (by linear_combination e : c * c = 1) with h | h
    · left
      exact mat_injective (by rw [hc, h, map_one, one_smul])
    · right
      exact mat_injective (by rw [hc, h, mat_negOne, neg_one_smul])
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact negOne_mem_spScalars

theorem longInv_mul_self (k : Fin 2) : longInv F 2 k * longInv F 2 k = 1 := by
  rw [longInv, ← map_mul]
  have : (-1 : SL(2, F)) * (-1) = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, map_one]

theorem rev_zero : Fin.rev (0 : Fin 2) = 1 := rfl

theorem rev_ne (k : Fin 2) : k ≠ Fin.rev k := by
  fin_cases k <;> decide

theorem longInv_rev_eq (k : Fin 2) : longInv F 2 (Fin.rev k) = negOne F * longInv F 2 k :=
  mat_injective (by
    rw [map_mul, mat_negOne, mat_longInv_rev, neg_one_mul])

theorem coords_compl_eq (k : Fin 2) : (coords k)ᶜ = coords (Fin.rev k) := by
  ext a
  simp only [Set.mem_compl_iff, mem_coords]
  rcases a with a | a <;> fin_cases k <;> fin_cases a <;> simp

theorem complGroup_longInv_two (h2 : (2 : F) ≠ 0) (k : Fin 2) :
    complGroup (longInv F 2 k) = longRootSp2 F 2 (Fin.rev k) := by
  rw [complGroup_longInv h2, coords_compl_eq, longRootSp2_eq_suppGroup]

theorem disjoint_L (k : Fin 2) :
    Disjoint (longRootSp2 F 2 k) (longRootSp2 F 2 (Fin.rev k)) := by
  rw [longRootSp2_eq_suppGroup, longRootSp2_eq_suppGroup, ← coords_compl_eq]
  exact disjoint_suppGroup_compl _

theorem commute_L (k : Fin 2) {x y : StatedSp 2 F} (hx : x ∈ longRootSp2 F 2 k)
    (hy : y ∈ longRootSp2 F 2 (Fin.rev k)) : x * y = y * x :=
  (commute_longRootSp2 (rev_ne k) hx hy).eq

theorem longInv_mem (k : Fin 2) : longInv F 2 k ∈ longRootSp2 F 2 k :=
  longInv_mem_longRootSp2 k

theorem longInv_comm_L (k l : Fin 2) {x : StatedSp 2 F} (hx : x ∈ longRootSp2 F 2 l) :
    longInv F 2 k * x = x * longInv F 2 k := by
  by_cases hkl : k = l
  · subst hkl
    obtain ⟨A, rfl⟩ := hx
    rw [longInv, ← map_mul, ← map_mul]
    congr 1
    rw [neg_one_mul, mul_neg_one]
  · have hl : l = Fin.rev k := by fin_cases k <;> fin_cases l <;> simp_all
    subst hl
    exact commute_L k (longInv_mem k) hx

@[expose] def perm2 (F : Type) [Field F] : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]

@[expose] def swMat (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks (perm2 F) 0 0 (perm2 F)

theorem perm2_mul_self : perm2 F * perm2 F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [perm2]

theorem perm2_transpose : (perm2 F)ᵀ = perm2 F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [perm2]

theorem swMat_symplectic : (swMat F)ᵀ * gram F 2 * swMat F = gram F 2 := by
  rw [swMat, gram, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [perm2_transpose, perm2_mul_self]

@[expose] noncomputable def sw (F : Type) [Field F] : StatedSp 2 F :=
  ofSymplecticMat (swMat F) swMat_symplectic

theorem mat_sw : mat 2 F (sw F) = swMat F := rfl

theorem sw_mul_self : sw F * sw F = 1 :=
  mat_injective (by
    rw [map_mul, mat_sw, map_one, swMat, Matrix.fromBlocks_multiply]
    simp [perm2_mul_self, Matrix.fromBlocks_one])

theorem sw_inv : (sw F)⁻¹ = sw F :=
  inv_eq_of_mul_eq_one_right sw_mul_self

theorem sw_mul_longInv (k : Fin 2) : sw F * longInv F 2 k = longInv F 2 (Fin.rev k) * sw F := by
  apply mat_injective
  rw [map_mul, map_mul, mat_sw, mat_longInv, mat_longInv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    fin_cases k <;>
    simp [swMat, perm2, Matrix.mul_apply, Matrix.diagonal_apply, mem_coords]

theorem sw_conj_longInv (k : Fin 2) :
    sw F * longInv F 2 k * (sw F)⁻¹ = longInv F 2 (Fin.rev k) := by
  rw [sw_mul_longInv, mul_assoc, mul_inv_cancel, mul_one]

theorem map_sw_L (h2 : (2 : F) ≠ 0) (k : Fin 2) :
    (longRootSp2 F 2 k).map (MulAut.conj (sw F)).toMonoidHom = longRootSp2 F 2 (Fin.rev k) := by
  rw [longRootSp2, longRootSp2, range_longBlock_eq_longRootGroup h2,
    range_longBlock_eq_longRootGroup h2, ← longRootGroup_conj, sw_conj_longInv]

end CFSG.ClassicalInvolution.Asc77.C5O.M
