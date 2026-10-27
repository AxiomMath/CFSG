module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCReduce

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

theorem coe_T1' : (((T1 K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron 1 (diag2 1 (-1)) := by
  rw [coe_T1]
  simp only [blk, kron, diag2]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem u1_mul_u1 : u1 K * u1 K = 1 := by
  rw [u1, ← map_mul, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
  left
  rw [Subgroup.coe_mul, Units.val_mul, coe_T1', kron_mul, Matrix.one_mul, diag2_mul]
  simp [diag2]
  rw [← kron_one_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem u2_mul_u1 : u2 K * u1 K = u1 K * u2 K := by
  rw [u2, u1, ← map_mul, ← map_mul]
  apply proj_eq_of_eq_or_neg
  right
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_T2, coe_T1',
    kron_mul, kron_mul, Matrix.one_mul, ← kron_neg_right]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J₁, diag2]

theorem u1_commute_Lsub {l : StatedProj (StatedSp 2 K)} (hl : l ∈ Lsub K) :
    u1 K * l = l * u1 K := by
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hl
  rw [u1, ← map_mul, ← map_mul]
  congr 1
  apply sp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_T1', coe_diagSL,
    kron_mul, kron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]

theorem kron_eq_blk (k : Matrix (Fin 2) (Fin 2) K) : kron k 1 = blk k k := by
  simp only [kron, blk, diag2]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem Lsub_le_E1_sup_E2 : Lsub K ≤ E1 K ⊔ E2 K := by
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  have : proj 2 K (diagSL K k) = proj 2 K (blkSL K (k, 1)) * proj 2 K (blkSL K (1, k)) := by
    rw [← map_mul (proj 2 K)]
    congr 1
    apply sp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_diagSL, coe_blkSL, coe_blkSL, kron_eq_blk,
      blk_mul]
    simp
  rw [this]
  exact mul_mem (mem_sup_left (mem_E1.mpr ⟨k, rfl⟩)) (mem_sup_right (mem_E2.mpr ⟨k, rfl⟩))

theorem T2_mul_blk (g h : Matrix (Fin 2) (Fin 2) K) :
    kron 1 J₁ * blk g h = blk h g * kron 1 J₁ := by
  simp only [kron, blk, diag2, J₁, fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem u2_conj_blkSL (x : Matrix.SpecialLinearGroup (Fin 2) K ×
    Matrix.SpecialLinearGroup (Fin 2) K) :
    u2 K * proj 2 K (blkSL K x) * (u2 K)⁻¹ = proj 2 K (blkSL K (x.2, x.1)) := by
  rw [u2, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply sp_ext
  have h1 : T2 K * blkSL K x = blkSL K (x.2, x.1) * T2 K := sp_ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_T2, coe_blkSL,
      coe_blkSL, T2_mul_blk])
  rw [h1, mul_inv_cancel_right]

theorem E2_le_map_E1 : E2 K ≤ (E1 K).map (MulAut.conj (u2 K)).toMonoidHom := by
  intro y hy
  obtain ⟨h, rfl⟩ := mem_E2.mp hy
  refine ⟨proj 2 K (blkSL K (h, 1)), mem_E1.mpr ⟨h, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [u2_conj_blkSL]

theorem map_E1_ne : (E1 K).map (MulAut.conj (u2 K)).toMonoidHom ≠ E1 K := by
  intro h
  set g : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  have hy : proj 2 K (blkSL K (1, g)) ∈ E1 K := h ▸ E2_le_map_E1 (mem_E2.mpr ⟨g, rfl⟩)
  obtain ⟨g', hg'⟩ := mem_E1.mp hy
  rcases eq_or_eq_neg_of_proj_eq hg' with e | e <;>
    simp only [coe_blkSL, Matrix.SpecialLinearGroup.coe_one] at e
  · obtain ⟨-, e2⟩ := blk_injective _ _ _ _ e
    have := congrFun (congrFun e2 0) 1
    simp [g] at this
  · rw [blk_neg] at e
    obtain ⟨-, e2⟩ := blk_injective _ _ _ _ e
    have := congrFun (congrFun e2 0) 1
    simp [g] at this

theorem E1_le_centralizer_u1 (h2 : (2 : K) ≠ 0) : E1 K ≤ centralizer {u1 K} :=
  (E1_le_X0 h2).trans X0_le_centralizer

theorem isComponent_E1 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    IsComponent ((E1 K).subgroupOf (centralizer {u1 K})) := by
  have hE := E1_le_centralizer_u1 h2
  have hX : X0 K ≤ centralizer {u1 K} := X0_le_centralizer
  refine ⟨(isQuasisimple_congr (subgroupOfEquivOfLe hE)).mpr (isQuasisimple_E1 h2 h4), ?_⟩
  have hXn : ((X0 K).subgroupOf (centralizer {u1 K})).Normal := by
    rw [normal_subgroupOf_iff hX]
    intro x c hx hc
    exact conj_mem_map_centralizer (T1 K) hc hx
  have hEX : (E1 K).subgroupOf (centralizer {u1 K}) ≤ (X0 K).subgroupOf (centralizer {u1 K}) :=
    fun x hx => E1_le_X0 h2 hx
  refine IsSubnormal.trans hEX ?_ hXn.isSubnormal
  apply Normal.isSubnormal
  rw [normal_subgroupOf_iff hEX]
  intro x c hx hc
  exact conj_mem_E1 h2 hc hx

theorem tcWitness_u2 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    TCWitness (MulAut.conj (u2 K)) (Lsub K) := by
  refine ⟨u1 K, u1_mul_u1, u1_ne_one h2, ?_, fun j hj => u1_commute_Lsub hj, E1 K,
    E1_le_centralizer_u1 h2, isComponent_E1 h2 h4, map_E1_ne, ?_⟩
  · rw [MulAut.conj_apply, u2_mul_u1, mul_inv_cancel_right]
  · exact Lsub_le_E1_sup_E2.trans (sup_le_sup_left E2_le_map_E1 _)

end CFSG.ComponentClassification.CatFactsSp4
