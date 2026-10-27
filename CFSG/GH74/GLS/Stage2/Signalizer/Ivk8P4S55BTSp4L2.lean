module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4M
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherFormZero
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open scoped commutatorElement

section Central

variable {G : Type*} [Group G]

theorem commutator_central_left {s : G} (hs : s ∈ center G) (x w : G) :
    ⁅s * x, w⁆ = ⁅x, w⁆ := by
  have h := Subgroup.mem_center_iff.mp hs
  rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev]
  calc s * x * w * (x⁻¹ * s⁻¹) * w⁻¹ = (s * (x * w * x⁻¹)) * s⁻¹ * w⁻¹ := by group
    _ = ((x * w * x⁻¹) * s) * s⁻¹ * w⁻¹ := by rw [h]
    _ = x * w * x⁻¹ * w⁻¹ := by group

theorem commutator_central_right {t : G} (ht : t ∈ center G) (x y : G) :
    ⁅x, t * y⁆ = ⁅x, y⁆ := by
  have h := Subgroup.mem_center_iff.mp ht
  rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev]
  calc x * (t * y) * x⁻¹ * (y⁻¹ * t⁻¹) = (x * t) * (y * x⁻¹ * y⁻¹) * t⁻¹ := by group
    _ = (t * x) * (y * x⁻¹ * y⁻¹) * t⁻¹ := by rw [h]
    _ = t * (x * y * x⁻¹ * y⁻¹) * t⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * t * t⁻¹ := by rw [h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem conj_commutator_of_central {a x y s t : G} (hs : s ∈ center G) (ht : t ∈ center G)
    (hx : a * x * a⁻¹ = s * x) (hy : a * y * a⁻¹ = t * y) : a * ⁅x, y⁆ * a⁻¹ = ⁅x, y⁆ := by
  have h1 : a * ⁅x, y⁆ * a⁻¹ = ⁅a * x * a⁻¹, a * y * a⁻¹⁆ := by
    rw [← MulAut.conj_apply, map_commutatorElement, MulAut.conj_apply, MulAut.conj_apply]
  rw [h1, hx, hy, commutator_central_left hs, commutator_central_right ht]

end Central

variable {F : Type} [Field F]

@[expose] def kerP : Subgroup (StatedSp 2 F) where
  carrier := {x | (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0 ∧
    (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = 1}
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> ext i j <;>
      simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.one_apply]
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · rw [Subgroup.coe_mul, Units.val_mul]
      exact ll_mul hx1 hy1
    · rw [Subgroup.coe_mul, Units.val_mul, ul_mul hy1, hx2, hy2, Matrix.one_mul]
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    set M := (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hM
    set N := ((((x⁻¹ : StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hN
    have hT : M.toBlocks₂₂ = 1 := by
      have := ul_transpose_mul_lr (μ := 1) hx1 (by
        rw [one_smul]; exact SymplecticTorusWeyl.mem_statedSp_iff.mp x.2)
      rwa [hx2, transpose_one, Matrix.one_mul, one_smul] at this
    have hMN : M * N = 1 := by
      rw [hM, hN, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        Units.val_one]
    obtain ⟨Q, hQ⟩ : ∃ Q, M.toBlocks₁₂ = Q := ⟨_, rfl⟩
    have hA : M = fromBlocks 1 Q 0 1 := by
      conv_lhs => rw [← fromBlocks_toBlocks M]
      rw [hx1, hx2, hT, hQ]
    have hMX : M * fromBlocks 1 (-Q) 0 1 = 1 := by
      rw [hA, fromBlocks_multiply, ← fromBlocks_one]
      simp
    have hNM : N * M = 1 := mul_eq_one_comm.mp hMN
    have hNeq : N = fromBlocks 1 (-Q) 0 1 := by
      calc N = N * (M * fromBlocks 1 (-Q) 0 1) := by rw [hMX, Matrix.mul_one]
        _ = fromBlocks 1 (-Q) 0 1 := by rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]
    refine ⟨?_, ?_⟩
    · rw [← hN, hNeq, toBlocks_fromBlocks₂₁]
    · rw [← hN, hNeq, toBlocks_fromBlocks₁₁]

theorem kerP_eq {x : StatedSp 2 F} (hx : x ∈ kerP) :
    (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks 1 (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₂ 0 1 := by
  obtain ⟨hx1, hx2⟩ := hx
  have hT := ul_transpose_mul_lr (μ := 1) hx1 (by
    rw [one_smul]; exact SymplecticTorusWeyl.mem_statedSp_iff.mp x.2)
  rw [hx2, transpose_one, Matrix.one_mul, one_smul] at hT
  conv_lhs => rw [← fromBlocks_toBlocks (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)]
  rw [hx1, hx2, hT]

theorem kerP_comm {x y : StatedSp 2 F} (hx : x ∈ kerP) (hy : y ∈ kerP) : x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, kerP_eq hx, kerP_eq hy,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add]
  rw [add_comm]

theorem commutator_kerP_eq_bot :
    ⁅(kerP : Subgroup (StatedSp 2 F)), (kerP : Subgroup (StatedSp 2 F))⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact kerP_comm hy hx

theorem ul_inv {x : StatedSp 2 F}
    (hxi : ((((x⁻¹ : StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₂₁ = 0) :
    (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ *
    ((((x⁻¹ : StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁ = 1 := by
  rw [← ul_mul hxi, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
    Units.val_one]
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
