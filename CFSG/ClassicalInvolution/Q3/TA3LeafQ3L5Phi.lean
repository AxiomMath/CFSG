module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5T1

public noncomputable section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q3L5

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem det_ne_zero_of_gl (A : GL (Fin 2) (ZMod 3)) : (A : Mat 2).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact Units.ne_zero _

@[expose] def φFun (A : GL (Fin 2) (ZMod 3)) : SL(2 + 3, ZMod 3) :=
  ⟨diagBlock (A : Mat 2) ((A : Mat 2).det • (1 : Mat 3)), by
    rw [CFSG.GH74.Filter.ClassicalOdd.det_diagBlock, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin]
    exact (by decide : ∀ d : ZMod 3, d ≠ 0 → d * d ^ 3 = 1) _ (det_ne_zero_of_gl A)⟩

theorem coe_φFun (A : GL (Fin 2) (ZMod 3)) :
    ((φFun A : SL(2 + 3, ZMod 3)) : Mat (2 + 3)) =
      diagBlock (A : Mat 2) ((A : Mat 2).det • (1 : Mat 3)) :=
  rfl

@[expose] def φ : GL (Fin 2) (ZMod 3) →* SL(2 + 3, ZMod 3) where
  toFun := φFun
  map_one' := sl_ext (by
    rw [coe_φFun, Units.val_one, Matrix.det_one, one_smul, Matrix.SpecialLinearGroup.coe_one]
    exact diagBlock_one)
  map_mul' A B := sl_ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_φFun, coe_φFun, coe_φFun, diagBlock_mul,
      Units.val_mul, Matrix.det_mul, smul_mul_smul_comm, mul_one])

theorem coe_φ (A : GL (Fin 2) (ZMod 3)) :
    ((φ A : SL(2 + 3, ZMod 3)) : Mat (2 + 3)) =
      diagBlock (A : Mat 2) ((A : Mat 2).det • (1 : Mat 3)) :=
  rfl

theorem φ_injective : Function.Injective φ := fun A B h => by
  have := congrArg (fun g : SL(2 + 3, ZMod 3) => p₁ (k := 2) (m := 3) (g : Mat (2 + 3))) h
  simp only [coe_φ, p₁_diagBlock] at this
  exact Units.ext this

theorem φ_neg_one : φ (-1) = u₁ := sl_ext (by
  rw [coe_φ, coe_u₁, Units.val_neg, Units.val_one, Matrix.det_neg, Matrix.det_one]
  decide)

theorem φ_mem_centralizer_u₁ (A : GL (Fin 2) (ZMod 3)) : φ A ∈ Subgroup.centralizer {u₁} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_φ A, coe_u₁]
  exact diagBlock_comm_neg _ _

theorem φ_mem_centralizer_H₁ (A : GL (Fin 2) (ZMod 3)) :
    φ A ∈ Subgroup.centralizer (H₁ : Set SL(2 + 3, ZMod 3)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨B, rfl⟩
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_φ A, coe_blk₃ B,
    diagBlock_mul, diagBlock_mul, one_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul, mul_one,
    one_mul]

theorem mem_range_φ {g : SL(2 + 3, ZMod 3)} (hg : g ∈ Subgroup.centralizer {u₁})
    (hgH : g ∈ Subgroup.centralizer (H₁ : Set SL(2 + 3, ZMod 3))) : g ∈ φ.range := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hc := comm_of_mem_u₁ hg
  have hB : ∀ X : SL(3, ZMod 3), (X : Mat 3) * p₂ (k := 2) (m := 3) (g : Mat (2 + 3)) =
      p₂ (k := 2) (m := 3) (g : Mat (2 + 3)) * X := by
    intro X
    have hX : ((blk₃ X : SL(2 + 3, ZMod 3)) : Mat (2 + 3)) * diagBlock (k := 2) (m := 3) (-1) 1 =
        diagBlock (k := 2) (m := 3) (-1) 1 * ((blk₃ X : SL(2 + 3, ZMod 3)) : Mat (2 + 3)) := by
      rw [coe_blk₃]
      exact diagBlock_comm_neg _ _
    have := congrArg (fun x : SL(2 + 3, ZMod 3) => p₂ (k := 2) (m := 3) (x : Mat (2 + 3)))
      (Subgroup.mem_centralizer_iff.mp hgH _ ⟨X, rfl⟩)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    rwa [p₂_mul h2 hX hc, p₂_mul h2 hc hX, coe_blk₃, p₂_diagBlock] at this
  obtain ⟨c, hcB⟩ := mem_range_scalar_of_commute_transvectionStruct fun t =>
    hB t.toSpecialLinearGroup
  have hdet := det_eq_p h2 hc
  rw [g.2, ← hcB, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have hcd : c = (p₁ (k := 2) (m := 3) (g : Mat (2 + 3))).det :=
    (by decide : ∀ a c : ZMod 3, 1 = a * c ^ 3 → c = a) _ _ hdet
  have h0 : IsUnit (p₁ (k := 2) (m := 3) (g : Mat (2 + 3))).det :=
    isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hdet.symm)
  let A : GL (Fin 2) (ZMod 3) := ⟨p₁ (k := 2) (m := 3) (g : Mat (2 + 3)),
    (p₁ (k := 2) (m := 3) (g : Mat (2 + 3)))⁻¹, Matrix.mul_nonsing_inv _ h0,
    Matrix.nonsing_inv_mul _ h0⟩
  have key : φ A = g := sl_ext (by
    rw [coe_φ A]
    conv_rhs => rw [eq_diagBlock_p h2 hc, ← hcB, hcd, scalar_apply, ← smul_one_eq_diagonal])
  exact ⟨A, key⟩

theorem range_φ : φ.range =
    Subgroup.centralizer {u₁} ⊓ Subgroup.centralizer (H₁ : Set SL(2 + 3, ZMod 3)) := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    exact ⟨φ_mem_centralizer_u₁ A, φ_mem_centralizer_H₁ A⟩
  · rintro g ⟨hg, hgH⟩
    exact mem_range_φ hg hgH

end CFSG.ClassicalInvolution.Q3.TA3.Q3L5
