module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5SL
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Fix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5Blk

public noncomputable section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q3L5

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def blk₃Fun (B : SL(3, ZMod 3)) : SL(2 + 3, ZMod 3) :=
  ⟨diagBlock (1 : Mat 2) (B : Mat 3), by
    rw [CFSG.GH74.Filter.ClassicalOdd.det_diagBlock, Matrix.det_one, one_mul, B.2]⟩

theorem coe_blk₃Fun (B : SL(3, ZMod 3)) :
    ((blk₃Fun B : SL(2 + 3, ZMod 3)) : Mat (2 + 3)) = diagBlock (1 : Mat 2) (B : Mat 3) :=
  rfl

@[expose] def blk₃ : SL(3, ZMod 3) →* SL(2 + 3, ZMod 3) where
  toFun := blk₃Fun
  map_one' := sl_ext (by
    rw [coe_blk₃Fun, Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_one]
    exact diagBlock_one)
  map_mul' B C := sl_ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_blk₃Fun, coe_blk₃Fun, coe_blk₃Fun,
      Matrix.SpecialLinearGroup.coe_mul, diagBlock_mul, mul_one])

theorem coe_blk₃ (B : SL(3, ZMod 3)) :
    ((blk₃ B : SL(2 + 3, ZMod 3)) : Mat (2 + 3)) = diagBlock (1 : Mat 2) (B : Mat 3) :=
  rfl

abbrev H₁ : Subgroup SL(2 + 3, ZMod 3) := blk₃.range

theorem blk₃_injective : Function.Injective blk₃ := fun X Y h => by
  have := congrArg (fun g : SL(2 + 3, ZMod 3) => p₂ (k := 2) (m := 3) (g : Mat (2 + 3))) h
  simp only [coe_blk₃, p₂_diagBlock] at this
  exact sl_ext this

theorem comm_of_mem_u₁ {g : SL(2 + 3, ZMod 3)} (hg : g ∈ Subgroup.centralizer {u₁}) :
    (g : Mat (2 + 3)) * diagBlock (k := 2) (m := 3) (-1) 1 =
      diagBlock (k := 2) (m := 3) (-1) 1 * (g : Mat (2 + 3)) := by
  have := congrArg (fun x : SL(2 + 3, ZMod 3) => (x : Mat (2 + 3)))
    (Subgroup.mem_centralizer_singleton_iff.mp hg)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  rw [← coe_u₁]
  exact this

theorem H₁_le : H₁ ≤ Subgroup.centralizer {u₁} := by
  rintro _ ⟨X, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blk₃ X, coe_u₁]
  exact diagBlock_comm_neg (1 : Mat 2) (X : Mat 3)

instance isPerfect_H₁ : Group.IsPerfect H₁ :=
  have : Group.IsPerfect SL(3, ZMod 3) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl
  Group.IsPerfect.range _

theorem noOddNormal_H₁ : NoOddNormal H₁ := by
  have h := (noOddNormal_top (k := 1) le_rfl).map blk₃ blk₃_injective
  rwa [← MonoidHom.range_eq_map] at h

@[expose] def blkHom₁ (M : Subgroup SL(2 + 3, ZMod 3)) (hM : M ≤ Subgroup.centralizer {u₁}) :
    M →* Mat 2 where
  toFun g := p₁ (k := 2) (m := 3) ((g : SL(2 + 3, ZMod 3)) : Mat (2 + 3))
  map_one' := by
    show p₁ (k := 2) (m := 3) (1 : Mat (2 + 3)) = 1
    rw [← diagBlock_one (K := ZMod 3) (k := 2) (m := 3), p₁_diagBlock]
  map_mul' g h := by
    show p₁ (k := 2) (m := 3) (((g : SL(2 + 3, ZMod 3)) : Mat (2 + 3)) *
      ((h : SL(2 + 3, ZMod 3)) : Mat (2 + 3))) = _
    rw [p₁_mul (by decide) (comm_of_mem_u₁ (hM g.2)) (comm_of_mem_u₁ (hM h.2))]

theorem blkHom₁_apply (M : Subgroup SL(2 + 3, ZMod 3)) (hM : M ≤ Subgroup.centralizer {u₁})
    (g : M) : blkHom₁ M hM g = p₁ (k := 2) (m := 3) ((g : SL(2 + 3, ZMod 3)) : Mat (2 + 3)) :=
  rfl

theorem perfect_le_H₁ (M : Subgroup SL(2 + 3, ZMod 3)) (hM : M ≤ Subgroup.centralizer {u₁})
    (hMp : ⁅M, M⁆ = M) : M ≤ H₁ := by
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.mpr hMp
  have : Group.IsSolvable (GL (Fin 2) (ZMod 3)) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable (ZMod 3)
      (Or.inr (Nat.card_zmod 3))
  let α : M →* GL (Fin 2) (ZMod 3) := (blkHom₁ M hM).toHomUnits
  have hα := eq_one_of_isPerfect_of_isSolvable α
  intro g hg
  have hc := comm_of_mem_u₁ (hM hg)
  have h1 : p₁ (k := 2) (m := 3) (g : Mat (2 + 3)) = 1 := by
    have h := congrArg Units.val (DFunLike.congr_fun hα ⟨g, hg⟩)
    rwa [MonoidHom.one_apply, Units.val_one, MonoidHom.coe_toHomUnits, blkHom₁_apply] at h
  have hdet := det_eq_p (by decide) hc
  rw [h1, Matrix.det_one, one_mul, g.2] at hdet
  have key : blk₃ ⟨p₂ (k := 2) (m := 3) (g : Mat (2 + 3)), hdet.symm⟩ = g := sl_ext (by
    rw [coe_blk₃ ⟨p₂ (k := 2) (m := 3) (g : Mat (2 + 3)), hdet.symm⟩]
    conv_rhs => rw [eq_diagBlock_p (by decide) hc, h1])
  exact ⟨_, key⟩

end CFSG.ClassicalInvolution.Q3.TA3.Q3L5
