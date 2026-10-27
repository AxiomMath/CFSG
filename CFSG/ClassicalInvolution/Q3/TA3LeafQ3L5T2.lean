module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5SL
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Fix
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5Blk

public noncomputable section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q3L5

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev H₂ : Subgroup SL(4 + 1, ZMod 3) := blk₄.range

theorem blk₄_injective : Function.Injective blk₄ := fun X Y h => by
  have := congrArg (fun g : SL(4 + 1, ZMod 3) => p₁ (k := 4) (m := 1) (g : Mat (4 + 1))) h
  simp only [coe_blk₄, p₁_diagBlock] at this
  exact sl_ext this

theorem comm_of_mem_u₂ {g : SL(4 + 1, ZMod 3)} (hg : g ∈ Subgroup.centralizer {u₂}) :
    (g : Mat (4 + 1)) * diagBlock (k := 4) (m := 1) (-1) 1 =
      diagBlock (k := 4) (m := 1) (-1) 1 * (g : Mat (4 + 1)) := by
  have := congrArg (fun x : SL(4 + 1, ZMod 3) => (x : Mat (4 + 1)))
    (Subgroup.mem_centralizer_singleton_iff.mp hg)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  rw [← coe_u₂]
  exact this

theorem H₂_le : H₂ ≤ Subgroup.centralizer {u₂} := by
  rintro _ ⟨X, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blk₄, coe_u₂]
  exact diagBlock_comm_neg (X : Mat 4) (1 : Mat 1)

instance isPerfect_H₂ : Group.IsPerfect H₂ :=
  have : Group.IsPerfect SL(4, ZMod 3) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  Group.IsPerfect.range _

theorem noOddNormal_H₂ : NoOddNormal H₂ := by
  have h := (noOddNormal_top (k := 2) (by norm_num)).map blk₄
    blk₄_injective
  rwa [← MonoidHom.range_eq_map] at h

@[expose] def detHom₂ (M : Subgroup SL(4 + 1, ZMod 3)) (hM : M ≤ Subgroup.centralizer {u₂}) :
    M →* ZMod 3 where
  toFun g := (p₂ (k := 4) (m := 1) ((g : SL(4 + 1, ZMod 3)) : Mat (4 + 1))).det
  map_one' := by
    show (p₂ (k := 4) (m := 1) (1 : Mat (4 + 1))).det = 1
    rw [← diagBlock_one (K := ZMod 3) (k := 4) (m := 1), p₂_diagBlock, Matrix.det_one]
  map_mul' g h := by
    show (p₂ (k := 4) (m := 1) (((g : SL(4 + 1, ZMod 3)) : Mat (4 + 1)) *
      ((h : SL(4 + 1, ZMod 3)) : Mat (4 + 1)))).det = _
    rw [p₂_mul (by decide) (comm_of_mem_u₂ (hM g.2)) (comm_of_mem_u₂ (hM h.2)), Matrix.det_mul]

theorem detHom₂_apply (M : Subgroup SL(4 + 1, ZMod 3)) (hM : M ≤ Subgroup.centralizer {u₂})
    (g : M) : detHom₂ M hM g =
      (p₂ (k := 4) (m := 1) ((g : SL(4 + 1, ZMod 3)) : Mat (4 + 1))).det :=
  rfl

theorem perfect_le_H₂ (M : Subgroup SL(4 + 1, ZMod 3)) (hM : M ≤ Subgroup.centralizer {u₂})
    (hMp : ⁅M, M⁆ = M) : M ≤ H₂ := by
  have : Group.IsPerfect M := Subgroup.isPerfect_iff.mpr hMp
  have : Group.IsSolvable (ZMod 3)ˣ := Group.isSolvable_of_comm fun a b => mul_comm a b
  have hβ := eq_one_of_isPerfect_of_isSolvable (detHom₂ M hM).toHomUnits
  intro g hg
  have hc := comm_of_mem_u₂ (hM hg)
  have hd : (p₂ (k := 4) (m := 1) (g : Mat (4 + 1))).det = 1 := by
    have h1 := congrArg Units.val (DFunLike.congr_fun hβ ⟨g, hg⟩)
    rwa [MonoidHom.one_apply, Units.val_one, MonoidHom.coe_toHomUnits, detHom₂_apply] at h1
  have hp₂ : p₂ (k := 4) (m := 1) (g : Mat (4 + 1)) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.det_unique] using hd
  have hdet := det_eq_p (by decide) hc
  rw [hd, mul_one, g.2] at hdet
  have key : blk₄ ⟨p₁ (k := 4) (m := 1) (g : Mat (4 + 1)), hdet.symm⟩ = g := sl_ext (by
    rw [coe_blk₄ ⟨p₁ (k := 4) (m := 1) (g : Mat (4 + 1)), hdet.symm⟩]
    conv_rhs => rw [eq_diagBlock_p (by decide) hc, hp₂])
  exact ⟨_, key⟩

theorem mul_self_of_mem_H₂ {g : SL(4 + 1, ZMod 3)} (hg : g ∈ Subgroup.centralizer {u₂})
    (hgH : g ∈ Subgroup.centralizer (H₂ : Set SL(4 + 1, ZMod 3))) : g * g = 1 := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hc := comm_of_mem_u₂ hg
  have hA : ∀ X : SL(4, ZMod 3), (X : Mat 4) * p₁ (k := 4) (m := 1) (g : Mat (4 + 1)) =
      p₁ (k := 4) (m := 1) (g : Mat (4 + 1)) * X := by
    intro X
    have := congrArg (fun x : SL(4 + 1, ZMod 3) => p₁ (k := 4) (m := 1) (x : Mat (4 + 1)))
      (Subgroup.mem_centralizer_iff.mp hgH _ ⟨X, rfl⟩)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    rwa [p₁_mul h2 ((coe_blk₄ X).symm ▸ diagBlock_comm_neg _ _) hc,
      p₁_mul h2 hc ((coe_blk₄ X).symm ▸ diagBlock_comm_neg _ _), coe_blk₄,
      p₁_diagBlock] at this
  obtain ⟨c, hcA⟩ := mem_range_scalar_of_commute_transvectionStruct fun t =>
    hA t.toSpecialLinearGroup
  set d := p₂ (k := 4) (m := 1) (g : Mat (4 + 1)) 0 0 with hd
  have hD : p₂ (k := 4) (m := 1) (g : Mat (4 + 1)) = scalar (Fin 1) d := by
    ext i j
    fin_cases i
    fin_cases j
    simp [hd]
  have hdet := det_eq_p h2 hc
  rw [g.2, ← hcA, hD, scalar_apply, scalar_apply, det_diagonal, det_diagonal,
    Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ] at hdet
  have hcd : ∀ c d : ZMod 3, 1 = c ^ Fintype.card (Fin 4) * d ^ Fintype.card (Fin 1) →
      c * c = 1 ∧ d * d = 1 := by decide
  obtain ⟨hcc, hdd⟩ := hcd c d hdet
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, eq_diagBlock_p h2 hc, diagBlock_mul, ← hcA, hD,
    ← map_mul, ← map_mul, hcc, hdd, map_one, map_one, diagBlock_one,
    Matrix.SpecialLinearGroup.coe_one]

end CFSG.ClassicalInvolution.Q3.TA3.Q3L5
