module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceRegularSylow
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

abbrev GL32 : Type := GL (Fin 3) (ZMod 2)

@[expose] def conjLin (g : GL32) : Mat3 ≃ₗ[ZMod 2] Mat3 where
  toFun X := (g : Mat3) * X * ((g⁻¹ : GL32) : Mat3)
  invFun X := ((g⁻¹ : GL32) : Mat3) * X * (g : Mat3)
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
  left_inv X := by
    have h1 : ((g⁻¹ : GL32) : Mat3) * (g : Mat3) = 1 := Units.inv_mul g
    calc ((g⁻¹ : GL32) : Mat3) * ((g : Mat3) * X * ((g⁻¹ : GL32) : Mat3)) * (g : Mat3)
        = (((g⁻¹ : GL32) : Mat3) * (g : Mat3)) * X * (((g⁻¹ : GL32) : Mat3) * (g : Mat3)) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  right_inv X := by
    have h1 : (g : Mat3) * ((g⁻¹ : GL32) : Mat3) = 1 := Units.mul_inv g
    calc (g : Mat3) * (((g⁻¹ : GL32) : Mat3) * X * (g : Mat3)) * ((g⁻¹ : GL32) : Mat3)
        = ((g : Mat3) * ((g⁻¹ : GL32) : Mat3)) * X * ((g : Mat3) * ((g⁻¹ : GL32) : Mat3)) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, Matrix.one_mul, Matrix.mul_one]

theorem conjLin_apply (g : GL32) (X : Mat3) :
    conjLin g X = (g : Mat3) * X * ((g⁻¹ : GL32) : Mat3) := rfl

@[expose] def conjRep : GL32 →* (Mat3 ≃ₗ[ZMod 2] Mat3) where
  toFun := conjLin
  map_one' := by
    refine LinearEquiv.ext fun X => ?_
    simp [conjLin_apply]
  map_mul' g h := by
    refine LinearEquiv.ext fun X => ?_
    simp only [conjLin_apply, LinearEquiv.mul_apply, _root_.mul_inv_rev, Units.val_mul,
      Matrix.mul_assoc]

theorem conjRep_apply (g : GL32) (X : Mat3) :
    conjRep g X = (g : Mat3) * X * ((g⁻¹ : GL32) : Mat3) := rfl

theorem card_sylowT : Nat.card sylowT = 8 := by
  rw [Nat.card_congr tripleEquiv.symm]
  simp

theorem isPGroup_sylowT : IsPGroup 2 sylowT :=
  IsPGroup.of_card (n := 3) (by rw [card_sylowT]; norm_num)

abbrev E13 : Mat3 := Matrix.single 0 2 1

theorem fixed_traceZeroMat : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : ZMod 2,
    unitri 1 0 0 * traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 * unitri 1 (1 * 0 + 0) 0 =
        traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 →
      unitri 0 0 1 * traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 * unitri 0 (0 * 1 + 0) 1 =
        traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 →
      traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 = 0 ∨ traceZeroMat x0 x1 x2 x3 x4 x5 x6 x7 = E13 := by
  decide +kernel

@[expose] def wGL : GL32 :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩

theorem conjLin_wGL_E13 : conjLin wGL E13 = E31 := by
  decide +kernel

theorem traceZero_irreducible {B : Submodule (ZMod 2) Mat3} (hB : B ≤ traceZero)
    (hinv : ∀ g : GL32, ∀ X ∈ B, (g : Mat3) * X * ((g⁻¹ : GL32) : Mat3) ∈ B) :
    B = ⊥ ∨ B = traceZero := by
  by_cases hB0 : B = ⊥
  · exact Or.inl hB0
  right
  obtain ⟨X, hXB, hX0, hXfix⟩ := @exists_ne_zero_fixed GL32 Mat3 _ _ Matrix.module _ conjRep sylowT
    isPGroup_sylowT B hB0
    (fun g _ x hx => hinv g x hx)
  have hXA : X ∈ traceZero := hB hXB
  have hX := eq_traceZeroMat hXA
  have h1 : unitri 1 0 0 * X * unitri 1 (1 * 0 + 0) 0 = X := hXfix (unitriGL 1 0 0) ⟨1, 0, 0, rfl⟩
  have h2 : unitri 0 0 1 * X * unitri 0 (0 * 1 + 0) 1 = X := hXfix (unitriGL 0 0 1) ⟨0, 0, 1, rfl⟩
  have hE : X = E13 := by
    rcases fixed_traceZeroMat (X 0 0) (X 0 1) (X 0 2) (X 1 0) (X 1 1) (X 1 2) (X 2 0) (X 2 1)
      (by rw [← hX]; exact h1) (by rw [← hX]; exact h2) with h | h
    · exact absurd (hX.trans h) hX0
    · exact hX.trans h
  have h3 : (wGL : Mat3) * E13 * ((wGL⁻¹ : GL32) : Mat3) = E31 := conjLin_wGL_E13
  have hE31 : E31 ∈ B := by
    have := hinv wGL X hXB
    rw [hE, h3] at this
    exact this
  refine le_antisymm hB fun Y hY => ?_
  have hspan : ⊤ ≤ Submodule.span (ZMod 2) (Set.range conjFamily) := span_conjFamily
  have hle : Submodule.span (ZMod 2) (Set.range conjFamily) ≤ B.comap traceZero.subtype := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨t, rfl⟩
    exact hinv (t : GL32) E31 hE31
  have hmem : (⟨Y, hY⟩ : traceZero) ∈ B.comap traceZero.subtype :=
    hle (hspan (Submodule.mem_top))
  exact hmem

end CFSG.QuasithinUnique.Setup.Family
