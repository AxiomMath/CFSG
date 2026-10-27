module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out

open Matrix
open scoped MatrixGroups

@[expose] def diagGL {K : Type*} [Field K] {n : ℕ} : (Fin n → Kˣ) →* GL (Fin n) K where
  toFun d := ⟨diagonal (fun j => ((d j : Kˣ) : K)), diagonal (fun j => (((d j)⁻¹ : Kˣ) : K)),
    by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩
  map_one' := Units.ext (by simp)
  map_mul' d e := Units.ext (by simp [diagonal_mul_diagonal])

theorem coe_diagGL {K : Type*} [Field K] {n : ℕ} (d : Fin n → Kˣ) :
    ((diagGL d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (fun j => ((d j : Kˣ) : K)) :=
  rfl

@[expose] def diagSL {K : Type*} [Field K] {n : ℕ} (d : Fin n → Kˣ) (hd : ∏ j, d j = 1) :
    SpecialLinearGroup (Fin n) K :=
  ⟨diagonal (fun j => ((d j : Kˣ) : K)), by
    rw [det_diagonal, ← Units.coe_prod, hd, Units.val_one]⟩

theorem coe_diagSL {K : Type*} [Field K] {n : ℕ} (d : Fin n → Kˣ) (hd : ∏ j, d j = 1) :
    (diagSL d hd : Matrix (Fin n) (Fin n) K) = diagonal (fun j => ((d j : Kˣ) : K)) :=
  rfl

@[expose] def diagSLHom {K : Type*} [Field K] {n : ℕ} {G : Type*} [Group G]
    (κ : G →* (Fin n → Kˣ)) (hdet : ∀ g, ∏ j, κ g j = 1) :
    G →* SpecialLinearGroup (Fin n) K where
  toFun g := diagSL (κ g) (hdet g)
  map_one' := by
    apply Subtype.ext
    rw [coe_diagSL, SpecialLinearGroup.coe_one]
    simp
  map_mul' g h := by
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, coe_diagSL, coe_diagSL, coe_diagSL, diagonal_mul_diagonal]
    simp [map_mul]

theorem coe_diagSLHom {K : Type*} [Field K] {n : ℕ} {G : Type*} [Group G]
    (κ : G →* (Fin n → Kˣ)) (hdet : ∀ g, ∏ j, κ g j = 1) (g : G) :
    (diagSLHom κ hdet g : Matrix (Fin n) (Fin n) K) = diagonal (fun j => ((κ g j : Kˣ) : K)) :=
  rfl

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out
