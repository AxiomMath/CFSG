module

public import CFSG.HardMathSupport.U4FF.ClassUminusA

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution)

abbrev SU4 (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Type :=
  ↥(SU (unitaryInvolution K 2 n) 4)

section Twist

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Type*} [Field k]

@[expose] noncomputable def suToSL (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    SU4 K n →* SL(4, K) where
  toFun g := ⟨((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), g.2.1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[expose] noncomputable def twistHom (n : ℕ) (φ : K →+* k) : SU4 K n →* SL(4, k) :=
  (Matrix.SpecialLinearGroup.map φ).comp (suToSL K n)

theorem twistHom_val (φ : K →+* k) (g : SU4 K n) :
    ((twistHom n φ g : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map φ := rfl

variable (k) in
@[expose] def lowTransv : Set SL(4, k) :=
  {g | ∃ (i j : Fin 4) (hij : i ≠ j), j < i ∧ ∃ t : k,
    g = Matrix.SpecialLinearGroup.transvection hij t}

variable (k) in
@[expose] def upTransv : Set SL(4, k) :=
  {g | ∃ (i j : Fin 4) (hij : i ≠ j), i < j ∧ ∃ t : k,
    g = Matrix.SpecialLinearGroup.transvection hij t}

variable (k) in
@[expose] def LowT : Subgroup SL(4, k) := Subgroup.closure (lowTransv k)

variable (k) in
@[expose] def UpT : Subgroup SL(4, k) := Subgroup.closure (upTransv k)

private theorem transvection_mem_LowT {i j : Fin 4} (hij : i ≠ j) (hji : j < i) (t : k) :
    Matrix.SpecialLinearGroup.transvection hij t ∈ LowT k :=
  Subgroup.subset_closure ⟨i, j, hij, hji, t, rfl⟩

private theorem transvection_mem_UpT {i j : Fin 4} (hij : i ≠ j) (hij' : i < j) (t : k) :
    Matrix.SpecialLinearGroup.transvection hij t ∈ UpT k :=
  Subgroup.subset_closure ⟨i, j, hij, hij', t, rfl⟩

theorem twistHom_mem_LowT (hK : Nat.card K = (2 ^ n) ^ 2) (φ : K →+* k) {u : SU4 K n}
    (hu : u ∈ LowerU K n) : twistHom n φ u ∈ LowT k := by
  obtain ⟨a, b, c, d, hC, hM⟩ := exists_uCond_of_mem n hK u.2 (mem_LowerU.mp hu)
  have hsu : suToSL K n u = uSL n a b c d := Subtype.ext hM
  have htw : twistHom n φ u = Matrix.SpecialLinearGroup.map φ (uSL n a b c d) := by
    rw [twistHom, MonoidHom.comp_apply, hsu]
  rw [htw, uSL_eq_prod n hC]
  simp only [map_mul, Matrix.SpecialLinearGroup.map_transvection]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact transvection_mem_LowT (by decide) (by decide) _

theorem twistHom_mem_UpT (hK : Nat.card K = (2 ^ n) ^ 2) (φ : K →+* k) {u : SU4 K n}
    (hu : u ∈ UpperU K n) : twistHom n φ u ∈ UpT k := by
  obtain ⟨a, b, c, d, hC, hM⟩ := exists_wCond_of_mem n hK u.2 (mem_UpperU.mp hu)
  have hsu : suToSL K n u = wSL n a b c d := Subtype.ext hM
  have htw : twistHom n φ u = Matrix.SpecialLinearGroup.map φ (wSL n a b c d) := by
    rw [twistHom, MonoidHom.comp_apply, hsu]
  rw [htw, wSL_eq_prod n hC]
  simp only [map_mul, Matrix.SpecialLinearGroup.map_transvection]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact transvection_mem_UpT (by decide) (by decide) _

theorem twistHom_diag (φ : K →+* k) {h : SU4 K n}
    (hd : ∀ i j, i ≠ j → ((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 0) :
    ((twistHom n φ h : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) =
      Matrix.diagonal (fun i => φ (((h : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i)) := by
  rw [twistHom_val]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Matrix.map_apply, hd i j hij, Matrix.diagonal_apply_ne _ hij, map_zero]

end Twist

end CFSG.HardMathSupport.U4FF
