module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsData
public import CFSG.LargeExtraspecial.DW37Input
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Matrix CFSG.LargeExtraspecial
open scoped MatrixGroups

@[expose] def heVecEquiv : (Fin 5 → ZMod 2) ≃ Fin 32 :=
  (finFunctionFinEquiv : (Fin 5 → Fin 2) ≃ Fin (2 ^ 5)).trans (finCongr (by norm_num))

@[expose] def heImgRow (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (i : Fin 5) (x : ℕ) : ℕ :=
  ((g i 0).val * (x % 2) + (g i 1).val * (x / 2 % 2) + (g i 2).val * (x / 4 % 2) +
    (g i 3).val * (x / 8 % 2) + (g i 4).val * (x / 16 % 2)) % 2

@[expose] def heImg (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (x : ℕ) : ℕ :=
  heImgRow g 0 x + 2 * heImgRow g 1 x + 4 * heImgRow g 2 x + 8 * heImgRow g 3 x +
    16 * heImgRow g 4 x

@[expose] def heRho : SL(5, ZMod 2) →* Equiv.Perm (Fin 32) where
  toFun g := heVecEquiv.symm.trans ((Matrix.SpecialLinearGroup.toLin' g).toEquiv.trans heVecEquiv)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

@[expose] def hePermSL (σ : Equiv.Perm (Fin 5)) : SL(5, ZMod 2) :=
  ⟨σ.permMatrix (ZMod 2), by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> decide⟩

@[expose] def heElemSL (i j : Fin 5) (hij : i ≠ j) : SL(5, ZMod 2) :=
  Matrix.SpecialLinearGroup.transvection hij 1

@[expose] def heBridgeGen : Fin 12 → SL(5, ZMod 2) :=
  ![heElemSL 0 1 (by decide), heElemSL 0 2 (by decide), heElemSL 0 3 (by decide),
    heElemSL 0 4 (by decide), heElemSL 1 2 (by decide), heElemSL 1 3 (by decide),
    heElemSL 1 4 (by decide), heElemSL 2 3 (by decide), heElemSL 2 4 (by decide),
    heElemSL 3 4 (by decide), hePermSL (Equiv.swap 1 2), hePermSL (Equiv.swap 2 3)]

@[expose] def HeBridgeFacts : Prop :=
  hePCGens.length = 12 ∧ ∀ k : Fin 12,
    (∀ x : Fin 32, (hePCGens[(k : ℕ)]!)[(x : ℕ)]! = heImg (heBridgeGen k) x) ∧
      heBridgeGen k * DW.cornerTransvection (N := 5) (by norm_num) =
        DW.cornerTransvection (N := 5) (by norm_num) * heBridgeGen k

instance : Decidable HeBridgeFacts := by
  unfold HeBridgeFacts
  infer_instance

theorem heBridgeFacts : HeBridgeFacts := by
  decide +kernel

end CFSG.ComponentClassification.AS81.HeTri
