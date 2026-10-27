module

public import CFSG.Blueprint.SourceBinaryGolayCode
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.Blueprint.EvenSource

open Finset

@[expose] def golayWord (c : Fin 12 → ZMod 2) : Fin 24 → ZMod 2 :=
  ∑ i, c i • sourceGolayGenerator i

theorem mem_sourceGolayCode_iff (x : Fin 24 → ZMod 2) :
    x ∈ sourceGolayCode ↔ ∃ c, golayWord c = x := by
  rw [sourceGolayCode, ← Fintype.range_linearCombination, LinearMap.mem_range]
  simp only [Fintype.linearCombination_apply, golayWord]

theorem golayWord_castAdd (c : Fin 12 → ZMod 2) (i : Fin 12) :
    golayWord c (Fin.castAdd 12 i) = c i := by
  simp only [golayWord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sourceGolayGenerator,
    Fin.append_left]
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [ite_eq_right (Ne.symm hk), mul_zero])
    (by simp), ite_eq_left rfl, mul_one]

theorem sourceGolayGenerator_dotProduct (i j : Fin 12) :
    sourceGolayGenerator i ⬝ᵥ sourceGolayGenerator j = 0 := by
  revert i j
  decide +kernel

theorem golayWord_dotProduct (c d : Fin 12 → ZMod 2) : golayWord c ⬝ᵥ golayWord d = 0 := by
  simp only [golayWord, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul,
    sourceGolayGenerator_dotProduct, smul_zero, Finset.sum_const_zero]

theorem sourceGolayB12_mul_transpose : sourceGolayB12 * sourceGolayB12.transpose = 1 := by
  decide +kernel

theorem sourceGolayGenerator_natAdd (i k : Fin 12) :
    sourceGolayGenerator i (Fin.natAdd 12 k) = sourceGolayB12 i k := by
  simp only [sourceGolayGenerator, Fin.append_right]

theorem mem_of_forall_dotProduct_eq_zero {x : Fin 24 → ZMod 2}
    (hx : ∀ y ∈ sourceGolayCode, x ⬝ᵥ y = 0) : x ∈ sourceGolayCode := by
  set c : Fin 12 → ZMod 2 := fun i => x (Fin.castAdd 12 i)
  set y := x - golayWord c with hy
  have hy0 : ∀ i : Fin 12, y (Fin.castAdd 12 i) = 0 := fun i => by
    rw [hy, Pi.sub_apply, golayWord_castAdd, sub_self]
  have hydot : ∀ i : Fin 12, y ⬝ᵥ sourceGolayGenerator i = 0 := fun i => by
    rw [hy, sub_dotProduct, hx _ (sourceGolayGenerator_mem i)]
    have := golayWord_dotProduct c (Pi.single i 1)
    rw [show golayWord (Pi.single i 1) = sourceGolayGenerator i by
      simp [golayWord, Pi.single_apply]] at this
    rw [this, sub_zero]
  set y₂ : Fin 12 → ZMod 2 := fun k => y (Fin.natAdd 12 k)
  have hB : sourceGolayB12.mulVec y₂ = 0 := by
    funext i
    have h := hydot i
    rw [dotProduct, show (∑ t : Fin 24, y t * sourceGolayGenerator i t) =
        ∑ t : Fin (12 + 12), y t * sourceGolayGenerator i t from rfl, Fin.sum_univ_add] at h
    simp only [hy0, zero_mul, Finset.sum_const_zero, zero_add, sourceGolayGenerator_natAdd] at h
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← h]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  have hy₂ : y₂ = 0 := by
    have h1 : sourceGolayB12.transpose * sourceGolayB12 = 1 :=
      mul_eq_one_comm.1 sourceGolayB12_mul_transpose
    rw [← Matrix.one_mulVec y₂, ← h1, ← Matrix.mulVec_mulVec, hB, Matrix.mulVec_zero]
  have hyz : y = 0 := by
    funext j
    revert j
    show ∀ j : Fin (12 + 12), y j = 0
    intro j
    induction j using Fin.addCases with
    | left i => exact hy0 i
    | right k => exact congrFun hy₂ k
  rw [sub_eq_zero] at hyz
  rw [hyz]
  exact (mem_sourceGolayCode_iff _).2 ⟨c, rfl⟩

theorem mem_iff_forall_dotProduct (x : Fin 24 → ZMod 2) :
    x ∈ sourceGolayCode ↔ ∀ y ∈ sourceGolayCode, x ⬝ᵥ y = 0 := by
  refine ⟨fun hx y hy => ?_, mem_of_forall_dotProduct_eq_zero⟩
  obtain ⟨c, rfl⟩ := (mem_sourceGolayCode_iff x).1 hx
  obtain ⟨d, rfl⟩ := (mem_sourceGolayCode_iff y).1 hy
  exact golayWord_dotProduct c d

end CFSG.Blueprint.EvenSource
