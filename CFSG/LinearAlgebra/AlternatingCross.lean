module

public import Mathlib.LinearAlgebra.CrossProduct

public section

namespace CFSG.LinearAlgebra

open Matrix

variable {K : Type*} [Field K]

private def alternatingTriple (A : Matrix (Fin 3) (Fin 3) K) : Fin 3 → K :=
  ![-A 1 2, A 0 2, -A 0 1]

private lemma alternatingTriple_injective {A B : Matrix (Fin 3) (Fin 3) K}
    (hA : Aᵀ = -A) (hdA : ∀ i, A i i = 0) (hB : Bᵀ = -B) (hdB : ∀ i, B i i = 0)
    (h : alternatingTriple A = alternatingTriple B) : A = B := by
  have hskewA : ∀ i j, A j i = -A i j := fun i j => by
    have := congrFun (congrFun hA i) j
    simpa using this
  have hskewB : ∀ i j, B j i = -B i j := fun i j => by
    have := congrFun (congrFun hB i) j
    simpa using this
  have h02 : A 0 2 = B 0 2 := by simpa [alternatingTriple] using congrFun h 1
  have h01 : A 0 1 = B 0 1 := by simpa [alternatingTriple] using congrFun h 2
  have h12 : A 1 2 = B 1 2 := by simpa [alternatingTriple] using congrFun h 0
  have h10 : A 1 0 = B 1 0 := by rw [hskewA 0 1, hskewB 0 1, h01]
  have h20 : A 2 0 = B 2 0 := by rw [hskewA 0 2, hskewB 0 2, h02]
  have h21 : A 2 1 = B 2 1 := by rw [hskewA 1 2, hskewB 1 2, h12]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h01, h02, h10, h12, h20, h21, hdA, hdB]

private lemma mulVec_eq_crossProduct_alternatingTriple {A : Matrix (Fin 3) (Fin 3) K}
    (hA : Aᵀ = -A) (hd : ∀ i, A i i = 0) (v : Fin 3 → K) :
    A *ᵥ v = crossProduct (alternatingTriple A) v := by
  have h10 : A 1 0 = -A 0 1 := by
    have h := congrFun (congrFun hA 0) 1
    simpa using h
  have h20 : A 2 0 = -A 0 2 := by
    have h := congrFun (congrFun hA 0) 2
    simpa using h
  have h21 : A 2 1 = -A 1 2 := by
    have h := congrFun (congrFun hA 1) 2
    simpa using h
  ext k
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, cross_apply, alternatingTriple, hd, h10, h20, h21,
      Fin.sum_univ_three] <;>
    ring

private lemma exists_smul_eq_of_crossProduct_eq_zero {v w : Fin 3 → K} (hv : v ≠ 0)
    (h : crossProduct w v = 0) : ∃ c : K, w = c • v := by
  have hni : ¬ LinearIndependent K ![w, v] := fun hli =>
    (crossProduct_ne_zero_iff_linearIndependent.mpr hli) h
  have hni' : ¬ LinearIndependent K ![v, w] := fun hli =>
    hni (LinearIndependent.pair_symm_iff.mpr hli)
  rw [LinearIndependent.pair_iff' hv] at hni'
  push Not at hni'
  obtain ⟨c, hc⟩ := hni'
  exact ⟨c, hc.symm⟩

theorem eq_zero_of_forall_alternating_mulVec_eq_zero [Finite K]
    (S : AddSubgroup (Matrix (Fin 3) (Fin 3) K)) (hS : ∀ A ∈ S, Aᵀ = -A ∧ ∀ i, A i i = 0)
    (hcard : Nat.card K < Nat.card S) {v : Fin 3 → K} (hv : ∀ A ∈ S, A *ᵥ v = 0) : v = 0 := by
  by_contra hv0
  have hcross : ∀ A : S, crossProduct (alternatingTriple (A : Matrix (Fin 3) (Fin 3) K)) v = 0 :=
    fun A => by
      rw [← mulVec_eq_crossProduct_alternatingTriple (hS A A.2).1 (hS A A.2).2 v, hv A A.2]
  choose c hc using fun A : S => exists_smul_eq_of_crossProduct_eq_zero hv0 (hcross A)
  have hinj : Function.Injective c := by
    intro A B hAB
    apply Subtype.ext
    apply alternatingTriple_injective (hS A A.2).1 (hS A A.2).2 (hS B B.2).1 (hS B B.2).2
    rw [hc A, hc B, hAB]
  have hle := Nat.card_le_card_of_injective c hinj
  omega

end CFSG.LinearAlgebra
