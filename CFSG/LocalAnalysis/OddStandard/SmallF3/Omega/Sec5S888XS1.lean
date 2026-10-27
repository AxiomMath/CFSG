module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E5a
import Mathlib.Tactic.FinCases

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

open scoped Classical in
@[expose] noncomputable def suppIdx (hS : PlaneSys V W) (v : V) : Finset (Fin 4) :=
  Finset.univ.filter fun i => comp hS v i ≠ 1

@[expose] def SuppTwo (hS : PlaneSys V W) (v : V) : Prop :=
  (suppIdx hS v).card = 2

theorem suppTwo_mul (hS : PlaneSys V W) {i j : Fin 4} (hij : i ≠ j) {a b : X} (ha : a ∈ W i)
    (hb : b ∈ W j) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    SuppTwo hS ⟨a * b, V.mul_mem (hS.le i ha) (hS.le j hb)⟩ := by
  classical
  let v : V := ⟨a * b, V.mul_mem (hS.le i ha) (hS.le j hb)⟩
  change SuppTwo hS v
  let w : Fin 4 → X := fun k => if k = i then a else if k = j then b else 1
  have hw_mem : ∀ k, w k ∈ W k := by
    intro k
    by_cases hki : k = i
    · rw [hki]
      simpa [w] using ha
    · by_cases hkj : k = j
      · rw [hkj]
        have hji : j ≠ i := fun h => hij h.symm
        simpa [w, hji] using hb
      · simpa [w, hki, hkj] using Subgroup.one_mem (W k)
  have hcomm : a * b = b * a := hS.comm a (hS.le i ha) b (hS.le j hb)
  have hw_prod : w 0 * w 1 * w 2 * w 3 = a * b := by
    fin_cases i <;> fin_cases j <;> simp_all [w]
  have hv_eq : (v : X) = w 0 * w 1 * w 2 * w 3 := by
    show a * b = w 0 * w 1 * w 2 * w 3
    rw [hw_prod]
  have hcomp : comp hS v = w :=
    hS.eq_of_prod_eq (comp_mem hS v) hw_mem ((prod_comp hS v).symm.trans hv_eq)
  have hfilter : Finset.univ.filter (fun k => w k ≠ 1) = {i, j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hk
      by_contra h
      push_neg at h
      exact hk (by simp [w, h.1, h.2])
    · rintro (hki | hkj)
      · rw [hki]
        simpa [w] using ha1
      · rw [hkj]
        have hji : j ≠ i := fun h => hij h.symm
        simpa [w, hji] using hb1
  unfold SuppTwo suppIdx
  rw [hcomp, hfilter, Finset.card_pair hij]

end CFSG.OddStandard.SmallF3.Omega
