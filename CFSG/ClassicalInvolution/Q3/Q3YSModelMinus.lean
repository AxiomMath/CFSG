module

public import CFSG.ClassicalInvolution.Q3.Q3YSInputs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin

section Frame

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

theorem longTorus_neg_one_mul_self (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    F.longTorus hij s t (-1) * F.longTorus hij s t (-1) = 1 := by
  rw [← map_mul]
  have : (-1 : Kˣ) * (-1) = 1 := Units.ext (by simp)
  rw [this, map_one]

theorem longTorus_neg_one_conj_odd (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    {k l : Fin n} (hkl : k ≠ l) (u v : Bool) (c : K)
    (hodd : Odd (longCoroot i j s t k u + longCoroot i j s t l v)) :
    F.longTorus hij s t (-1) * F.longRoot hkl u v (.ofAdd c) * (F.longTorus hij s t (-1))⁻¹ =
      F.longRoot hkl u v (.ofAdd (-c)) := by
  rw [F.longTorus_conj_longRoot, hodd.neg_one_zpow]
  simp

theorem longTorus_neg_one_conj_even (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    {k l : Fin n} (hkl : k ≠ l) (u v : Bool) (c : K)
    (heven : Even (longCoroot i j s t k u + longCoroot i j s t l v)) :
    F.longTorus hij s t (-1) * F.longRoot hkl u v (.ofAdd c) * (F.longTorus hij s t (-1))⁻¹ =
      F.longRoot hkl u v (.ofAdd c) := by
  rw [F.longTorus_conj_longRoot, heven.neg_one_zpow]
  simp

theorem not_mem_center_of_conj_longRoot (F : HypFrame Q n) {k l : Fin n} (hkl : k ≠ l)
    (u v : Bool) {g : ↥(spinGroup Q)} {c d : K} (hcd : c ≠ d)
    (h : g * F.longRoot hkl u v (.ofAdd c) * g⁻¹ = F.longRoot hkl u v (.ofAdd d)) :
    g ∉ Subgroup.center ↥(spinGroup Q) := by
  intro hg
  have h1 : g * F.longRoot hkl u v (.ofAdd c) * g⁻¹ = F.longRoot hkl u v (.ofAdd c) := by
    rw [← Subgroup.mem_center_iff.mp hg (F.longRoot hkl u v (.ofAdd c))]
    group
  rw [h1] at h
  exact hcd (Multiplicative.ofAdd.injective (F.longRoot_injective hkl u v h))

theorem exists_fourGroup_hypFrame [Finite ↥(spinGroup Q)] (F : HypFrame Q n) (hn : 3 ≤ n)
    (hk : (-1 : K) ≠ 1) :
    ∃ Fo : Subgroup ↥(spinGroup Q), IsElemAbelian 2 Fo ∧ Nat.card Fo = 4 ∧
      Fo ⊓ Subgroup.center ↥(spinGroup Q) = ⊥ := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hne : (-1 : K) ≠ 1 := hk
  have hp : F.longTorus hab true false (-1) ∉ Subgroup.center ↥(spinGroup Q) := by
    refine not_mem_center_of_conj_longRoot F hbc true false (c := 1) (d := -1) hne.symm ?_
    exact longTorus_neg_one_conj_odd F hab true false hbc true false 1 (by
      simp [longCoroot, a, b, c, Fin.ext_iff])
  have hq : F.longTorus hbc true false (-1) ∉ Subgroup.center ↥(spinGroup Q) := by
    refine not_mem_center_of_conj_longRoot F hab true false (c := 1) (d := -1) hne.symm ?_
    exact longTorus_neg_one_conj_odd F hbc true false hab true false 1 (by
      simp [longCoroot, a, b, c, Fin.ext_iff])
  have hpq : F.longTorus hab true false (-1) * F.longTorus hbc true false (-1) ∉
      Subgroup.center ↥(spinGroup Q) := by
    refine not_mem_center_of_conj_longRoot F hab true false (c := 1) (d := -1) hne.symm ?_
    have e : ∀ g₁ g₂ y : ↥(spinGroup Q),
        g₁ * g₂ * y * (g₁ * g₂)⁻¹ = g₁ * (g₂ * y * g₂⁻¹) * g₁⁻¹ := by
      intros
      group
    rw [e, longTorus_neg_one_conj_odd F hbc true false hab true false 1 (by
      simp [longCoroot, a, b, c, Fin.ext_iff])]
    exact longTorus_neg_one_conj_even F hab true false hab true false (-1) (by
      simp [longCoroot, a, b, Fin.ext_iff])
  exact exists_fourGroup_of_noncentral (longTorus_neg_one_mul_self F hab true false)
    (longTorus_neg_one_mul_self F hbc true false)
    (F.commute_longTorus_longTorus hab true false (-1) hbc true false (-1)).eq hp hq hpq

end Frame

section Model


theorem fourGroup_pOmegaMinus (n : ℕ) (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    ∃ F : Subgroup (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K, IsElemAbelian 2 F ∧
      Nat.card F = 4 ∧
        F ⊓ Subgroup.center (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K = ⊥ := by
  have hn : 4 ≤ n := hadm.2.2
  have hfin0 : Finite (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  have hfin : Finite ↥(spinGroup (Spin.quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) := hfin0
  exact exists_fourGroup_hypFrame
    (Spin.Twisted.minusFrame n (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame (by omega)
    neg_one_ne_one_gf3

theorem modelFourGroup3On_minus : ModelFourGroup3On fun t => t = .POmegaMinus := by
  intro t n ht _ hadm _ _
  subst ht
  exact fourGroup_pOmegaMinus n hadm

end Model

end CFSG.ClassicalInvolution.Q3.Q3YS
