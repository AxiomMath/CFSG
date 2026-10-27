module

public import CFSG.LinearAlgebra.BinaryReflectionNormalizer

public noncomputable section

namespace CFSG.LinearAlgebra.SteinbergBQ

open Module QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem sum_sum_symm_eq_sum_diag {n : ℕ} (g : Fin n → Fin n → ZMod 2)
    (hg : ∀ i j, g i j = g j i) : ∑ i, ∑ j, g i j = ∑ i, g i i := by
  classical
  have key : ∀ i j, g i j = ((if i < j then g i j else 0) + if j < i then g j i else 0) +
      if i = j then g i i else 0 := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij, hij.ne, lt_asymm hij]
    · simp
    · simp [hij, hij.ne', lt_asymm hij, hg i j]
  have h1 : ∑ i, ∑ j, g i j = (∑ i, ∑ j, if i < j then g i j else 0) +
      (∑ i, ∑ j, if j < i then g j i else 0) + ∑ i, ∑ j, (if i = j then g i i else 0) := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
  rw [h1, Finset.sum_comm (f := fun i j => if j < i then g j i else 0), zmod2_add_self,
    zero_add]
  simp

theorem bilin_charVector_self_eq_finrank {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X] (β : LinearMap.BilinForm (ZMod 2) X) (hβ : β.Nondegenerate)
    (hsymm : ∀ x y, β x y = β y x) {c : X} (hc : ∀ x, β x x = β x c) :
    β c c = (finrank (ZMod 2) X : ZMod 2) := by
  classical
  set b := Module.finBasis (ZMod 2) X with hbdef
  set d := β.dualBasis hβ b with hddef
  have hdb : ∀ i j, β (d i) (b j) = if j = i then 1 else 0 := fun i j =>
    LinearMap.BilinForm.apply_dualBasis_left hβ b i j
  have hexp : ∀ x, x = ∑ j, β x (b j) • d j := fun x => by
    conv_lhs => rw [← d.sum_repr x]
    simp only [hddef, LinearMap.BilinForm.dualBasis_repr_apply]
  have hone : ∀ i, β (b i) (d i) = 1 := fun i => by
    rw [hsymm, hdb]
    simp
  have hw : (finrank (ZMod 2) X : ZMod 2) = ∑ i, ∑ j, β (b i) (b j) * β (d j) (d i) := by
    have h1 : (finrank (ZMod 2) X : ZMod 2) = ∑ i, β (b i) (d i) := by
      simp [hone]
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [hexp (b i)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hcc : β c c = ∑ j, β (b j) (b j) * β (d j) (d j) := by
    have h1 : β c c = β (∑ j, β c (b j) • d j) c := congrArg (fun y => β y c) (hexp c)
    rw [h1]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm c (b j), ← hc (b j), ← hc (d j)]
  rw [hcc, hw, sum_sum_symm_eq_sum_diag]
  intro i j
  show β (b i) (b j) * β (d j) (d i) = β (b j) (b i) * β (d i) (d j)
  rw [hsymm (b i) (b j), hsymm (d j) (d i)]

variable {q : QuadraticForm (ZMod 2) V}

variable [FiniteDimensional (ZMod 2) V] {w : ℕ} {L : Submodule (ZMod 2) V}

end CFSG.LinearAlgebra.SteinbergBQ

