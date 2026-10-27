module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup
open scoped MatrixGroups Matrix

section SLElements

variable {k : Type} [Field k]

@[expose] def ivk95lSigns {d : ℕ} (p q : Fin d) : Fin d → k := fun i => if i = p ∨ i = q then -1 else 1

theorem ivk95lSigns_mul_self {d : ℕ} (p q i : Fin d) :
    (ivk95lSigns p q i : k) * ivk95lSigns p q i = 1 := by
  unfold ivk95lSigns
  split_ifs <;> simp

theorem ivk95lSigns_prod {d : ℕ} {p q : Fin d} (hpq : p ≠ q) : ∏ i, (ivk95lSigns p q i : k) = 1 := by
  have h1 : ∀ i ∈ Finset.univ, ivk95lSigns p q i = (if i = p then (-1 : k) else 1) *
      (if i = q then (-1 : k) else 1) := by
    intro i _
    unfold ivk95lSigns
    by_cases hp : i = p
    · by_cases hq : i = q
      · exact absurd (hp ▸ hq) hpq
      · subst hp
        simp [hq]
    · by_cases hq : i = q
      · subst hq
        simp [hp]
      · simp [hp, hq]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib]
  simp [Finset.prod_ite_eq']

@[expose] def ivk95lSignMatrix {d : ℕ} {p q : Fin d} (hpq : p ≠ q) : SL(d, k) :=
  ⟨Matrix.diagonal (ivk95lSigns p q), by rw [Matrix.det_diagonal]; exact ivk95lSigns_prod hpq⟩

theorem ivk95l_two_involutions (h2 : (2 : k) ≠ 0) {d : ℕ} (hd : 3 ≤ d) :
    ∃ u v : SL(d, k), u * u = 1 ∧ v * v = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  have h0 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h0' : (⟨0, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hm1 : (-1 : k) ≠ 1 := by
    intro h
    apply h2
    have : (1 : k) + 1 = 0 := by nth_rewrite 2 [← h]; simp
    simpa [one_add_one_eq_two] using this
  have hne : ∀ {p q : Fin d} (hpq : p ≠ q), ivk95lSignMatrix (k := k) hpq ≠ 1 := by
    intro p q hpq h
    have := congrArg (fun A : SL(d, k) => (A : Matrix (Fin d) (Fin d) k) p p) h
    simp [ivk95lSignMatrix, ivk95lSigns] at this
    exact hm1 this
  have hsq : ∀ {p q : Fin d} (hpq : p ≠ q), ivk95lSignMatrix (k := k) hpq * ivk95lSignMatrix hpq = 1 := by
    intro p q hpq
    apply Subtype.ext
    change Matrix.diagonal (ivk95lSigns p q) * Matrix.diagonal (ivk95lSigns p q) =
      (1 : Matrix (Fin d) (Fin d) k)
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [ivk95lSigns_mul_self]
    · simp [hij]
  refine ⟨ivk95lSignMatrix h0, ivk95lSignMatrix h0', hsq h0, hsq h0', hne h0, hne h0', fun h => ?_⟩
  have := congrArg (fun A : SL(d, k) => (A : Matrix (Fin d) (Fin d) k) ⟨1, by omega⟩ ⟨1, by omega⟩) h
  simp [ivk95lSignMatrix, ivk95lSigns, Fin.ext_iff] at this
  exact hm1 this

theorem ivk95l_order_four :
    ∃ w : SL(2, k), w * w = -1 ∧ w ∉ Subgroup.center SL(2, k) := by
  let w : SL(2, k) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  refine ⟨w, ?_, ?_⟩
  · apply Subtype.ext
    change (!![0, 1; -1, 0] * !![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) =
      ((-1 : SL(2, k)) : Matrix (Fin 2) (Fin 2) k)
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro hw
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hw
    have := congrArg (fun A : Matrix (Fin 2) (Fin 2) k => A 0 1) hr
    simp [w] at this

end SLElements

section Scalars

variable {k : Type} [Field k] {m : ℕ}

theorem ivk95l_hom_one_of_perfect {G A : Type*} [Group G] [Group A] [IsMulCommutative A]
    (hG : Group.IsPerfect G)
    (φ : G →* A) : φ = 1 := by
  have htop : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  have hle : (⊤ : Subgroup G) ≤ φ.ker := by
    rw [← htop, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact IsMulCommutative.is_comm.comm _ _
  ext g
  exact hle (Subgroup.mem_top g)

theorem ivk95l_scalar_eq_one {b : ℕ} (hb : 1 ≤ b) {c : kˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin b) c = 1) : c = 1 := by
  have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin b) c : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)
      ⟨0, hb⟩ ⟨0, hb⟩ = c := by
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have h2 : ((1 : GL (Fin b) k) : Matrix (Fin b) (Fin b) k) ⟨0, hb⟩ ⟨0, hb⟩ = 1 := by simp
  apply Units.ext
  rw [← h1, h, h2]
  rfl

theorem ivk95l_center_scalar (hm : 0 < m) {A : SL(m, k)} (h : A ∈ Subgroup.center SL(m, k)) :
    ∃ c : kˣ, Matrix.SpecialLinearGroup.toGL A = Matrix.GeneralLinearGroup.scalar (Fin m) c := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow hm.ne'] at hr
    exact zero_ne_one hr
  refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.GeneralLinearGroup.coe_scalar,
    Units.val_mk0]
  exact hrA.symm

theorem ivk95l_mem_center_of_scalar {A : SL(m, k)} {c : kˣ}
    (h : Matrix.SpecialLinearGroup.toGL A = Matrix.GeneralLinearGroup.scalar (Fin m) c) :
    A ∈ Subgroup.center SL(m, k) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  have hA : (Matrix.scalar (Fin m)) (c : k) = (A : Matrix (Fin m) (Fin m) k) := by
    have := congrArg (fun u : GL (Fin m) k => (u : Matrix (Fin m) (Fin m) k)) h
    simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.GeneralLinearGroup.coe_scalar] at this
    exact this.symm
  refine ⟨c, ?_, hA⟩
  have hdet := A.2
  rw [← hA, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ] at hdet
  exact hdet

theorem ivk95l_neg_one_ne_one (h2 : (2 : k) ≠ 0) : (-1 : SL(2, k)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
    Matrix.one_apply_eq] at this
  apply h2
  linear_combination -this

theorem ivk95l_toGL_neg_one : Matrix.SpecialLinearGroup.toGL (-1 : SL(2, k)) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : kˣ) := by
  apply Units.ext
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg,
    Units.val_one]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

end Scalars

end CFSG.GH74.GLS.IVK.Proofs2
