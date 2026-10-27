module

public import CFSG.Timmesfeld.Transvection.ModelRankSp

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

namespace T7L

section Tv

variable {n : ℕ} {F : Type} [Field F]

theorem matrix_ext_of_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {M N : Matrix ι ι F}
    (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simpa [Matrix.toLin'_apply] using h x)

@[expose] noncomputable def tv (v : Fin n ⊕ Fin n → F) (c : F) : StatedSp n F :=
  Classical.choose (exists_mat_eq_spTrans v c)

theorem mat_tv (v : Fin n ⊕ Fin n → F) (c : F) : mat n F (tv v c) = spTrans v c :=
  Classical.choose_spec (exists_mat_eq_spTrans v c)

theorem tv_mul (v : Fin n ⊕ Fin n → F) (a b : F) : tv v a * tv v b = tv v (a + b) :=
  mat_injective (by rw [map_mul, mat_tv, mat_tv, mat_tv, spTrans_mul_spTrans])

theorem tv_zero (v : Fin n ⊕ Fin n → F) : tv v (0 : F) = 1 :=
  mat_injective (by rw [mat_tv, map_one, spTrans_zero])

theorem tv_inv (v : Fin n ⊕ Fin n → F) (c : F) : (tv v c)⁻¹ = tv v (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [tv_mul, add_neg_cancel, tv_zero])

theorem tv_comm {v w : Fin n ⊕ Fin n → F} (h : spForm v w = 0) (a b : F) :
    tv v a * tv w b = tv w b * tv v a :=
  mat_injective (by rw [map_mul, map_mul, mat_tv, mat_tv, spTrans_commute_of_spForm_eq_zero h])

theorem tv_neg_vec (v : Fin n ⊕ Fin n → F) (c : F) : tv (-v) c = tv v c := by
  apply mat_injective
  rw [mat_tv, mat_tv, ← neg_one_smul F v, spTrans_smul]
  congr 1
  ring

theorem conj_tv (g : StatedSp n F) (v : Fin n ⊕ Fin n → F) (c : F) :
    g * tv v c * g⁻¹ = tv (mat n F g *ᵥ v) c :=
  mat_injective (by rw [mat_conj_of_mat_eq (mat_tv v c) g, mat_tv])

theorem mat_tv_mulVec (v x : Fin n ⊕ Fin n → F) (c : F) :
    mat n F (tv v c) *ᵥ x = x + (c * spForm v x) • v := by
  rw [mat_tv, spTrans_mulVec]

theorem spForm_sub_add_eq_zero {v w : Fin n ⊕ Fin n → F} (h : spForm v w = 0) :
    spForm (v - w) (v + w) = 0 := by
  have h' : spForm w v = 0 := by rw [spForm_comm, h, neg_zero]
  rw [spForm_sub_left, spForm_add_right, spForm_add_right, spForm_self, spForm_self, h, h']
  ring

theorem tv_three {v w : Fin n ⊕ Fin n → F} (h : spForm v w = 0) (c : F) :
    tv (v - w) c * tv (v + w) c * tv v (-c + -c) = tv w (c + c) := by
  have h' : spForm w v = 0 := by rw [spForm_comm, h, neg_zero]
  apply mat_injective
  rw [map_mul, map_mul, mat_tv, mat_tv, mat_tv, mat_tv]
  apply matrix_ext_of_mulVec
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, spTrans_mulVec, spTrans_mulVec,
    spTrans_mulVec, spTrans_mulVec]
  simp only [spForm_add_left, spForm_add_right, spForm_sub_left, spForm_smul_right', spForm_self,
    h, h']
  module

end Tv

end T7L

end CFSG.ClassicalInvolution.Asc77
