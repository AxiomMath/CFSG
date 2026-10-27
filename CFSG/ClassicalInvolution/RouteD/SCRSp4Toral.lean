module

public import CFSG.ClassicalInvolution.RouteD.SCRSp4Norm

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSp4

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Steinberg.Sp TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem elt_comm_diag (r : RootSubgroupIndex 2) (c : F) (d : Fin 2 ⊕ Fin 2 → F)
    (h : ∀ a b, E F r a b ≠ 0 → d a = d b) :
    mat 2 F (elt r c) * Matrix.diagonal d = Matrix.diagonal d * mat 2 F (elt r c) := by
  rw [mat_elt]
  ext a b
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    simp [mul_comm]
  · by_cases hE : E F r a b = 0
    · simp [Finset.sum_ite_eq, hab, hE]
    · have := h a b hE
      simp [Finset.sum_ite_eq, hab, this, mul_comm]

theorem mat_x0 : mat 2 F (x0 F) =
    Matrix.diagonal (fun a => if a ∈ coords (n := 2) 0 then (-1 : F) else 1) := mat_longInv 0



theorem elt_mem_centralizer_of_diag (r : RootSubgroupIndex 2) (c : F) (y : StatedSp 2 F)
    (d : Fin 2 ⊕ Fin 2 → F) (hd : mat 2 F y = Matrix.diagonal d)
    (hr : ∀ a b, E F r a b ≠ 0 → d a = d b) :
    elt r c ∈ Subgroup.centralizer ({y} : Set (StatedSp 2 F)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mat_injective
  rw [map_mul, map_mul, hd]
  exact elt_comm_diag r c d hr

theorem E_posLong_supp (i : Fin 2) {a b : Fin 2 ⊕ Fin 2} (h : E F (.positiveLong i) a b ≠ 0) :
    Sum.inl i = a ∧ Sum.inr i = b := by
  simp only [E, Matrix.single_apply] at h
  split_ifs at h with h1
  · exact h1
  · exact absurd rfl h

theorem E_negLong_supp (i : Fin 2) {a b : Fin 2 ⊕ Fin 2} (h : E F (.negativeLong i) a b ≠ 0) :
    Sum.inr i = a ∧ Sum.inl i = b := by
  simp only [E, Matrix.single_apply] at h
  split_ifs at h with h1
  · exact h1
  · exact absurd rfl h

theorem E_diff_supp (i j : Fin 2) (hij : i ≠ j) {a b : Fin 2 ⊕ Fin 2}
    (h : E F (.difference i j hij) a b ≠ 0) :
    (Sum.inl i = a ∧ Sum.inl j = b) ∨ (Sum.inr j = a ∧ Sum.inr i = b) := by
  simp only [E, Matrix.sub_apply, Matrix.single_apply] at h
  split_ifs at h with h1 h2 h2
  · exact Or.inl h1
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd (by simp) h

theorem E_posSum_supp (i j : Fin 2) (hij : i < j) {a b : Fin 2 ⊕ Fin 2}
    (h : E F (.positiveSum i j hij) a b ≠ 0) :
    (Sum.inl i = a ∧ Sum.inr j = b) ∨ (Sum.inl j = a ∧ Sum.inr i = b) := by
  simp only [E, Matrix.add_apply, Matrix.single_apply] at h
  split_ifs at h with h1 h2 h2
  · exact Or.inl h1
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd (by simp) h

theorem E_negSum_supp (i j : Fin 2) (hij : i < j) {a b : Fin 2 ⊕ Fin 2}
    (h : E F (.negativeSum i j hij) a b ≠ 0) :
    (Sum.inr i = a ∧ Sum.inl j = b) ∨ (Sum.inr j = a ∧ Sum.inl i = b) := by
  simp only [E, Matrix.add_apply, Matrix.single_apply] at h
  split_ifs at h with h1 h2 h2
  · exact Or.inl h1
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd (by simp) h


theorem mat_ut_Dι (ι : F) (hι : ι * ι = -1) :
    mat 2 F (ut (Dι ι hι) (Dι ι hι)) = Matrix.diagonal (Sum.elim ![ι, ι] ![-ι, -ι]) := by
  rw [mat_ut, coe_Dι]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> simp

theorem toral_sup_eq_top (ι : F) (hι : ι * ι = -1) :
    Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({ut (Dι ι hι) (Dι ι hι)} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({x0 F * ut (Dι ι hι) (Dι ι hι)} : Set (StatedSp 2 F)) = ⊤ := by
  apply eq_top_of_elt_mem
  intro r c
  have hmx := mat_x0 (F := F)
  have hmu := mat_ut_Dι ι hι
  have hmxu : mat 2 F (x0 F * ut (Dι ι hι) (Dι ι hι)) = Matrix.diagonal
      ((fun a => if a ∈ coords (n := 2) 0 then (-1 : F) else 1) * Sum.elim ![ι, ι] ![-ι, -ι]) := by
    rw [map_mul, hmx, hmu, Matrix.diagonal_mul_diagonal]
    rfl
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · refine Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (elt_mem_centralizer_of_diag _ c _ _ hmx fun a b hab => ?_))
    obtain ⟨rfl, rfl⟩ := E_posLong_supp i hab
    fin_cases i <;> simp [mem_coords]
  · refine Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (elt_mem_centralizer_of_diag _ c _ _ hmx fun a b hab => ?_))
    obtain ⟨rfl, rfl⟩ := E_negLong_supp i hab
    fin_cases i <;> simp [mem_coords]
  · refine Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (elt_mem_centralizer_of_diag _ c _ _ hmu fun a b hab => ?_))
    rcases E_diff_supp i j hij hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases i <;> fin_cases j <;>
      simp
  · refine Subgroup.mem_sup_right
      (elt_mem_centralizer_of_diag _ c _ _ hmxu fun a b hab => ?_)
    have hi : i = 0 := by fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
    have hj : j = 1 := by fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
    subst hi hj
    rcases E_posSum_supp 0 1 hij hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [mem_coords]
  · refine Subgroup.mem_sup_right
      (elt_mem_centralizer_of_diag _ c _ _ hmxu fun a b hab => ?_)
    have hi : i = 0 := by fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
    have hj : j = 1 := by fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)
    subst hi hj
    rcases E_negSum_supp 0 1 hij hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [mem_coords]

end CFSG.ClassicalInvolution.RouteD.SCRSp4
