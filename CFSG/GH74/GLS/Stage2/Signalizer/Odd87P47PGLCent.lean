module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47PGLMat
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47PGL

open Subgroup Matrix
open scoped MatrixGroups commutatorElement

section PGL

variable {F : Type} [Field F]

open Matrix.ProjGenLinGroup in
theorem comm_of_mk_comm (hcube : ∀ c : Fˣ, c ^ 3 = 1) {G X : GL (Fin 3) F} (hX : X * X = 1)
    (h : ProjGenLinGroup.mk G * ProjGenLinGroup.mk X = ProjGenLinGroup.mk X * ProjGenLinGroup.mk G) :
    G * X = X * G := by
  have hk1 : ProjGenLinGroup.mk ⁅G, X⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hk1
  obtain ⟨u, hu⟩ := hk1
  set k : GL (Fin 3) F := ⁅G, X⁆ with hk
  have hkc : ∀ A : GL (Fin 3) F, k * A = A * k := fun A => by
    rw [← hu]
    exact GeneralLinearGroup.scalar_commute u A
  have hGX : G * X * G⁻¹ = k * X := by
    rw [hk, commutatorElement_def]
    group
  have hsq : (G * X * G⁻¹) * (G * X * G⁻¹) = 1 := by
    calc (G * X * G⁻¹) * (G * X * G⁻¹) = G * (X * X) * G⁻¹ := by group
      _ = 1 := by rw [hX]; group
  rw [hGX] at hsq
  have hk2 : k * k = 1 := by
    have h3 : k * X * (k * X) = k * k := by
      calc k * X * (k * X) = k * (X * k) * X := by simp only [mul_assoc]
        _ = k * (k * X) * X := by rw [← hkc X]
        _ = k * k * (X * X) := by simp only [mul_assoc]
        _ = k * k := by rw [hX, mul_one]
    rw [← h3]
    exact hsq
  have hk3 : k * (k * k) = 1 := by
    have : k ^ 3 = 1 := by rw [← hu, ← map_pow, hcube u, map_one]
    rw [← this]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hk1' : k = 1 := by
    rw [hk2, mul_one] at hk3
    exact hk3
  exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [← hk]; exact hk1')

open Matrix.ProjGenLinGroup in
theorem sq_eq_one_of_comm (h2 : (2 : F) = 0) (hcube : ∀ c : Fˣ, c ^ 3 = 1)
    {g : ProjGenLinGroup (Fin 3) F} (h1 : g * mk (x12GL (1 : F)) = mk (x12GL 1) * g)
    (h1' : g * mk (x23GL (1 : F)) = mk (x23GL 1) * g) : g ^ 2 = 1 := by
  obtain ⟨G, rfl⟩ := mk_surjective g
  have c1 := comm_of_mk_comm hcube (x12GL_sq h2) h1
  have c2 := comm_of_mk_comm hcube (x23GL_sq h2) h1'
  have m1 : G.val * x12 1 = x12 1 * G.val := congrArg Units.val c1
  have m2 : G.val * x23 1 = x23 1 * G.val := congrArg Units.val c2
  have e01 := congrFun (congrFun m1 0) 1
  have e11 := congrFun (congrFun m1 1) 1
  have e21 := congrFun (congrFun m1 2) 1
  have e02 := congrFun (congrFun m1 0) 2
  have f12 := congrFun (congrFun m2 1) 2
  have f02 := congrFun (congrFun m2 0) 2
  have f22 := congrFun (congrFun m2 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, x12] at e01 e11 e21 e02
  simp [Matrix.mul_apply, Fin.sum_univ_three, x23] at f12 f02 f22
  have a01 : G.val 0 0 = G.val 1 1 := by
    linear_combination e01
  have a12 : G.val 1 1 = G.val 2 2 := by
    linear_combination f12
  have hsq : G.val * G.val = (G.val 0 0 * G.val 0 0) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, e11, e21, e02, f02, f22, ← a01, ← a12]
    all_goals linear_combination (G.val 0 0 * G.val 0 2) * h2
  have hGG : ((G * G : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (G.val 0 0 * G.val 0 0) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [Units.val_mul]
    exact hsq
  have hcen : G * G ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Subgroup.mem_center_iff]
    intro A
    apply Units.ext
    rw [Units.val_mul A (G * G), Units.val_mul (G * G) A, hGG, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  rw [pow_two, ← map_mul, ProjGenLinGroup.mk_eq_one]
  exact hcen

end PGL

section V

variable {F : Type} [Field F]

open Matrix.ProjGenLinGroup in
@[expose] noncomputable def vSub (F : Type) [Field F] : Subgroup (ProjGenLinGroup (Fin 3) F) :=
  Subgroup.closure {ProjGenLinGroup.mk (x12GL (1 : F)), ProjGenLinGroup.mk (x23GL (1 : F))}

open Matrix.ProjGenLinGroup in
theorem mk_x12_mem_vSub : ProjGenLinGroup.mk (x12GL (1 : F)) ∈ vSub F :=
  Subgroup.subset_closure (Set.mem_insert _ _)

open Matrix.ProjGenLinGroup in
theorem mk_x23_mem_vSub : ProjGenLinGroup.mk (x23GL (1 : F)) ∈ vSub F :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

open Matrix.ProjGenLinGroup in
theorem vSub_le_commutator [Finite F] (hF : Nat.card F = 4) :
    vSub F ≤ ⁅(⊤ : Subgroup (ProjGenLinGroup (Fin 3) F)), ⊤⁆ := by
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_one_of_card_four hF
  have hne : a - 1 ≠ 0 := sub_ne_zero.2 ha1
  set t : F := (a - 1)⁻¹ with ht
  have hat : a * t = 1 + t := by
    rw [ht]
    field_simp
    ring
  rw [vSub, Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | hy
  · have hm : ProjGenLinGroup.mk (x12GL (1 : F)) =
        ⁅ProjGenLinGroup.mk (dg1GL a ha0), ProjGenLinGroup.mk (x12GL t)⁆ := by
      rw [← map_commutatorElement, comm_dg1_x12 ha0 hat]
    rw [SetLike.mem_coe, hm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · rw [Set.mem_singleton_iff] at hy
    have hm : ProjGenLinGroup.mk (x23GL (1 : F)) =
        ⁅ProjGenLinGroup.mk (dg2GL a ha0), ProjGenLinGroup.mk (x23GL t)⁆ := by
      rw [← map_commutatorElement, comm_dg2_x23 ha0 hat]
    rw [hy, SetLike.mem_coe, hm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

open Matrix.ProjGenLinGroup in
theorem vSub_isPGroup [Finite F] (hF : Nat.card F = 4) : IsPGroup 2 (vSub F) := by
  have h2 := char_two_of_card_four hF
  have hU : IsPGroup 2 ((uniSub h2).map ProjGenLinGroup.mk) := (uniSub_isPGroup h2).map _
  refine hU.to_le ?_
  rw [vSub, Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | hy
  · exact ⟨x12GL 1, x12GL_mem_uniSub h2, rfl⟩
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact ⟨x23GL 1, x23GL_mem_uniSub h2, rfl⟩

end V

section Det

variable {F : Type} [Field F]

open Matrix.ProjGenLinGroup in
@[expose] noncomputable def detPGL (hcube : ∀ c : Fˣ, c ^ 3 = 1) :
    ProjGenLinGroup (Fin 3) F →* Fˣ :=
  ProjGenLinGroup.lift GeneralLinearGroup.det (by
    ext u
    simp [hcube u])

open Matrix.ProjGenLinGroup in
theorem detPGL_mk (hcube : ∀ c : Fˣ, c ^ 3 = 1) (g : GL (Fin 3) F) :
    detPGL hcube (ProjGenLinGroup.mk g) = GeneralLinearGroup.det g :=
  rfl

open Matrix.ProjGenLinGroup in
theorem commutator_pgl_ne_top [Finite F] (hF : Nat.card F = 4) :
    ⁅(⊤ : Subgroup (ProjGenLinGroup (Fin 3) F)), (⊤ : Subgroup (ProjGenLinGroup (Fin 3) F))⁆ ≠
      (⊤ : Subgroup (ProjGenLinGroup (Fin 3) F)) := by
  have hcube := cube_eq_one_of_card_four hF
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_one_of_card_four hF
  intro htop
  have hle : ⁅(⊤ : Subgroup (ProjGenLinGroup (Fin 3) F)), ⊤⁆ ≤ (detPGL hcube).ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  rw [htop] at hle
  have hmem : ProjGenLinGroup.mk (dg1GL a ha0) ∈ (detPGL hcube).ker :=
    hle (Subgroup.mem_top (ProjGenLinGroup.mk (dg1GL a ha0)))
  rw [MonoidHom.mem_ker, detPGL_mk] at hmem
  have h1 : (dg1 a).det = 1 := by
    have := congrArg Units.val hmem
    simpa [GeneralLinearGroup.val_det_apply, dg1GL] using this
  apply ha1
  simpa [dg1, Matrix.det_fin_three] using h1

end Det

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47PGL
