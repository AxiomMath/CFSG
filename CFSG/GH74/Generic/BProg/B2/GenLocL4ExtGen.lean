module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtAux
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Subgroup Matrix Matrix.SpecialLinearGroup
open scoped commutatorElement

namespace GenLocL4Ext

variable {F : Type} [Field F]

theorem comm_mul_of_commute {G : Type*} [Group G] (x y z w : G) (hxy : Commute x y)
    (hyw : Commute y w) (hxz : ⁅x, z⁆ = w) : ⁅x, y * z⁆ = w := by
  have h1 : x * y = y * x := hxy.eq
  have h2 : y * w = w * y := hyw.eq
  rw [← hxz] at h2 ⊢
  simp only [commutatorElement_def] at h2 ⊢
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = (x * y) * z * x⁻¹ * z⁻¹ * y⁻¹ := by group
    _ = y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ := by rw [h1]; group
    _ = (x * z * x⁻¹ * z⁻¹) * y * y⁻¹ := by rw [h2]
    _ = x * z * x⁻¹ * z⁻¹ := by group

@[expose] def tv (i j : Fin 4) (h : i ≠ j) (t : F) : Matrix.SpecialLinearGroup (Fin 4) F :=
  transvection h t

@[expose] def u0 : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 0 2 (by decide) 1 * tv 1 3 (by decide) 1

@[expose] def u1 (c : F) : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 0 3 (by decide) c * tv 1 2 (by decide) 1

@[expose] def v0 : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 2 0 (by decide) 1 * tv 3 1 (by decide) 1

@[expose] def v1 (c : F) : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 2 1 (by decide) c * tv 3 0 (by decide) 1

theorem u0_comm (c : F) : ((u0 : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * i0 c =
    i0 c * (u0 : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold u0 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [i0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]

theorem u1_comm (c : F) : ((u1 c : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * i0 c =
    i0 c * (u1 c : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold u1 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [i0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]

theorem v0_comm (c : F) : ((v0 : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * i0 c =
    i0 c * (v0 : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold v0 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [i0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]

theorem v1_comm (c : F) : ((v1 c : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * i0 c =
    i0 c * (v1 c : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold v1 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [i0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]

theorem tv01_comm_xs (t : F) :
    ((tv 0 1 (by decide) t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * xs =
      (xs : Matrix (Fin 4) (Fin 4) F) *
        ((tv 0 1 (by decide) t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  unfold tv
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]

theorem tv10_comm_xs (t : F) :
    ((tv 1 0 (by decide) t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * xs =
      (xs : Matrix (Fin 4) (Fin 4) F) *
        ((tv 1 0 (by decide) t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  unfold tv
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]

theorem tv23_comm_xs (t : F) :
    ((tv 2 3 (by decide) t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * xs =
      (xs : Matrix (Fin 4) (Fin 4) F) *
        ((tv 2 3 (by decide) t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  unfold tv
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]

theorem tv32_comm_xs (t : F) :
    ((tv 3 2 (by decide) t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * xs =
      (xs : Matrix (Fin 4) (Fin 4) F) *
        ((tv 3 2 (by decide) t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  unfold tv
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]

theorem comm_01_u0 (a : F) : ⁅tv 0 1 (by decide) a, (u0 : Matrix.SpecialLinearGroup (Fin 4) F)⁆ =
    tv 0 3 (by decide) a := by
  unfold u0 tv
  refine comm_mul_of_commute _ _ _ _ ?_ ?_ ?_
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · rw [Matrix.SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) (by decide), mul_one]

theorem comm_01_u1 (c a : F) : ⁅tv 0 1 (by decide) a, (u1 c : Matrix.SpecialLinearGroup (Fin 4) F)⁆ =
    tv 0 2 (by decide) a := by
  unfold u1 tv
  refine comm_mul_of_commute _ _ _ _ ?_ ?_ ?_
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · rw [Matrix.SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) (by decide), mul_one]

theorem u0_swap : (u0 : Matrix.SpecialLinearGroup (Fin 4) F) =
    tv 1 3 (by decide) 1 * tv 0 2 (by decide) 1 := by
  unfold u0 tv
  exact (Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _).eq

theorem u1_swap (c : F) : (u1 c : Matrix.SpecialLinearGroup (Fin 4) F) =
    tv 1 2 (by decide) 1 * tv 0 3 (by decide) c := by
  unfold u1 tv
  exact (Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _).eq

theorem v0_swap : (v0 : Matrix.SpecialLinearGroup (Fin 4) F) =
    tv 3 1 (by decide) 1 * tv 2 0 (by decide) 1 := by
  unfold v0 tv
  exact (Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _).eq

theorem v1_swap (c : F) : (v1 c : Matrix.SpecialLinearGroup (Fin 4) F) =
    tv 3 0 (by decide) 1 * tv 2 1 (by decide) c := by
  unfold v1 tv
  exact (Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _).eq

theorem comm_10_u0 (a : F) : ⁅tv 1 0 (by decide) a, (u0 : Matrix.SpecialLinearGroup (Fin 4) F)⁆ =
    tv 1 2 (by decide) a := by
  rw [u0_swap]
  unfold tv
  refine comm_mul_of_commute _ _ _ _ ?_ ?_ ?_
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · rw [Matrix.SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) (by decide), mul_one]

theorem comm_10_u1 (c a : F) : ⁅tv 1 0 (by decide) a, (u1 c : Matrix.SpecialLinearGroup (Fin 4) F)⁆ =
    tv 1 3 (by decide) (a * c) := by
  rw [u1_swap]
  unfold tv
  refine comm_mul_of_commute _ _ _ _ ?_ ?_ ?_
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · rw [Matrix.SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) (by decide)]

theorem comm_23_v0 (a : F) : ⁅tv 2 3 (by decide) a, (v0 : Matrix.SpecialLinearGroup (Fin 4) F)⁆ =
    tv 2 1 (by decide) a := by
  unfold v0 tv
  refine comm_mul_of_commute _ _ _ _ ?_ ?_ ?_
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · rw [Matrix.SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) (by decide), mul_one]

theorem comm_23_v1 (c a : F) : ⁅tv 2 3 (by decide) a, (v1 c : Matrix.SpecialLinearGroup (Fin 4) F)⁆ =
    tv 2 0 (by decide) a := by
  unfold v1 tv
  refine comm_mul_of_commute _ _ _ _ ?_ ?_ ?_
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · rw [Matrix.SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) (by decide), mul_one]

theorem comm_32_v0 (a : F) : ⁅tv 3 2 (by decide) a, (v0 : Matrix.SpecialLinearGroup (Fin 4) F)⁆ =
    tv 3 0 (by decide) a := by
  rw [v0_swap]
  unfold tv
  refine comm_mul_of_commute _ _ _ _ ?_ ?_ ?_
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · rw [Matrix.SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) (by decide), mul_one]

theorem comm_32_v1 (c a : F) : ⁅tv 3 2 (by decide) a, (v1 c : Matrix.SpecialLinearGroup (Fin 4) F)⁆ =
    tv 3 1 (by decide) (a * c) := by
  rw [v1_swap]
  unfold tv
  refine comm_mul_of_commute _ _ _ _ ?_ ?_ ?_
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · exact Matrix.SpecialLinearGroup.commute_transvection (by decide) (by decide) (by decide) (by decide) _ _
  · rw [Matrix.SpecialLinearGroup.commutatorElement_transvection (by decide) (by decide) (by decide)]

theorem eq_top_of_centralizers_std (c : F) (hc : c ≠ 0)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (hI : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * i0 c = i0 c * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (hX : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * xs = xs * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    Γ = ⊤ := by
  have hcomm : ∀ {x U : Matrix.SpecialLinearGroup (Fin 4) F}, x ∈ Γ → U ∈ Γ → ⁅x, U⁆ ∈ Γ := by
    intro x U hx hU
    rw [commutatorElement_def]
    exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hx hU) (Γ.inv_mem hx)) (Γ.inv_mem hU)
  have e01 : ∀ t : F, tv 0 1 (by decide) t ∈ Γ := fun t => hX _ (tv01_comm_xs t)
  have e10 : ∀ t : F, tv 1 0 (by decide) t ∈ Γ := fun t => hX _ (tv10_comm_xs t)
  have e23 : ∀ t : F, tv 2 3 (by decide) t ∈ Γ := fun t => hX _ (tv23_comm_xs t)
  have e32 : ∀ t : F, tv 3 2 (by decide) t ∈ Γ := fun t => hX _ (tv32_comm_xs t)
  have hu0 : (u0 : Matrix.SpecialLinearGroup (Fin 4) F) ∈ Γ := hI _ (u0_comm c)
  have hu1 : (u1 c : Matrix.SpecialLinearGroup (Fin 4) F) ∈ Γ := hI _ (u1_comm c)
  have hv0 : (v0 : Matrix.SpecialLinearGroup (Fin 4) F) ∈ Γ := hI _ (v0_comm c)
  have hv1 : (v1 c : Matrix.SpecialLinearGroup (Fin 4) F) ∈ Γ := hI _ (v1_comm c)
  have e03 : ∀ t : F, tv 0 3 (by decide) t ∈ Γ := fun t => by
    rw [← comm_01_u0 t]; exact hcomm (e01 t) hu0
  have e02 : ∀ t : F, tv 0 2 (by decide) t ∈ Γ := fun t => by
    rw [← comm_01_u1 c t]; exact hcomm (e01 t) hu1
  have e12 : ∀ t : F, tv 1 2 (by decide) t ∈ Γ := fun t => by
    rw [← comm_10_u0 t]; exact hcomm (e10 t) hu0
  have e13 : ∀ t : F, tv 1 3 (by decide) t ∈ Γ := fun t => by
    have h := comm_10_u1 c (t / c)
    rw [div_mul_cancel₀ t hc] at h
    rw [← h]; exact hcomm (e10 _) hu1
  have e21 : ∀ t : F, tv 2 1 (by decide) t ∈ Γ := fun t => by
    rw [← comm_23_v0 t]; exact hcomm (e23 t) hv0
  have e20 : ∀ t : F, tv 2 0 (by decide) t ∈ Γ := fun t => by
    rw [← comm_23_v1 c t]; exact hcomm (e23 t) hv1
  have e30 : ∀ t : F, tv 3 0 (by decide) t ∈ Γ := fun t => by
    rw [← comm_32_v0 t]; exact hcomm (e32 t) hv0
  have e31 : ∀ t : F, tv 3 1 (by decide) t ∈ Γ := fun t => by
    have h := comm_32_v1 c (t / c)
    rw [div_mul_cancel₀ t hc] at h
    rw [← h]; exact hcomm (e32 _) hv1
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (K := F) (n := 4),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, t, rfl⟩
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact e01 t | exact e02 t | exact e03 t | exact e10 t | exact e12 t | exact e13 t
    | exact e20 t | exact e21 t | exact e23 t | exact e30 t | exact e31 t | exact e32 t

theorem conj_mul_conj (B : GL (Fin 4) F) (X Y : Matrix (Fin 4) (Fin 4) F) :
    ((B : Matrix (Fin 4) (Fin 4) F) * X * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) *
        ((B : Matrix (Fin 4) (Fin 4) F) * Y * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) =
      (B : Matrix (Fin 4) (Fin 4) F) * (X * Y) * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  have h1 : ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) = 1 :=
    B.inv_mul
  calc _ = (B : Matrix (Fin 4) (Fin 4) F) * X *
        (((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F)) * Y *
        ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem eq_top_of_centralizers (c : F) (hc : c ≠ 0) (B : GL (Fin 4) F)
    (i x : Matrix (Fin 4) (Fin 4) F) (hi : i * (B : Matrix (Fin 4) (Fin 4) F) = (B : Matrix (Fin 4) (Fin 4) F) * i0 c)
    (hx : x * (B : Matrix (Fin 4) (Fin 4) F) = (B : Matrix (Fin 4) (Fin 4) F) * xs)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (hΓi : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * i = i * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (hΓx : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    Γ = ⊤ := by
  have hi' : i = (B : Matrix (Fin 4) (Fin 4) F) * i0 c * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [← hi, Units.mul_inv_cancel_right]
  have hx' : x = (B : Matrix (Fin 4) (Fin 4) F) * xs * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [← hx, Units.mul_inv_cancel_right]
  let φ : Matrix.SpecialLinearGroup (Fin 4) F →* Matrix.SpecialLinearGroup (Fin 4) F :=
    (CatalogueBHigherLinearAction.slConjugation 4 F B : MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
  have hφ : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F, ((φ g : Matrix.SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = (B : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
        ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := fun g =>
    LinearFlag.coe_slConjugation B g
  have h0 : Γ.comap φ = ⊤ := by
    refine eq_top_of_centralizers_std c hc (Γ.comap φ) (fun g hg => ?_) (fun g hg => ?_)
    · refine hΓi (φ g) ?_
      rw [hφ, hi', conj_mul_conj, conj_mul_conj, hg]
    · refine hΓx (φ g) ?_
      rw [hφ, hx', conj_mul_conj, conj_mul_conj, hg]
  rw [eq_top_iff]
  intro h _
  have h1 : (CatalogueBHigherLinearAction.slConjugation 4 F B⁻¹ h) ∈ Γ.comap φ := by
    rw [h0]; exact mem_top _
  have h2 : φ (CatalogueBHigherLinearAction.slConjugation 4 F B⁻¹ h) = h := by
    show (CatalogueBHigherLinearAction.slConjugation 4 F B)
      ((CatalogueBHigherLinearAction.slConjugation 4 F B⁻¹) h) = h
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [← h2]
  exact h1

end GenLocL4Ext

end CFSG.GH74.Generic.BProg.B2
