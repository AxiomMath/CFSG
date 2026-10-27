module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup Matrix Matrix.SpecialLinearGroup
open scoped commutatorElement

namespace GenLocL4Q

variable {F : Type} [Field F]

@[expose] def tv (i j : Fin 4) (h : i ≠ j) (t : F) : Matrix.SpecialLinearGroup (Fin 4) F :=
  SpecialLinearGroup.transvection h t

@[expose] def Xr (c : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, c, 0, 0; 1, 0, 0, 0; 0, 0, 0, c; 0, 0, 1, 0]

@[expose] def Yr (m : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, m, 0; 0, 0, 0, -m; 1, 0, 0, 0; 0, -1, 0, 0]

theorem Xr_mul_Xr (c : F) : Xr c * Xr c = c • (1 : Matrix (Fin 4) (Fin 4) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xr, Matrix.mul_apply, Fin.sum_univ_four]

theorem Yr_mul_Yr (m : F) : Yr m * Yr m = m • (1 : Matrix (Fin 4) (Fin 4) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Yr, Matrix.mul_apply, Fin.sum_univ_four]

theorem Xr_mul_Yr (c m : F) : Xr c * Yr m = -(Yr m * Xr c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xr, Yr, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

@[expose] def a1 (s : F) : Matrix.SpecialLinearGroup (Fin 4) F := tv 0 2 (by decide) s * tv 1 3 (by decide) s

@[expose] def a2 (c t : F) : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 0 3 (by decide) (t * c) * tv 1 2 (by decide) t

@[expose] def l1 (s : F) : Matrix.SpecialLinearGroup (Fin 4) F := tv 2 0 (by decide) s * tv 3 1 (by decide) s

@[expose] def l2 (c t : F) : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 2 1 (by decide) (t * c) * tv 3 0 (by decide) t

@[expose] def b1 (a : F) : Matrix.SpecialLinearGroup (Fin 4) F := tv 0 1 (by decide) a * tv 2 3 (by decide) (-a)

@[expose] def b2 (c a : F) : Matrix.SpecialLinearGroup (Fin 4) F :=
  tv 0 1 (by decide) a * tv 3 2 (by decide) (-(a / c))

theorem a1_comm (c s : F) : ((a1 s : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Xr c =
    Xr c * (a1 s : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold a1 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals ring

theorem a2_comm (c t : F) : ((a2 c t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Xr c =
    Xr c * (a2 c t : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold a2 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals ring

theorem l1_comm (c s : F) : ((l1 s : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Xr c =
    Xr c * (l1 s : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold l1 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals ring

theorem l2_comm (c t : F) : ((l2 c t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Xr c =
    Xr c * (l2 c t : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold l2 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals ring

theorem b1_comm (m a : F) : ((b1 a : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Yr m =
    Yr m * (b1 a : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold b1 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Yr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals ring

theorem b2_comm (c m a : F) (hc : c ≠ 0) :
    ((b2 c a : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (Xr c * Yr m) =
    (Xr c * Yr m) * (b2 c a : Matrix.SpecialLinearGroup (Fin 4) F) := by
  unfold b2 tv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Xr, Yr, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals field_simp

theorem b1_a1 (a s : F) :
    b1 a * a1 s = tv 0 3 (by decide) (2 * a * s) * (a1 s * b1 a) := by
  unfold b1 a1 tv
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals ring

theorem b2_a1 (c a s : F) (hc : c ≠ 0) :
    b2 c a * a1 s = (tv 0 3 (by decide) (s * a) * tv 1 2 (by decide) (s * a / c) *
      tv 0 2 (by decide) (s * a ^ 2 / c)) * (a1 s * b2 c a) := by
  unfold b2 a1 tv
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals (try field_simp)
  all_goals ring

theorem b1_l1 (a s : F) :
    b1 a * l1 s = tv 2 1 (by decide) (-(2 * a * s)) * (l1 s * b1 a) := by
  unfold b1 l1 tv
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals ring

theorem b2_l1 (c a s : F) (hc : c ≠ 0) :
    b2 c a * l1 s = (tv 2 1 (by decide) (-(s * a)) * tv 3 0 (by decide) (-(s * a / c)) *
      tv 3 1 (by decide) (s * a ^ 2 / c)) * (l1 s * b2 c a) := by
  unfold b2 l1 tv
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.add_apply]
  all_goals (try field_simp)
  all_goals ring

theorem mem_of_mul_eq {G : Type*} [Group G] (Γ : Subgroup G) {g h u : G} (hg : g ∈ Γ) (hh : h ∈ Γ)
    (e : g * h = u * (h * g)) : u ∈ Γ := by
  have : u = g * h * (h * g)⁻¹ := by rw [e]; group
  rw [this]
  exact Γ.mul_mem (Γ.mul_mem hg hh) (Γ.inv_mem (Γ.mul_mem hh hg))

theorem comm_tv {i j l : Fin 4} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (a b : F) :
    ⁅tv i j hij a, tv j l hjl b⁆ = tv i l hil (a * b) :=
  SpecialLinearGroup.commutatorElement_transvection hij hjl hil a b

theorem comm_mem {G : Type*} [Group G] (Γ : Subgroup G) {g h : G} (hg : g ∈ Γ) (hh : h ∈ Γ) :
    ⁅g, h⁆ ∈ Γ := by
  rw [commutatorElement_def]
  exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hg hh) (Γ.inv_mem hg)) (Γ.inv_mem hh)

theorem top_of_generators (h2 : (2 : F) ≠ 0) {c : F} (hc : c ≠ 0)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (hA1 : ∀ s, a1 s ∈ Γ) (hA2 : ∀ t, a2 c t ∈ Γ) (hL1 : ∀ s, l1 s ∈ Γ) (hL2 : ∀ t, l2 c t ∈ Γ)
    (hB1 : ∀ a, b1 a ∈ Γ) (hB2 : ∀ a, b2 c a ∈ Γ) : Γ = ⊤ := by
  have e03 : ∀ t : F, tv 0 3 (by decide) t ∈ Γ := fun t => by
    have key := mem_of_mul_eq Γ (hB1 1) (hA1 (t / 2)) (b1_a1 (F := F) 1 (t / 2))
    have hh : (2 : F) * 1 * (t / 2) = t := by field_simp
    rwa [hh] at key
  have e12 : ∀ t : F, tv 1 2 (by decide) t ∈ Γ := fun t => by
    have key := Γ.mul_mem (Γ.inv_mem (e03 (t * c))) (hA2 t)
    simpa only [a2, inv_mul_cancel_left] using key
  have e02 : ∀ u : F, tv 0 2 (by decide) u ∈ Γ := fun u => by
    have key := mem_of_mul_eq Γ (hB2 1) (hA1 (u * c)) (b2_a1 c 1 (u * c) hc)
    have key2 := Γ.mul_mem (Γ.inv_mem (Γ.mul_mem (e03 (u * c * 1)) (e12 (u * c * 1 / c)))) key
    simp only [inv_mul_cancel_left] at key2
    have hh : u * c * 1 ^ 2 / c = u := by field_simp
    rwa [hh] at key2
  have e13 : ∀ s : F, tv 1 3 (by decide) s ∈ Γ := fun s => by
    have key := Γ.mul_mem (Γ.inv_mem (e02 s)) (hA1 s)
    simpa only [a1, inv_mul_cancel_left] using key
  have e21 : ∀ t : F, tv 2 1 (by decide) t ∈ Γ := fun t => by
    have key := mem_of_mul_eq Γ (hB1 1) (hL1 (-t / 2)) (b1_l1 (F := F) 1 (-t / 2))
    have hh : -(2 * 1 * (-t / 2)) = t := by field_simp
    rwa [hh] at key
  have e30 : ∀ t : F, tv 3 0 (by decide) t ∈ Γ := fun t => by
    have key := Γ.mul_mem (Γ.inv_mem (e21 (t * c))) (hL2 t)
    simpa only [l2, inv_mul_cancel_left] using key
  have e31 : ∀ u : F, tv 3 1 (by decide) u ∈ Γ := fun u => by
    have key := mem_of_mul_eq Γ (hB2 1) (hL1 (u * c)) (b2_l1 c 1 (u * c) hc)
    have key2 := Γ.mul_mem (Γ.inv_mem (Γ.mul_mem (e21 (-(u * c * 1))) (e30 (-(u * c * 1 / c))))) key
    simp only [inv_mul_cancel_left] at key2
    have hh : u * c * 1 ^ 2 / c = u := by field_simp
    rwa [hh] at key2
  have e20 : ∀ s : F, tv 2 0 (by decide) s ∈ Γ := fun s => by
    have key := Γ.mul_mem (hL1 s) (Γ.inv_mem (e31 s))
    simpa only [l1, mul_inv_cancel_right] using key
  have e01 : ∀ t : F, tv 0 1 (by decide) t ∈ Γ := fun t => by
    have key := comm_mem Γ (e02 t) (e21 1)
    rw [comm_tv (by decide) (by decide) (by decide), mul_one] at key
    exact key
  have e10 : ∀ t : F, tv 1 0 (by decide) t ∈ Γ := fun t => by
    have key := comm_mem Γ (e12 t) (e20 1)
    rw [comm_tv (by decide) (by decide) (by decide), mul_one] at key
    exact key
  have e23 : ∀ t : F, tv 2 3 (by decide) t ∈ Γ := fun t => by
    have key := comm_mem Γ (e20 t) (e03 1)
    rw [comm_tv (by decide) (by decide) (by decide), mul_one] at key
    exact key
  have e32 : ∀ t : F, tv 3 2 (by decide) t ∈ Γ := fun t => by
    have key := comm_mem Γ (e31 t) (e12 1)
    rw [comm_tv (by decide) (by decide) (by decide), mul_one] at key
    exact key
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (K := F) (n := 4),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, t, rfl⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact e01 t | exact e02 t | exact e03 t | exact e10 t | exact e12 t | exact e13 t
    | exact e20 t | exact e21 t | exact e23 t | exact e30 t | exact e31 t | exact e32 t

theorem eq_top_of_centralizers (h2 : (2 : F) ≠ 0) {c m : F} (hc : c ≠ 0)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (hX : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Xr c = Xr c * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (hY : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * Yr m = Yr m * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (hXY : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * (Xr c * Yr m) = (Xr c * Yr m) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ Γ) : Γ = ⊤ :=
  top_of_generators h2 hc Γ (fun s => hX _ (a1_comm c s)) (fun t => hX _ (a2_comm c t))
    (fun s => hX _ (l1_comm c s)) (fun t => hX _ (l2_comm c t)) (fun a => hY _ (b1_comm m a))
    (fun a => hXY _ (b2_comm c m a hc))

end GenLocL4Q

end CFSG.GH74.Generic.BProg.B2
