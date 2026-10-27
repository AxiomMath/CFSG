module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedInteger

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFiveFixed

open CFSG.Wreathed.ConditionalFourier

variable {ι : Type*} [DecidableEq ι]

theorem sum_cast_unitVector_mul {B : Finset ι} {q : ι} (hq : q ∈ B) (F : ι → ℂ) :
    ∑ φ ∈ B, ((unitVector q φ : ℤ) : ℂ) * F φ = F q := by
  simp only [unitVector, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' B q, ite_eq_left_iff.mpr fun h => absurd hq h]

theorem sum_cast_lincomb_mul {κ₁ : Type*} [Fintype κ₁] {B : Finset ι} {g : κ₁ → ι}
    (hg : ∀ l, g l ∈ B) (a : κ₁ → ℤ) (F : ι → ℂ) :
    ∑ φ ∈ B, ((∑ l, a l * unitVector (g l) φ : ℤ) : ℂ) * F φ = ∑ l, (a l : ℂ) * F (g l) := by
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : ∀ φ, (a l : ℂ) * ((unitVector (g l) φ : ℤ) : ℂ) * F φ =
      (a l : ℂ) * (((unitVector (g l) φ : ℤ) : ℂ) * F φ) := fun φ => by ring
  rw [Finset.sum_congr rfl fun φ _ => h φ, ← Finset.mul_sum, sum_cast_unitVector_mul (hg l)]

theorem sum_cast_four_mul {B : Finset ι} {q₁ q₂ q₃ q₄ : ι} (h₁ : q₁ ∈ B) (h₂ : q₂ ∈ B)
    (h₃ : q₃ ∈ B) (h₄ : q₄ ∈ B) (a₁ a₂ a₃ a₄ : ℤ) (F : ι → ℂ) :
    ∑ φ ∈ B, ((a₁ * unitVector q₁ φ + a₂ * unitVector q₂ φ + a₃ * unitVector q₃ φ +
      a₄ * unitVector q₄ φ : ℤ) : ℂ) * F φ =
      a₁ * F q₁ + a₂ * F q₂ + a₃ * F q₃ + a₄ * F q₄ := by
  have h := sum_cast_lincomb_mul (B := B) (g := ![q₁, q₂, q₃, q₄])
    (fun l => by fin_cases l <;> simpa) ![a₁, a₂, a₃, a₄] F
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h
  simpa using h

theorem sum_cast_five_mul {B : Finset ι} {q₁ q₂ q₃ q₄ q₅ : ι} (h₁ : q₁ ∈ B) (h₂ : q₂ ∈ B)
    (h₃ : q₃ ∈ B) (h₄ : q₄ ∈ B) (h₅ : q₅ ∈ B) (a₁ a₂ a₃ a₄ a₅ : ℤ) (F : ι → ℂ) :
    ∑ φ ∈ B, ((a₁ * unitVector q₁ φ + a₂ * unitVector q₂ φ + a₃ * unitVector q₃ φ +
      a₄ * unitVector q₄ φ + a₅ * unitVector q₅ φ : ℤ) : ℂ) * F φ =
      a₁ * F q₁ + a₂ * F q₂ + a₃ * F q₃ + a₄ * F q₄ + a₅ * F q₅ := by
  have h := sum_cast_lincomb_mul (B := B) (g := ![q₁, q₂, q₃, q₄, q₅])
    (fun l => by fin_cases l <;> simpa) ![a₁, a₂, a₃, a₄, a₅] F
  simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h
  simpa using h


theorem sum_cast_fixedPart_mul {B : Finset ι} {p A Bq Dq : ι} (hp : p ∈ B) (hA : A ∈ B)
    (hBq : Bq ∈ B) (hDq : Dq ∈ B) (σ τ₀ κ : ℤ) (F : ι → ℂ) :
    ∑ φ ∈ B, ((fixedPart p A Bq Dq σ τ₀ κ φ : ℤ) : ℂ) * F φ =
      -F p - σ * F A - τ₀ * F Bq + κ * F Dq := by
  have h : ∀ φ, ((fixedPart p A Bq Dq σ τ₀ κ φ : ℤ) : ℂ) = (((-1) * unitVector p φ +
      (-σ) * unitVector A φ + (-τ₀) * unitVector Bq φ + κ * unitVector Dq φ : ℤ) : ℂ) :=
    fun φ => by rw [fixedPart]; push_cast; ring
  rw [Finset.sum_congr rfl fun φ _ => by rw [h φ], sum_cast_four_mul hp hA hBq hDq]
  push_cast
  ring

theorem exists_orbit_representatives {K X : Type*} [Group K] [MulAction K X] [Fintype X]
    [DecidableEq X] (P : Set X → Prop) :
    ∃ V : Finset X, (∀ I ∈ V, P (MulAction.orbit K I)) ∧
      ∀ I, P (MulAction.orbit K I) → ∃! J, J ∈ V ∧ J ∈ MulAction.orbit K I := by
  classical
  let rep : X → X := fun I =>
    Classical.choose (⟨I, MulAction.mem_orbit_self I⟩ : ∃ J, J ∈ MulAction.orbit K I)
  have hrep : ∀ I, rep I ∈ MulAction.orbit K I := fun I =>
    Classical.choose_spec (⟨I, MulAction.mem_orbit_self I⟩ : ∃ J, J ∈ MulAction.orbit K I)
  have hchoose : ∀ (s t : Set X) (h₁ : ∃ J, J ∈ s) (h₂ : ∃ J, J ∈ t), s = t →
      Classical.choose h₁ = Classical.choose h₂ := by
    rintro s t h₁ h₂ rfl
    rfl
  have hrep_eq : ∀ I I', MulAction.orbit K I = MulAction.orbit K I' → rep I = rep I' :=
    fun I I' h => hchoose _ _ _ _ h
  have horb : ∀ I, MulAction.orbit K (rep I) = MulAction.orbit K I := fun I =>
    MulAction.orbit_eq_iff.mpr (hrep I)
  refine ⟨(Finset.univ.filter fun I => P (MulAction.orbit K I)).image rep, ?_, ?_⟩
  · intro J hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    rw [horb]
    exact (Finset.mem_filter.mp hI).2
  · intro I hI
    refine ⟨rep I, ⟨Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI⟩,
      rfl⟩, hrep I⟩, ?_⟩
    rintro J ⟨hJV, hJI⟩
    obtain ⟨I₀, -, rfl⟩ := Finset.mem_image.mp hJV
    apply hrep_eq
    rw [← horb I₀]
    exact MulAction.orbit_eq_iff.mpr hJI

end CFSG.Wreathed.ConditionalFiveFixed
