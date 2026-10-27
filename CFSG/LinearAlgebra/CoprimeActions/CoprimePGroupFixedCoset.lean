module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset

open MulAction

variable {B X : Type*} [Group B] [Group X]

@[expose] def Coset (R : Subgroup X) (x : X) : Type _ := {y : X // y * x⁻¹ ∈ R}

theorem natCard_coset (R : Subgroup X) (x : X) : Nat.card (Coset R x) = Nat.card R := by
  apply Nat.card_congr
  exact
    { toFun := fun y => ⟨y.1 * x⁻¹, y.2⟩
      invFun := fun r => ⟨r.1 * x, by simpa using r.2⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun r => Subtype.ext (by simp) }

@[expose, instance_reducible] noncomputable def cosetAction (ρ : B →* MulAut X) (R : Subgroup X)
    (hR : ∀ b, ∀ r ∈ R, ρ b r ∈ R) (x : X) (hx : ∀ b, ρ b x * x⁻¹ ∈ R) :
    MulAction B (Coset R x) where
  smul b y := ⟨ρ b y.1, by
    have h : ρ b y.1 * x⁻¹ = ρ b (y.1 * x⁻¹) * (ρ b x * x⁻¹) := by
      simp [mul_assoc]
    rw [h]; exact R.mul_mem (hR b _ y.2) (hx b)⟩
  one_smul y := by apply Subtype.ext; simp [HSMul.hSMul]
  mul_smul a b y := by apply Subtype.ext; simp [HSMul.hSMul]

theorem exists_fixed {p : ℕ} [Fact p.Prime] [Finite B] [Finite X]
    (hB : IsPGroup p B) (ρ : B →* MulAut X) (R : Subgroup X) (_hRn : R.Normal)
    (hR : ∀ b, ∀ r ∈ R, ρ b r ∈ R) (hp : ¬ p ∣ Nat.card R)
    (x : X) (hx : ∀ b, ρ b x * x⁻¹ ∈ R) :
    ∃ y : X, y * x⁻¹ ∈ R ∧ ∀ b, ρ b y = y := by
  letI := cosetAction ρ R hR x hx
  haveI : Finite (Coset R x) := Subtype.finite
  have h := hB.card_modEq_card_fixedPoints (Coset R x)
  rw [natCard_coset] at h
  have hne : Nat.card (fixedPoints B (Coset R x)) ≠ 0 := by
    intro h0
    rw [h0] at h
    exact hp ((Nat.modEq_zero_iff_dvd).mp h)
  have : Nonempty (fixedPoints B (Coset R x)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    simp at hne
  obtain ⟨y, hyf⟩ := this
  refine ⟨y.1, y.2, fun b => ?_⟩
  have := congrArg Subtype.val (hyf b)
  exact this

end CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset
