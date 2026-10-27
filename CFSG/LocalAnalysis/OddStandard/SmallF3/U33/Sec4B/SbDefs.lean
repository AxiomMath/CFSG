module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutDefs
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

variable {G : Type} [Group G]

@[expose] def ctxN (tau x₁ x₂ : G) : Subgroup G := closure {tau, x₁ ^ 2, (x₁ * x₂) ^ 2}

@[expose] def ctxO (t tau x₁ x₂ : G) : Subgroup G := CFSG.Open.pCoreOf 2 (ctxM t tau x₁ x₂)

@[expose] def ctxR (t tau x₁ x₂ : G) : Subgroup G where
  carrier := {g | g ∈ ctxM t tau x₁ x₂ ∧
    (∀ x ∈ ctxX t tau x₁ x₂, g * x * g⁻¹ * x⁻¹ ∈ fourGrp x₁ x₂) ∧
    ∀ v ∈ fourGrp x₁ x₂, g * v * g⁻¹ = v}
  mul_mem' := by
    rintro g h ⟨hgM, hgX, hgV⟩ ⟨hhM, hhX, hhV⟩
    refine ⟨mul_mem hgM hhM, fun x hx => ?_, fun v hv => ?_⟩
    · have h1 : g * h * x * (g * h)⁻¹ * x⁻¹ =
          (g * (h * x * h⁻¹ * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
      rw [h1, hgV _ (hhX x hx)]
      exact mul_mem (hhX x hx) (hgX x hx)
    · have h1 : g * h * v * (g * h)⁻¹ = g * (h * v * h⁻¹) * g⁻¹ := by group
      rw [h1, hhV v hv, hgV v hv]
  one_mem' := by
    refine ⟨one_mem _, fun x hx => ?_, fun v hv => ?_⟩
    · simp
    · simp
  inv_mem' := by
    rintro g ⟨hgM, hgX, hgV⟩
    refine ⟨inv_mem hgM, fun x hx => ?_, fun v hv => ?_⟩
    · have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ ctxX t tau x₁ x₂ :=
        (mem_normalizer_iff.mp (inv_mem hgM) x).mp hx
      have h2 := hgX _ hx'
      have h3 : g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ =
          (g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ * (g⁻¹ * x * g⁻¹⁻¹)⁻¹)⁻¹ := by group
      rw [h3]
      exact inv_mem h2
    · have := hgV v hv
      have h1 : g⁻¹ * v * g⁻¹⁻¹ = g⁻¹ * (g * v * g⁻¹) * g := by rw [this]; simp
      rw [h1]
      group

@[expose] def ctxQ (t tau x₁ x₂ rho : G) : Subgroup G := ⁅ctxO t tau x₁ x₂, zpowers rho⁆

@[expose] def ctxPhi (R : Subgroup G) : Subgroup G := (frattini ↥R).map R.subtype

@[expose] def ctxYq (t tau x₁ x₂ rho : G) : Subgroup G :=
  closure {g | g ∈ ctxQ t tau x₁ x₂ rho ∧ g ^ 2 = 1}

@[expose] def ctxU (t tau x₁ x₂ lam : G) : Subgroup G := ctxO t tau x₁ x₂ ⊔ zpowers lam

@[expose] def ctxK (t tau x₁ x₂ rho : G) : Subgroup G :=
  normalizer ((ctxQ t tau x₁ x₂ rho ⊔ closure {t, tau} : Subgroup G) : Set G)

@[expose] def IsZ4Z4E4 (Q : Subgroup G) : Prop := Nonempty (↥Q ≃* Outside.Z4Z4Z2Z2)

@[expose] def IsSylSL34 (Q : Subgroup G) : Prop := Nonempty (↥Q ≃* SylSL3_4)

@[expose] def IsZ4pow (n : ℕ) (P : Subgroup G) : Prop := Nonempty (↥P ≃* Outside.Z4pow n)

@[expose] def ctxCO (t tau x₁ x₂ rho : G) : Subgroup G :=
  ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G)

@[expose] def IsSylowIn (p : ℕ) (P K : Subgroup G) : Prop :=
  P ≤ K ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex K

@[expose] def CharIn (A B : Subgroup G) : Prop := A ≤ B ∧ (A.subgroupOf B).Characteristic

@[expose] def InvIn (A : Set G) : Set G := {u | u ∈ A ∧ u ^ 2 = 1 ∧ u ≠ 1}

end CFSG.OddStandard.SmallF3.HarrisU33
