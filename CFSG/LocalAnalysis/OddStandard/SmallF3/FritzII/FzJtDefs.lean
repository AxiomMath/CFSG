module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL36J

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

@[expose] def fzCalZ (x₁ x₂ lam : G) (T₂ : Subgroup G) : Set G :=
  {v | v ≠ 1 ∧ v ∈ fourGrp x₁ x₂} ∪ {v | ∃ h ∈ T₂, v = h * lam * h⁻¹}

@[expose] def FzJt (t : G) (T : Subgroup G) (x : G) : Prop :=
  ∃ v ∈ T ⊓ centralizer ({x} : Set G), ∃ w ∈ T ⊓ centralizer ({x} : Set G),
    v ^ 2 = 1 ∧ w ^ 2 = 1 ∧ v ≠ w ∧ v * w = w * v ∧ IsConj t v ∧ IsConj t w ∧ IsConj t (v * w)

theorem fzJt_conj_sq (g v : G) : (g⁻¹ * v * g) ^ 2 = g⁻¹ * v ^ 2 * g := by
  rw [pow_two, pow_two]; group

theorem fzJt_conj {t : G} {T : Subgroup G} {u x g : G} (hg : g⁻¹ * u * g = x)
    (hC : ∀ c ∈ T ⊓ centralizer ({u} : Set G), g⁻¹ * c * g ∈ T ⊓ centralizer ({x} : Set G))
    (hJ : FzJt t T u) : FzJt t T x := by
  obtain ⟨v, hv, w, hw, hv2, hw2, hvw, hc, htv, htw, htvw⟩ := hJ
  have key : ∀ c : G, IsConj t c → IsConj t (g⁻¹ * c * g) := fun c h =>
    h.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  refine ⟨g⁻¹ * v * g, hC v hv, g⁻¹ * w * g, hC w hw, ?_, ?_, ?_, ?_, key v htv, key w htw, ?_⟩
  · rw [fzJt_conj_sq, hv2]; group
  · rw [fzJt_conj_sq, hw2]; group
  · intro h; apply hvw
    have := congrArg (fun e => g * e * g⁻¹) h
    simpa [mul_assoc] using this
  · calc g⁻¹ * v * g * (g⁻¹ * w * g) = g⁻¹ * (v * w) * g := by group
      _ = g⁻¹ * (w * v) * g := by rw [hc]
      _ = g⁻¹ * w * g * (g⁻¹ * v * g) := by group
  · rw [show g⁻¹ * v * g * (g⁻¹ * w * g) = g⁻¹ * (v * w) * g by group]; exact key _ htvw

@[expose] def FzInvolT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G),
    FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ →
    ∀ v ∈ T₂, v ^ 2 = 1 → v ≠ 1 → v ∉ fzCalZ x₁ x₂ lam T₂ → IsConj t v

@[expose] def FzInvolZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G),
    FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ →
    ∀ v ∈ fzCalZ x₁ x₂ lam T₂, ¬ IsConj t v

@[expose] def FzSylR3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G),
    FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ →
    ∀ a ∈ fzR3 t x₁ x₂ a₃₂, a ^ 2 = (x₁ * x₂) ^ 2 →
      IsSylowOf 2 (T₂ ⊓ centralizer ({a} : Set G)) (centralizer ({a} : Set G))

@[expose] def FzJFailsR3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G),
    FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ →
    ∀ a ∈ fzR3 t x₁ x₂ a₃₂, a ^ 2 = (x₁ * x₂) ^ 2 → ¬ FzJ T₂ a

@[expose] def FzCalZPairR3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G),
    FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ →
    ∀ a ∈ fzR3 t x₁ x₂ a₃₂, a ^ 2 = (x₁ * x₂) ^ 2 →
    ∀ v ∈ T₂ ⊓ centralizer ({a} : Set G), ∀ w ∈ T₂ ⊓ centralizer ({a} : Set G),
      v ^ 2 = 1 → w ^ 2 = 1 → v ≠ 1 → w ≠ 1 → v ≠ w → v * w = w * v →
      v ∈ fzCalZ x₁ x₂ lam T₂ ∨ w ∈ fzCalZ x₁ x₂ lam T₂ ∨ v * w ∈ fzCalZ x₁ x₂ lam T₂

@[expose] def FzJtWitness : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G),
    FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ →
    ∀ u ∈ T₂, u ^ 2 = (x₁ * x₂) ^ 2 → u ∉ fzR3 t x₁ x₂ a₃₂ →
      ¬ (u ∈ fzR6 t x₁ x₂ a₁₂ a₂₂ a₃₂ ∧ ¬ ∃ r ∈ fzR3 t x₁ x₂ a₃₂, ∃ ε ∈ fourGrp x₁ x₂, u = r * ε) →
      ∃ v ∈ T₂ ⊓ centralizer ({u} : Set G), ∃ w ∈ T₂ ⊓ centralizer ({u} : Set G),
        v ^ 2 = 1 ∧ w ^ 2 = 1 ∧ v ≠ 1 ∧ w ≠ 1 ∧ v ≠ w ∧ v * w = w * v ∧
        v ∉ fzCalZ x₁ x₂ lam T₂ ∧ w ∉ fzCalZ x₁ x₂ lam T₂ ∧ v * w ∉ fzCalZ x₁ x₂ lam T₂

end CFSG.OddStandard.SmallF3.FritzII
