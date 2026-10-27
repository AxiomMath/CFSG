module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsS

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1

open Subgroup CFSG.Open
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] (fr : Frame Γ)

namespace Frame

@[expose] def Fact16 (L : Subgroup Γ) : Prop :=
  (fr.z ∈ invols L ∧ ∀ u ∈ invols L, ∀ v ∈ invols L, ∃ l ∈ L, v = l * u * l⁻¹) ∧
  centEl L fr.z = fr.K₁ ⊔ fr.K₂ ⊔ closure {fr.h₀} ∧
  Nonempty (↥fr.K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
  Nonempty (↥fr.K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
  (fr.K₁ ≤ centEl L fr.z ∧ (fr.K₁.subgroupOf (centEl L fr.z)).Normal) ∧
  (fr.K₂ ≤ centEl L fr.z ∧ (fr.K₂.subgroupOf (centEl L fr.z)).Normal) ∧
  (∀ u ∈ fr.K₁, ∀ v ∈ fr.K₂, u * v = v * u) ∧ fr.K₁ ⊓ fr.K₂ = fr.Z ∧
  pCoreOf 2 fr.K₁ = closure {fr.a₁, fr.b₁} ∧ pCoreOf 2 fr.K₂ = closure {fr.a₂, fr.b₂} ∧
  IsSylowIn 3 fr.K₁ fr.X₁ ∧ IsSylowIn 3 fr.K₂ fr.X₂ ∧
  (∀ y ∈ fr.X₁, fr.h₀ * y * fr.h₀⁻¹ = y⁻¹) ∧ (∀ y ∈ fr.X₂, fr.h₀ * y * fr.h₀⁻¹ = y⁻¹) ∧
  conjSub fr.σ fr.K₁ = fr.K₂

@[expose] def Fact17 (L : Subgroup Γ) : Prop :=
  Nonempty (↥(centEl L fr.σ) ≃*
    MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))) ∧
  IsSylowIn 2 (centEl L fr.σ) fr.F

@[expose] def Fact18 (L : Subgroup Γ) : Prop :=
  (normIn L fr.S = normIn L fr.A ⊓ normIn L fr.B ∧ normIn L fr.S = fr.S) ∧
  (normIn L fr.A = centEl L fr.z ∧
    SecProp (normIn L fr.A) fr.A (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y) ∧
    ∀ T : Subgroup Γ, IsSylowIn 3 (normIn L fr.A) T →
      IsOrbitMod T fr.Z ((closure {fr.a₁, fr.b₁} : Set Γ) \ (fr.Z : Set Γ)) ∧
      IsOrbitMod T fr.Z ((closure {fr.a₂, fr.b₂} : Set Γ) \ (fr.Z : Set Γ)) ∧
      IsOrbitMod T fr.Z ((fr.A : Set Γ) \
        ((closure {fr.a₁, fr.b₁} : Set Γ) ∪ (closure {fr.a₂, fr.b₂} : Set Γ)))) ∧
  (normIn L fr.B = normIn L (cen fr.B) ∧ normIn L fr.B ≤ normIn L fr.F ∧
    SecProp (normIn L fr.B) fr.B (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∧
    (∀ T : Subgroup Γ, IsSylowIn 3 (normIn L fr.B) T →
      ActsRegularly T (cen fr.B) ⊥ ∧ ActsRegularly T (thompsonSubgroup fr.B) (cen fr.B)) ∧
    centIn L (cen fr.B) = fr.B) ∧
  (centIn L fr.E = fr.E ∧ normIn L fr.E ≤ normIn L fr.A ∧
    SecProp (normIn L fr.E) fr.A (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∧
    (∀ u ∈ fr.E, u ∉ fr.Z → ∀ v ∈ fr.E, v ∉ fr.Z → ∃ k ∈ normIn L fr.E, k * u * k⁻¹ = v) ∧
    ∀ T : Subgroup Γ, IsSylowIn 3 (normIn L fr.E) T →
      ActsRegularly T fr.E fr.Z ∧ ActsRegularly T fr.A fr.E) ∧
  (centIn L fr.F = fr.F ∧
    SecProp (normIn L fr.F) fr.F
      (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∧
    ¬ SplitsOver (normIn L fr.F) fr.F ∧
    SecProp (normIn L fr.A ⊓ normIn L fr.F) fr.A
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∧
    ∀ T : Subgroup Γ, IsSylowIn 3 (normIn L fr.A ⊓ normIn L fr.F) T →
      ActsRegularly T fr.F fr.Z ∧ ActsRegularly T fr.A fr.F)

@[expose] def Fact19 (L : Subgroup Γ) : Prop :=
  ∀ Y ∈ maxElemAbelian L, ∃ l ∈ L, Y = conjSub l fr.E ∨ Y = conjSub l fr.F

@[expose] def Fact110 (L : Subgroup Γ) : Prop :=
  (SecProp (normIn L fr.A ⊔ closure {fr.σ}) fr.A
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
    {g : Γ | g ∈ L ⊔ closure {fr.σ} ∧ ∀ a ∈ fr.A, ⁅a, g⁆ ∈ fr.Z} = (fr.A : Set Γ) ∧
    {g : Γ | g ∈ L ⊔ closure {fr.σ} ∧ ∀ y ∈ fr.E ⊔ fr.F, ⁅y, g⁆ ∈ fr.Z} = (fr.A : Set Γ)) ∧
  (fr.σ ∈ normalizer (fr.F : Set Γ) ∧ ∀ g ∈ normIn L fr.F, ⁅fr.σ, g⁆ ∈ fr.F)

@[expose] def Facts (L : Subgroup Γ) : Prop :=
  fr.Fact11 L ∧ fr.Fact12 ∧ fr.Fact13 ∧ fr.Fact14 ∧ fr.Fact15 ∧ fr.Fact16 L ∧ fr.Fact17 L ∧
    fr.Fact18 L ∧ fr.Fact19 L ∧ fr.Fact110 L

end Frame

end CFSG.OddStandard.HigherRank.G2Three.Sec1
