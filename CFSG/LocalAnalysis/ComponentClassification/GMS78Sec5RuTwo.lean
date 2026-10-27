module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoPreimage
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Recognition.RuTypeDefs
public import Certificates.Data.GMS78RuQCheck

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

@[expose] def Dempwolff218Hyp (G : Type) [Group G] [Finite G] : Prop :=
  ∀ {H J X Z : Subgroup G}, IsElemAbelian 2 X → Nat.card X = 32 → Z ≤ X → Nat.card Z = 2 →
    (∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ = z) → (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) →
    (∀ h, h ∈ J ↔ h ∈ H ∧ ∀ x ∈ X, h * x * h⁻¹ * x⁻¹ ∈ Z) → J.relIndex H = 120 →
    (∀ x ∈ X, x ∉ Z → ∀ x' ∈ X, x' ∉ Z → ∃ h ∈ H, h * x * h⁻¹ * x'⁻¹ ∈ Z) →
    (∃ σ : H →* Equiv.Perm (Fin 5), Function.Surjective σ ∧ σ.ker = J.subgroupOf H) ∧
    ∃ (φ : H →* RuType.SigmaL2F4) (ψ : X →* Multiplicative (Fin 2 → RuType.F4)),
      Function.Surjective φ ∧ φ.ker = J.subgroupOf H ∧
      Function.Surjective ψ ∧ ψ.ker = Z.subgroupOf X ∧
      ∀ (h : H) (u u' : X), (u' : G) = h * u * (h : G)⁻¹ →
        ψ u' = Multiplicative.ofAdd (RuType.sigmaAct (φ h) (Multiplicative.toAdd (ψ u)))

omit [Finite G] in
theorem mem_zpowers_of_mul_self {f : G} (hf2 : f * f = 1) {x : G} :
    x ∈ zpowers f ↔ x = 1 ∨ x = f := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two, hf2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hf2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
