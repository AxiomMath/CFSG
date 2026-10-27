module

public import CFSG.Goldschmidt.Setup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Open

structure Theorem48Inputs : Prop where
  goldschmidt_theorem_four : ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 2 Y) (V : Subgroup Y),
    V ≤ P → IsElemAbelian 2 V →
    (∀ h : Y, rightConjugate V h ≤ P → rightConjugate V h = V) →
    (∃ v ∈ V, ∃ h : Y, h⁻¹ * v * h ∈ (P : Subgroup Y) ∧ h⁻¹ * v * h ∉ V) →
    ∃ U ≤ V, ∃ h : Y, rightConjugate U h ≤ P ∧ ¬ rightConjugate U h ≤ V ∧
      ∀ w ∈ rightConjugate U h,
        Nat.card (⁅V, Subgroup.zpowers w⁆ : Subgroup Y) ≤ V.relIndex (rightConjugate U h)
  walter_schur_two_part : ∀ (K : Type) [Group K] [Finite K] (Z₀ : Subgroup K) [Z₀.Normal],
    IsQuasisimple K → Z₀ ≤ Subgroup.center K → IsPGroup 2 Z₀ →
    ∀ P : Sylow 2 (K ⧸ Z₀), IsMulCommutative (P : Subgroup (K ⧸ Z₀)) →
      Nat.card Z₀ ≤ 2 ∧ (8 ≤ Nat.card P → Z₀ = ⊥)
  goldschmidt : CFSG.Goldschmidt.TopStatement

end CFSG.ComponentClassification.AschbacherTheorem3
