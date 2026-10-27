module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.Asc76

@[expose] def Hall32For (G : Type) [Group G] [Finite G] : Prop :=
  ∀ S T : Subgroup G, IsSylowOf 2 S ⊤ → T ≤ S → Nat.card T = 4 → IsElemAbelian 2 T →
    (∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T) →
    IsSylowOf 2 T (normalClosure (T : Set G)) ∨
      Nonempty (↥(normalClosure (T : Set G)) ⧸
          CFSG.Assembly.oddCore ↥(normalClosure (T : Set G)) ≃* PSU3 2 2) ∨
      ∀ P : Subgroup G, IsSylowOf 2 P (normalClosure (T : Set G)) →
        Nonempty (P ≃* DihedralGroup 4)

theorem hallFusionThm32_iff :
    HallFusionThm32 ↔ ∀ (G : Type) [Group G] [Finite G], Hall32For G :=
  Iff.rfl

@[expose] def Hall32Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → Hall32For H) →
    ∀ S T : Subgroup G, IsSylowOf 2 S ⊤ → T ≤ S → Nat.card T = 4 → IsElemAbelian 2 T →
      (∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T) →
      (∃ t ∈ T, ∃ g : G, g⁻¹ * t * g ∈ S ∧ g⁻¹ * t * g ∉ T) →
      normalClosure (T : Set G) = ⊤ →
      (∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥) →
      S ⊓ centralizer (T : Set G) = T

end CFSG.ComponentClassification.Asc76X
