module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25B00
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.ExactLayer (tqMembers exactCore)

section Residuals


@[expose] def Sup23_2Three : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G},
    Hyp23Setting Ω K K' z → Hyp24Data Ω K K' W S R R' z u →
      Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤

@[expose] def Hyp51VertexThree : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K₀ : Subgroup G},
    AscStand Ω K₀ → ∀ {K K' : Subgroup G} {z x y e₁ e₂ : G}, K ∈ Ω → K' ∈ Ω →
      IsUniqueInvolution K z → IsUniqueInvolution K' z → ∀ {B : Subgroup G}, IsElemAbelian 2 B →
        z ∈ B → x ∈ K → y ∈ K' → x * y ∈ B → x * y ≠ 1 → x * y ≠ z →
        e₁ ∈ B → e₁ ≠ 1 → e₁ ≠ z → e₁ ∈ trivialOnQuot K →
        e₂ ∈ B → e₂ ≠ 1 → e₂ ≠ z → e₂ ∈ trivialOnQuot K' → Hyp51At B z

@[expose] def Hyp51TwinInnerThree : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K₀ : Subgroup G},
    AscStand Ω K₀ → ∀ {K K' : Subgroup G} {b d c : G}, K ∈ Ω → K' ∈ Ω → K' ≠ K →
      IsUniqueInvolution K b → IsUniqueInvolution K' b → K ∈ tqMembers Ω c →
      K' ∈ tqMembers Ω c → ∀ {B : Subgroup G}, IsElemAbelian 2 B → b ∈ B → d ∈ B →
        c ∈ B → B = Subgroup.closure ({b, d, c} : Set G) → c ≠ 1 → b ≠ c → d ≠ 1 → d ≠ b →
        d * d = 1 → d ∈ exactCore c K ⊔ exactCore c K' → Hyp51At B c

end Residuals

end CFSG.ClassicalInvolution.Q3.Q3T7P24
