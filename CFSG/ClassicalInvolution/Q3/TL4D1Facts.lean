module

public import CFSG.ClassicalInvolution.Q3.TL3T16
public import CFSG.ClassicalInvolution.Q3.AE.Bar
public import CFSG.ClassicalInvolution.Q3.AE.Models

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin

@[expose] def E8NormalFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X E : Subgroup G), E8Struct X E →
    ∀ N : Subgroup G, N ≤ X → (∀ x ∈ X, ∀ y ∈ N, x * y * x⁻¹ ∈ N) →
      IsPGroup 2 ↥N ∨ N = X

@[expose] def E8PerfectFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X E : Subgroup G), E8Struct X E → ⁅X, X⁆ = X

variable {n : ℕ}

abbrev aeModel (m : ℕ) : Subgroup (AE.AEQ m) := (AE.aeSub m).map (AE.mkQ m)

@[expose] def ModelNormal (M : Subgroup (AE.AEQ n)) : Prop :=
  ∀ N : Subgroup (AE.AEQ n), N ≤ M → (∀ x ∈ M, ∀ y ∈ N, x * y * x⁻¹ ∈ N) →
    IsPGroup 2 ↥N ∨ N = M

@[expose] def ModelPerfect (M : Subgroup (AE.AEQ n)) : Prop := ⁅M, M⁆ = M

@[expose] def ModelThree (𝒜 : Set (Finset (Fin n))) (M : Subgroup (AE.AEQ n)) : Prop :=
  ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ y ∈ M, y ^ 3 = 1 ∧
    (∀ k ∈ AE.memBar α h b, y * k * y⁻¹ ∈ AE.memBar α h b) ∧
    AE.memBar α h b ≤ Subgroup.closure {x | ∃ k ∈ AE.memBar α h b, x = k * y * k⁻¹ * y⁻¹}

@[expose] def ModelMembers (𝒜 : Set (Finset (Fin n))) (M : Subgroup (AE.AEQ n)) : Prop :=
  ∀ (B : Subgroup (AE.AEQ n)) (w : AE.AEQ n), B ≤ M → IsUniqueInvolution B w →
    Nat.card ↥B = 8 → (∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) →
    (∃ T : Subgroup (AE.AEQ n), T ≤ M ∧ (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) ∧
      IsPGroup 2 ↥T ∧ w ∈ T) →
    (∀ T : Subgroup (AE.AEQ n), T ≤ M → (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
      IsPGroup 2 ↥T → ∀ x ∈ B, x ∈ T → x = 1 ∨ x = w) →
    (∀ y ∈ M, Odd (orderOf y) → y * w = w * y → ∀ x ∈ B, y * x * y⁻¹ ∈ B) →
    (∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), AE.zBar α h = w →
      AE.memBar α h b = B ∨ Commutes (AE.memBar α h b) B) →
    (∀ g ∈ M, g * w = w * g → conjSub g B = B ∨ Commutes B (conjSub g B)) →
    ∃ α ∈ 𝒜, ∃ (h : α.card = 4) (b : Bool), B = AE.memBar α h b

structure ModelFacts (𝒜 : Set (Finset (Fin n))) (M : Subgroup (AE.AEQ n)) : Prop where
  normal : ModelNormal M
  perfect : ModelPerfect M
  three : ModelThree 𝒜 M
  members : ModelMembers 𝒜 M

structure D1Facts : Prop where
  e8Normal : E8NormalFact
  e8Perfect : E8PerfectFact
  aeNormal : ∀ m : ℕ, 5 ≤ m → ModelNormal (aeModel m)
  aePerfect : ∀ m : ℕ, 5 ≤ m → ModelPerfect (aeModel m)
  aeMembers : ∀ m : ℕ, 5 ≤ m → ModelMembers (Set.univ : Set (Finset (Fin m))) (aeModel m)
  e64 : ModelFacts AE.e64Sets AE.e64Sub
  e29 : ModelFacts AE.e29Sets AE.e29Sub

end CFSG.ClassicalInvolution.Q3.TL4
