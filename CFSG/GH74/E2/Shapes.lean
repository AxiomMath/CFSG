module

public import CFSG.GH74.E2.Local
public import CFSG.GH74.Conclusion
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.E2

open Subgroup Blueprint

section Shapes

variable (K : Type) [Group K]

@[expose] def ShapeA5 : Prop :=
  Nonempty (K ≃* alternatingGroup (Fin 5)) ∨ LieModel K .PSL 2 2 2 ∨ LieModel K .PSL 2 5 1

@[expose] def ShapeL27 : Prop := LieModel K .PSL 2 7 1 ∨ LieModel K .PSL 3 2 1

@[expose] def ShapeA6 : Prop :=
  Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ LieModel K .PSL 2 3 2

@[expose] def ShapeL217 : Prop := LieModel K .PSL 2 17 1

@[expose] def ShapeL28 : Prop := LieModel K .PSL 2 2 3

@[expose] def ShapeL33 : Prop := LieModel K .PSL 3 3 1

@[expose] def ShapeU33 : Prop := LieModel K .PSU 3 3 1

@[expose] def ShapeSz8 : Prop := LieModel K .twistedB2 0 2 3

@[expose] def ShapeM11 : Prop := NativeSporadic.IsSporadic K .M11

@[expose] def Shape2M12 : Prop :=
  IsQuasisimple K ∧ Nat.card (center K) = 2 ∧ NativeSporadic.IsSporadic (K ⧸ center K) .M12

@[expose] def Shape2Sz8 : Prop :=
  IsQuasisimple K ∧ Nat.card (center K) = 2 ∧ LieModel (K ⧸ center K) .twistedB2 0 2 3

@[expose] def K0Shape : Prop :=
  ShapeA5 K ∨ ShapeL27 K ∨ ShapeA6 K ∨ ShapeL217 K ∨ ShapeL28 K ∨ ShapeL33 K ∨ ShapeU33 K ∨
    ShapeSz8 K ∨ ShapeM11 K ∨ Shape2M12 K ∨ Shape2Sz8 K

noncomputable def centerQuotientEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) :
    K ⧸ center K ≃* L ⧸ center L :=
  QuotientGroup.congr (center K) (center L) e (Subgroup.map_center_eq e)

end Shapes

theorem card_center_eq_of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) :
    Nat.card (center K) = Nat.card (center L) := by
  have hc : (center K).map e.toMonoidHom = center L := Subgroup.map_center_eq e
  rw [← hc]
  exact (Subgroup.card_map_of_injective e.injective).symm

section Transport

variable {K L : Type} [Group K] [Group L] (e : K ≃* L)

include e

theorem ShapeA5.of_mulEquiv : ShapeA5 K → ShapeA5 L := by
  rintro (h | h | h)
  · exact Or.inl (nonempty_alternating_of_mulEquiv e h)
  · exact Or.inr (Or.inl (lieModel_of_mulEquiv e h))
  · exact Or.inr (Or.inr (lieModel_of_mulEquiv e h))

theorem ShapeL27.of_mulEquiv : ShapeL27 K → ShapeL27 L := by
  rintro (h | h)
  · exact Or.inl (lieModel_of_mulEquiv e h)
  · exact Or.inr (lieModel_of_mulEquiv e h)

theorem ShapeA6.of_mulEquiv : ShapeA6 K → ShapeA6 L := by
  rintro (h | h)
  · exact Or.inl (nonempty_alternating_of_mulEquiv e h)
  · exact Or.inr (lieModel_of_mulEquiv e h)

theorem Shape2M12.of_mulEquiv : Shape2M12 K → Shape2M12 L := by
  rintro ⟨h1, h2, h3⟩
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e h1, (card_center_eq_of_mulEquiv e) ▸ h2,
    isSporadic_of_mulEquiv (centerQuotientEquiv e) h3⟩

theorem Shape2Sz8.of_mulEquiv : Shape2Sz8 K → Shape2Sz8 L := by
  rintro ⟨h1, h2, h3⟩
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e h1, (card_center_eq_of_mulEquiv e) ▸ h2,
    lieModel_of_mulEquiv (centerQuotientEquiv e) h3⟩

theorem K0Shape.of_mulEquiv : K0Shape K → K0Shape L :=
  Or.imp (ShapeA5.of_mulEquiv e) <| Or.imp (ShapeL27.of_mulEquiv e) <|
    Or.imp (ShapeA6.of_mulEquiv e) <| Or.imp (fun h => lieModel_of_mulEquiv e h) <|
    Or.imp (fun h => lieModel_of_mulEquiv e h) <| Or.imp (fun h => lieModel_of_mulEquiv e h) <|
    Or.imp (fun h => lieModel_of_mulEquiv e h) <| Or.imp (fun h => lieModel_of_mulEquiv e h) <|
    Or.imp (fun h => isSporadic_of_mulEquiv e h) <| Or.imp (Shape2M12.of_mulEquiv e)
      (Shape2Sz8.of_mulEquiv e)

end Transport

@[expose] def ComponentList : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ t : G, orderOf t = 2 → ∀ K : Subgroup G,
    IsCompCen t K → K0Shape ↥K ∧ ∀ K' : Subgroup G, IsCompCen t K' → K' = K

structure K0Data : Prop where
  autRank_ge5 : ∀ (K : Type) [Group K] [Finite K], K0Shape K → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ B : Subgroup (MulAut K), ElemAb p B → Nat.card B ≤ p
  center_card : ∀ (K : Type) [Group K] [Finite K], K0Shape K → Nat.card (center K) ≤ 2
  sylow_rank_simple : ∀ (K : Type) [Group K] [Finite K], K0Shape K → center K = ⊥ →
    ∃ T : Subgroup K, IsPGroup 2 T ∧ 2 ≤ Group.rank T
  sylow_rank_cover : ∀ (K : Type) [Group K] [Finite K], K0Shape K → center K ≠ ⊥ →
    ∃ T : Subgroup K, IsPGroup 2 T ∧ 3 ≤ Group.rank T

structure K0Data3 : Prop where
  autRank3_le_two : ∀ (K : Type) [Group K] [Finite K], K0Shape K →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 9
  autRank3_le_one : ∀ (K : Type) [Group K] [Finite K],
    (ShapeA5 K ∨ ShapeL27 K ∨ ShapeL217 K ∨ ShapeSz8 K ∨ Shape2Sz8 K) →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 3
  rank_ge3 : ∀ (K : Type) [Group K] [Finite K], (ShapeL28 K ∨ ShapeU33 K ∨ Shape2M12 K) →
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 3 ≤ Group.rank U
  rank_ge4 : ∀ (K : Type) [Group K] [Finite K], Shape2M12 K →
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 4 ≤ Group.rank U
  rank_ge3_sz : ∀ (K : Type) [Group K] [Finite K], (ShapeSz8 K ∨ Shape2Sz8 K) →
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 3 ≤ Group.rank U
  rank_ge4_sz : ∀ (K : Type) [Group K] [Finite K], Shape2Sz8 K →
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 4 ≤ Group.rank U
  inner3 : ∀ (K : Type) [Group K] [Finite K], (ShapeA6 K ∨ ShapeL33 K ∨ ShapeM11 K) →
    ∀ φ : MulAut K, φ ^ 3 = 1 → ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹
  centralizer3 : ∀ (K : Type) [Group K] [Finite K], (ShapeA6 K ∨ ShapeL33 K ∨ ShapeM11 K) →
    ∀ B : Subgroup K, ElemAb 3 B → Nat.card B = 9 → ∀ k : K, (∀ b ∈ B, k * b = b * k) → k ∈ B
  center_bot : ∀ (K : Type) [Group K] [Finite K],
    (ShapeL28 K ∨ ShapeU33 K ∨ ShapeA6 K ∨ ShapeL33 K ∨ ShapeM11 K ∨ ShapeA5 K ∨ ShapeL27 K ∨
      ShapeL217 K ∨ ShapeSz8 K) → center K = ⊥
  inner3_small : ∀ (K : Type) [Group K] [Finite K], (ShapeA5 K ∨ ShapeL27 K ∨ ShapeL217 K) →
    ∀ φ : MulAut K, φ ^ 3 = 1 → ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹
  autCentralizer : ∀ (K : Type) [Group K] [Finite K],
    (ShapeA6 K ∨ ShapeL28 K ∨ ShapeL33 K ∨ ShapeU33 K ∨ ShapeM11 K ∨ Shape2M12 K) →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R = 9 → ∀ ψ : MulAut K, ψ ^ 2 = 1 →
      (∀ r ∈ R, ψ * r = r * ψ) → ψ = 1

@[expose] def Q8Lemma : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (c : MulAut X), IsPGroup 2 X → Group.rank X = 2 →
    (∀ P : Subgroup X, Group.rank ↥P ≤ 2) → orderOf c = 3 →
    (∀ x : X, c x * x⁻¹ ∈ frattini X → x ∈ frattini X) → (∃ x : X, x ≠ 1 ∧ c x = x) →
    Nonempty (X ≃* QuaternionGroup 2)

end CFSG.GH74.E2
