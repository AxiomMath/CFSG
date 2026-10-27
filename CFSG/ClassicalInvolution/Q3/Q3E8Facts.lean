module

public import CFSG.ClassicalInvolution.Q3.Q3EPExcl
public import CFSG.ClassicalInvolution.RouteD.TypeE8Excl
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLayerStmt
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclRowStmt
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorNodes
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorTwin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


section Toral

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

@[expose] def ToralNormalAt3 (c : ETCtx3 .E7 0 Ω K z) {t : G} (ht : t * z * t⁻¹ = z)
    (g : TypeE8.K7 3 1) (p₀ : Fin 7) : Prop :=
  ∀ γ ∈ (TypeE8.D7 3 1).roots,
    ((conjSub g (TypeE8.Rroot 3 1 γ)).map c.d.ψ).map
        (Gaps.locAut c.hΩ.conjInvariant ht).toMonoidHom =
      (conjSub g (TypeE8.Rroot 3 1 γ)).map c.d.ψ ∧
    ((∀ x ∈ (conjSub g (TypeE8.Rroot 3 1 γ)).map c.d.ψ,
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ ((γ p₀ : ℤ) : ZMod 2) = 0)

end Toral

@[expose] def E8ClassExcluded3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .E7 0) (conjClass3 K) z →
      ∀ c : ETCtx3 .E7 0 (conjClass3 K) K z, ∀ β ∈ conjClass3 K, ∀ t : G,
        IsClassicalMember3 β t →
        (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) →
        ∀ ht : t * z * t⁻¹ = z, ∀ (g : TypeE8.K7 3 1) (p₀ : Fin 7),
          ToralNormalAt3 c ht g p₀ → p₀ = 6

@[expose] def E7SignPerp3 : Prop := TypeE8.E7Sign 3 1 ∧ TypeE8.E7Perp2 3 1

@[expose] def E8D8Row3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), IsFundTag t → t ≠ .G2 → t ≠ .trialityD4 →
    StatedLieAdmissible t n 3 1 →
    ∀ R₀ ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D,
      ∀ k ∈ R₀, (∀ r ∈ R₀, r * k = k * r) →
      ∀ φ : {R : Subgroup (modelUniv t n 3 1 Nat.prime_three).K //
          R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D ∧
            R ≤ Subgroup.centralizer ({k} : Set (modelUniv t n 3 1 Nat.prime_three).K)} ≃
          TypeE8.D8Layer 3 1,
        (∀ R R', Commutes R.1 R'.1 ↔ TypeE8.D8Layer.rel 3 1 (φ R) (φ R')) →
        (∀ R, R.1 = R₀ → φ R = none) → t = .POmegaPlus ∧ n = 8

@[expose] def E8P1x3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z → ∀ (W₁ W₂ : Subgroup G) (w₁ w₂ : G),
      W₁ ∈ conjClass3 K → W₂ ∈ conjClass3 K → IsClassicalMember3 W₁ w₁ →
      IsClassicalMember3 W₂ w₂ → Commutes K W₁ → Commutes K W₂ → Commutes W₁ W₂ →
      Nat.card (Subgroup.closure ({z, w₁, w₂} : Set G)) = 8 →
      LocalOddCentral (conjClass3 K) {w₁ * w₂} ∧ LocalOddThreeFree3 (conjClass3 K) (w₁ * w₂)

@[expose] def E8R1Excluded3 : Prop :=
  TypeE8.E7FrameRelations 3 1 → TypeE8.E7PerpA2StarFree 3 1 →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
        LocalShapeC3 1 (CompData.model .E7 0) (conjClass3 K) z →
        ∀ c : ETCtx3 .E7 0 (conjClass3 K) K z, ∀ β ∈ conjClass3 K, ∀ t : G,
          IsClassicalMember3 β t →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) →
          ∀ ht : t * z * t⁻¹ = z, ∀ (g : TypeE8.K7 3 1) (p₀ : Fin 7),
            (p₀ = 0 ∨ p₀ = 2 ∨ p₀ = 3 ∨ p₀ = 5) → ToralNormalAt3 c ht g p₀ → False

@[expose] def E8R2Excluded3 : Prop :=
  TypeE8.E7FrameRelations 3 1 → TypeE8.E7FrameInvolutions 3 1 → TypeE8.E7LayerEquiv 3 1 →
    TypeE8.Fund12Connected 3 1 → E8D8Row3 → TypeE8.D8NoThreeAdjPairs 3 .POmegaPlus 8 1 →
    E8P1x3 →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
        LocalShapeC3 1 (CompData.model .E7 0) (conjClass3 K) z →
        ∀ c : ETCtx3 .E7 0 (conjClass3 K) K z, ∀ β ∈ conjClass3 K, ∀ t : G,
          IsClassicalMember3 β t →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) →
          ∀ ht : t * z * t⁻¹ = z, ∀ (g : TypeE8.K7 3 1) (p₀ : Fin 7), (p₀ = 1 ∨ p₀ = 4) →
            ToralNormalAt3 c ht g p₀ → False

theorem e8ClassExcluded3_of_packages (hB8 : TypeE8.E7FrameRelations 3 1)
    (hB9 : TypeE8.E7FrameInvolutions 3 1) (hB7 : TypeE8.E7PerpA2StarFree 3 1)
    (hLayer : TypeE8.E7LayerEquiv 3 1) (hConn : TypeE8.Fund12Connected 3 1) (hRow : E8D8Row3)
    (hD8 : TypeE8.D8NoThreeAdjPairs 3 .POmegaPlus 8 1) (hP1x : E8P1x3)
    (h1 : E8R1Excluded3) (h2 : E8R2Excluded3) : E8ClassExcluded3 := by
  intro G _ _ _ hnab K z hR hshape c β hβ t htβ hKβ ht g p₀ hT
  by_contra h6
  have hcases : p₀ = 0 ∨ p₀ = 1 ∨ p₀ = 2 ∨ p₀ = 3 ∨ p₀ = 4 ∨ p₀ = 5 := by
    fin_cases p₀ <;> simp_all
  have hR1 : (p₀ = 0 ∨ p₀ = 2 ∨ p₀ = 3 ∨ p₀ = 5) → False := fun h =>
    h1 hB8 hB7 G hnab K z hR hshape c β hβ t htβ hKβ ht g p₀ h hT
  have hR2 : (p₀ = 1 ∨ p₀ = 4) → False := fun h =>
    h2 hB8 hB9 hLayer hConn hRow hD8 hP1x G hnab K z hR hshape c β hβ t htβ hKβ ht g p₀ h hT
  rcases hcases with h | h | h | h | h | h
  · exact hR1 (Or.inl h)
  · exact hR2 (Or.inl h)
  · exact hR1 (Or.inr (Or.inl h))
  · exact hR1 (Or.inr (Or.inr (Or.inl h)))
  · exact hR2 (Or.inr h)
  · exact hR1 (Or.inr (Or.inr (Or.inr h)))

end CFSG.ClassicalInvolution.Q3.Q3W
