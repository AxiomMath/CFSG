module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YOutside

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def litFixSub {G : Type*} [Group G] (σ : G ≃* G) : Subgroup G where
  carrier := {x | σ x = x}
  mul_mem' := by
    intro x y hx hy
    show σ (x * y) = x * y
    rw [map_mul, show σ x = x from hx, show σ y = y from hy]
  one_mem' := map_one σ
  inv_mem' := by
    intro x hx
    show σ x⁻¹ = x⁻¹
    rw [map_inv, show σ x = x from hx]

@[expose] def litTSub {X : Type*} [Group X] (τ : X ≃* X) (N : Subgroup X) [N.Normal] :
    Subgroup X where
  carrier := {x | τ x * x⁻¹ ∈ N}
  mul_mem' := by
    intro x y hx hy
    show τ (x * y) * (x * y)⁻¹ ∈ N
    have e : τ (x * y) * (x * y)⁻¹ = (τ x * x⁻¹) * (x * (τ y * y⁻¹) * x⁻¹) := by
      rw [map_mul]
      group
    rw [e]
    exact N.mul_mem hx (Normal.conj_mem inferInstance _ hy x)
  one_mem' := by
    show τ 1 * (1 : X)⁻¹ ∈ N
    simp
  inv_mem' := by
    intro x hx
    show τ x⁻¹ * (x⁻¹)⁻¹ ∈ N
    have e : τ x⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * (τ x * x⁻¹)⁻¹ * x := by
      rw [map_inv]
      group
    rw [e]
    have h := Normal.conj_mem inferInstance _ (N.inv_mem hx) x⁻¹
    simpa using h

@[expose] def LitPSLU4 (S : Type) [Group S] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f % 8 = 5 ∧ CFSG.Blueprint.LieModel S .PSL 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f % 8 = 3 ∧ CFSG.Blueprint.LieModel S .PSU 4 p f)

@[expose] def LitPSLU4S (S : Type) [Group S] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f % 8 = 1 ∧ CFSG.Blueprint.LieModel S .PSL 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f % 8 = 7 ∧ CFSG.Blueprint.LieModel S .PSU 4 p f)

@[expose] def LitPSLU4All (S : Type) [Group S] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f % 4 = 1 ∧ CFSG.Blueprint.LieModel S .PSL 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 0 < f ∧ p ^ f % 4 = 3 ∧ CFSG.Blueprint.LieModel S .PSU 4 p f)

@[expose] def LitQType (S : Type) [Group S] : Prop :=
  CFSG.Blueprint.NativeSporadic.IsSporadic S .M22 ∨ LitPSLU4 S

@[expose] def LitStrothType (S : Type) [Group S] : Prop :=
  CFSG.Blueprint.NativeSporadic.IsSporadic S .HS ∨ LitPSLU4S S ∨ HasPSL6Sylow S

@[expose] def Gomi1Q : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (S A : Subgroup Γ), IsSimpleGroup ↥S → A ≤ S → IsE 4 ↥A →
    IsQuotIso (normIn S A) (centIn S A) ↥(alternatingGroup (Fin 6)) →
    IsSylowIn 2 (centIn S A) A → LitQType ↥S

@[expose] def GomiOuterPSLU4 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (τ : H ≃* H), CFSG.IsQuasisimple H →
    LitPSLU4All (H ⧸ center H) → (∀ x, τ (τ x) = x) →
    (∃ z ∈ center H, (∃ k : ℕ, z ^ 2 ^ k = 1) ∧ τ z ≠ z) →
    Group.IsSolvable ↥(litTSub τ (center H)) → IsSU43 (H ⧸ CFSG.oddCore H)

@[expose] def GomiOuterM22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (σ : G ≃* G), M.Normal →
    CFSG.Blueprint.NativeSporadic.IsSporadic ↥M .M22 → centralizer (M : Set G) = ⊥ →
    (∀ x, σ (σ x) = x) → (∃ x, σ x ≠ x) → ¬ 9 ∣ Nat.card ↥(litFixSub σ)

@[expose] def StrothSigma6 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (S A : Subgroup Γ), IsSimpleGroup ↥S → A ≤ S → IsE 4 ↥A →
    IsQuotIso (normIn S A) (centIn S A) (Equiv.Perm (Fin 6)) → IsSylowIn 2 (centIn S A) A →
    LitStrothType ↥S

end CFSG.OddStandard.HigherRank.YamadaG23
