module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def TrivAut (p : ℕ) (H : Type) [Group H] (φ : MulAut H) : Prop :=
  ∀ y : H, φ y * y⁻¹ ∈ GLAPPrimeCore p H

@[expose] def InnDiagAut (p : ℕ) (H : Type) [Group H] (φ : MulAut H) : Prop :=
  GLAMarking (ppQuot p H) fun _ _ _ I _ θ => ∃ u ∈ I, GLAInduces θ (relOfAut p φ) u

@[expose] noncomputable def cent2Aut (p : ℕ) (H : Type) [Group H] (φ : MulAut H) : ℕ :=
  twoPart (Nat.card {q : ppQuot p H // relOfAut p φ q q})

@[expose] def T2021RankFact : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (𝔅 : Type) [Group 𝔅] [Finite 𝔅] (ψ : 𝔅 →* MulAut H) (b : 𝔅),
    p.Prime → p ≠ 2 → IsChevSimple 2 (psimpleOf p H) → (∀ g : 𝔅, g ^ p = 1) → (∀ g h : 𝔅, g * h = h * g) →
    ¬ (p = 3 ∧ IsTD4Grp 3 H) → p ^ 3 * Nat.card {g : 𝔅 // TrivAut p H (ψ g)} ≤ Nat.card 𝔅 →
    FieldAutOn p H (ψ b) →
    ∃ b₁ : 𝔅, ¬ TrivAut p H (ψ b₁) ∧ InnDiagAut p H (ψ b₁) ∧ b ∉ Subgroup.zpowers b₁ ∧
      (∀ c ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers b₁, TrivAut p H (ψ c) → c = 1) ∧
      ∀ c ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers b₁, c ∉ Subgroup.zpowers b₁ →
        FieldAutOn p H (ψ c) ∧ ¬ TrivAut p H (ψ c)

@[expose] def T2021FixFact : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (𝔅 : Type) [Group 𝔅] [Finite 𝔅] (ψ : 𝔅 →* MulAut H) (T : Subgroup H),
    p.Prime → p ≠ 2 → IsChevSimple 2 (psimpleOf p H) → commutator (ppQuot p H) = ⊤ →
    ¬ (p = 3 ∧ IsTD4Grp 3 H) → (∀ g : 𝔅, g ^ p = 1) →
    (∀ g h : 𝔅, g * h = h * g) → IsPGroup 2 T → (∀ g : 𝔅, ∀ t ∈ T, ψ g t ∈ T) → ¬ T ≤ GLAPPrimeCore p H →
    (∀ T' : Subgroup H, IsPGroup 2 T' → (∀ g : 𝔅, ∀ t ∈ T', ψ g t ∈ T') → T ≤ T' → T' = T) →
    p ^ 3 * Nat.card {g : 𝔅 // TrivAut p H (ψ g)} ≤ Nat.card 𝔅 →
    ∀ g : 𝔅, (∀ t ∈ T, ψ g t * t⁻¹ ∈ GLAPPrimeCore p H) → TrivAut p H (ψ g)

@[expose] def T2021LayerFact : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (𝔅 : Type) [Group 𝔅] [Finite 𝔅] (ψ : 𝔅 →* MulAut H)
    (T : Subgroup H) (a b₁ : 𝔅),
    p.Prime → p ≠ 2 → IsChevSimple 2 (psimpleOf p H) → ¬ (p = 3 ∧ IsTD4Grp 3 H) → (∀ g : 𝔅, g ^ p = 1) →
    (∀ g h : 𝔅, g * h = h * g) → IsPGroup 2 T → (∀ g : 𝔅, ∀ t ∈ T, ψ g t ∈ T) →
    p ^ 3 * Nat.card {g : 𝔅 // TrivAut p H (ψ g)} ≤ Nat.card 𝔅 →
    FieldAutOn p H (ψ a) → InnDiagAut p H (ψ b₁) → ¬ TrivAut p H (ψ b₁) → a ∉ Subgroup.zpowers b₁ →
    (∃ t ∈ T, ψ a t * t⁻¹ ∈ GLAPPrimeCore p H ∧ ψ b₁ t * t⁻¹ ∉ GLAPPrimeCore p H) →
    ∃ T' : Subgroup H, T' ≤ GLAPLayer p (fixSub (ψ a)) ∧ IsPGroup 2 T' ∧ (∀ g : 𝔅, ∀ t ∈ T', ψ g t ∈ T') ∧
      ¬ T' ≤ GLAPPrimeCoreOf p (GLAPLayer p (fixSub (ψ a)))

@[expose] def T2021TD4Fact : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (𝔅 : Type) [Group 𝔅] [Finite 𝔅] (ψ : 𝔅 →* MulAut H) (T : Subgroup H) (b : 𝔅),
    IsChevSimple 2 (psimpleOf 3 H) → IsTD4Grp 3 H → (∀ g : 𝔅, g ^ 3 = 1) → (∀ g h : 𝔅, g * h = h * g) →
    IsPGroup 2 T →
    (∀ g : 𝔅, ∀ t ∈ T, ψ g t ∈ T) → ¬ T ≤ GLAPPrimeCore 3 H →
    (∀ T' : Subgroup H, IsPGroup 2 T' → (∀ g : 𝔅, ∀ t ∈ T', ψ g t ∈ T') → T ≤ T' → T' = T) →
    3 ^ 3 * Nat.card {g : 𝔅 // TrivAut 3 H (ψ g)} ≤ Nat.card 𝔅 →
    FieldAutOn 3 H (ψ b) → cent2Aut 3 H (ψ b) = Nat.sqrt (twoPart (Nat.card (ppQuot 3 H))) →
    ∃ T' : Subgroup H, T' ≤ GLAPLayer 3 (fixSub (ψ b)) ∧ IsPGroup 2 T' ∧
      (∀ g : 𝔅, ∀ t ∈ T', ψ g t ∈ T') ∧ ¬ T' ≤ GLAPPrimeCoreOf 3 (GLAPLayer 3 (fixSub (ψ b)))

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
