module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar

instance e6Order3NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩


@[expose] def E6KindA2 (w : WeylGroup Tag.E6) : Prop :=
  ∃ α β : Fin Tag.E6.rank → ℤ, IsA2Pair α β ∧ w = rootReflection α * rootReflection β

@[expose] def E6Kind3A2 (w : WeylGroup Tag.E6) : Prop :=
  ∀ v : Fin Tag.E6.rank → ℤ, v + w • v + w • w • v = 0

@[expose] def E6Kind2A2 (w : WeylGroup Tag.E6) (γ₁ γ₂ : Fin Tag.E6.rank → ℤ) : Prop :=
  IsA2Pair γ₁ γ₂ ∧ w • γ₁ = γ₁ ∧ w • γ₂ = γ₂ ∧
    (∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → w • γ = γ → γ ∈ a2Roots γ₁ γ₂) ∧
    (∃ μ : Fin Tag.E6.rank → ℤ, 2 • γ₁ + γ₂ = μ + w • μ + w • w • μ) ∧
    ∀ j : Fin Tag.E6.rank, ∃ m n : ℤ,
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) + w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
          w • w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
        m • γ₁ + n • γ₂

@[expose] def E6Order3Kinds : Prop :=
  ∀ w : WeylGroup Tag.E6, w ^ 3 = 1 → w ≠ 1 →
    E6KindA2 w ∨ (∃ γ₁ γ₂, E6Kind2A2 w γ₁ γ₂) ∨ E6Kind3A2 w

@[expose] def E6Order3Pairs : Prop :=
  ∀ w₁ w₂ : WeylGroup Tag.E6, w₁ ^ 3 = 1 → w₁ ≠ 1 → w₂ ^ 3 = 1 → Commute w₁ w₂ →
    w₂ ∉ Subgroup.zpowers w₁ →
    (∃ i j : ℕ, E6Kind3A2 (w₁ ^ i * w₂ ^ j)) ∨
    ((∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ w₁ • γ = γ ∧ w₂ • γ = γ) ∧
      (∃ i j k l : ℕ, ¬ (3 : ℤ) ∣ ((i * l : ℕ) : ℤ) - ((j * k : ℕ) : ℤ) ∧
        (∃ γ₁ γ₂, E6Kind2A2 (w₁ ^ i * w₂ ^ j) γ₁ γ₂) ∧
        (∃ γ₁ γ₂, E6Kind2A2 (w₁ ^ k * w₂ ^ l) γ₁ γ₂)) ∧
      ∀ w₃ : WeylGroup Tag.E6, w₃ ^ 3 = 1 → Commute w₁ w₃ → Commute w₂ w₃ →
        (∀ i j : ℕ, w₃ ≠ w₁ ^ i * w₂ ^ j) →
          ∃ i j k : ℕ, E6Kind3A2 (w₁ ^ i * w₂ ^ j * w₃ ^ k))

@[expose] def E6FixesNode3 (w : WeylGroup Tag.E6) : Prop :=
  ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → (w • γ) 3 ≡ γ 3 [ZMOD 3]

@[expose] def E6TauChars (w : WeylGroup Tag.E6) (γ₁ : Fin Tag.E6.rank → ℤ) : Prop :=
  ∀ χ : Fin Tag.E6.rank → ZMod 3, χ ≠ 0 →
    (∀ v : Fin Tag.E6.rank → ℤ, ∑ i, χ i * ((w • v) i : ZMod 3) = ∑ i, χ i * (v i : ZMod 3)) →
    ∑ i, χ i * (γ₁ i : ZMod 3) = 0 →
    ((rootFinset Tag.E6).filter fun γ => ∑ i, χ i * (γ i : ZMod 3) = 0).card = 18 ∨
    ∃ β : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 β ∧ (3 : ℤ) ∣ β 3 ∧
      ∑ i, χ i * (β i : ZMod 3) = 0 ∧
      iform β (w • β) = 0 ∧ iform β (w • w • β) = 0 ∧ iform (w • β) (w • w • β) = 0

@[expose] def E6CaseITable : Prop :=
  (∀ w : WeylGroup Tag.E6, w ^ 3 = 1 → w ≠ 1 → E6FixesNode3 w →
    E6KindA2 w ∨ E6Kind3A2 w ∨
    (∃ γ₁ γ₂, E6Kind2A2 w γ₁ γ₂ ∧ ∀ γ ∈ a2Roots γ₁ γ₂, (3 : ℤ) ∣ γ 3) ∨
    (∃ γ₁ γ₂, E6Kind2A2 w γ₁ γ₂ ∧ (∀ γ ∈ a2Roots γ₁ γ₂, ¬ (3 : ℤ) ∣ γ 3) ∧
      E6TauChars w γ₁)) ∧
  ∀ w₁ w₂ : WeylGroup Tag.E6, w₁ ^ 3 = 1 → w₁ ≠ 1 → w₂ ^ 3 = 1 → Commute w₁ w₂ →
    w₂ ∉ Subgroup.zpowers w₁ → E6FixesNode3 w₁ → E6FixesNode3 w₂ →
    (∃ i j : ℕ, E6Kind3A2 (w₁ ^ i * w₂ ^ j)) ∨
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3 ∧ w₁ • γ = γ ∧ w₂ • γ = γ ∧
      ∃ i j k l : ℕ, ¬ (3 : ℤ) ∣ ((i * l : ℕ) : ℤ) - ((j * k : ℕ) : ℤ) ∧
        (∃ γ₁ γ₂, E6Kind2A2 (w₁ ^ i * w₂ ^ j) γ₁ γ₂ ∧ ∀ δ ∈ a2Roots γ₁ γ₂, (3 : ℤ) ∣ δ 3) ∧
        (∃ γ₁ γ₂, E6Kind2A2 (w₁ ^ k * w₂ ^ l) γ₁ γ₂ ∧ ∀ δ ∈ a2Roots γ₁ γ₂, (3 : ℤ) ∣ δ 3)

end CFSG.LieType.SeitzGeneration.ExcWideThree
