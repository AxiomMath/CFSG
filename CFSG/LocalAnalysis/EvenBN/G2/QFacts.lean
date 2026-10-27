module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYFourFacts

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

structure Setup.QFourFacts
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {K : Type} [Field K]
    [CharP K 2] (_h : Setup G L f t) (d : G2Data L K) : Prop where
  le_centralizer_U₁ : ∀ {P : Subgroup G}, P ≤ yamadaB d → IsPGroup 2 P →
    yamadaD₁ d t ⊓ centralizer (d.J₁ : Set G) ≤ P → P ≤ centralizer (yamadaU₁ d t : Set G)
  exists_complement : ∀ {V : Subgroup G}, IsSylowOf 2 V (yamadaB d) → ∀ {E : Subgroup G},
    E ≤ V → (∀ e ∈ E, e * e = 1) → (∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) →
    Nat.card E = Nat.card K ^ 4 → ∃ C : Subgroup G, C ≤ V ∧ E ⊓ C = ⊥ ∧ E ⊔ C = V

structure Setup.QFacts
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {K : Type} [Field K]
    [CharP K 2] (h : Setup G L f t) (d : G2Data L K) : Prop where
  doubling : h.DoublingFacts d
  branch : 8 ≤ Nat.card K ∨ (Nat.card K = 4 ∧ h.QFourFacts d)

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section QFacts

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem qFacts_of_eight (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (h8 : 8 ≤ Nat.card K) : h.QFacts d :=
  ⟨h.doublingFacts_of_eight d hK h8, Or.inl h8⟩

namespace QFacts

variable {h : Setup G L f t} {d : G2Data L K}

omit [Finite K] in
theorem four_le (hQ : h.QFacts d) : 4 ≤ Nat.card K := by
  rcases hQ.branch with h8 | ⟨hK4, -⟩
  · omega
  · omega

omit [Finite K] in
theorem one_lt (hQ : h.QFacts d) : 1 < Nat.card K :=
  lt_of_lt_of_le (by norm_num) hQ.four_le

end QFacts

end QFacts

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
