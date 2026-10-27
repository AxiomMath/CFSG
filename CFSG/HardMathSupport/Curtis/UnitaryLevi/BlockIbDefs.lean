module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDefs
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveGeometryLattice

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

structure BlockIbParab {Y : Type} [Group Y] [Finite Y] (Lb Pb : Subgroup Y) : Prop where
  comp : IsComponentOf Lb ⊤
  odd : Odd (Nat.card (Subgroup.center ↥Lb))
  parab : IsParabolicTwo Lb Pb
  ne : Pb ≠ Lb

structure BlockIbData {Y : Type} [Group Y] [Finite Y] (Lb Pb D : Subgroup Y) (x : Y) : Prop where
  cop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥Lb))
  rank : CFSG.Open.pRank 3 Pb ≤ 3
  cyc : ∀ V : Subgroup Y, V ≤ Pb → ⁅V, V⁆ = V → ∀ A : Subgroup Y, A ≤ V → IsPGroup 3 A →
    IsCyclic A
  Dperf : ⁅D, D⁆ = D
  Dle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y)
  Dcyc : ∀ A : Subgroup Y, A ≤ D → IsPGroup 3 A → IsCyclic A
  Dcarry : ∀ V : Subgroup Y, V ≤ Pb → ⁅V, V⁆ = V → ∀ k : ℕ, 3 ^ k ∣ Nat.card V →
    3 ^ k ∣ Nat.card D
  hx : x ∈ D
  hx3 : x ^ 3 = 1
  hxC : x ∉ Subgroup.centralizer (Lb : Set Y)
  free : ∀ W : Subgroup Y, W ≤ Lb → ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({x} : Set Y) →
    W = ⊥

@[expose] def BlockIbRankFam (𝔉 : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Lb Pb D : Subgroup Y) (x : Y), BlockIbParab Lb Pb →
    𝔉 (↥Lb ⧸ Subgroup.center ↥Lb) → BlockIbData Lb Pb D x →
    ∀ E : Subgroup Y, E ≤ Subgroup.normalizer (Lb : Set Y) →
      E ≤ Subgroup.normalizer (Pb : Set Y) → E ≤ Subgroup.centralizer (D : Set Y) →
      CFSG.Open.IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      ∀ t ∈ Subgroup.normalizer (Lb : Set Y), t ∈ Subgroup.normalizer (E : Set Y) →
      (∀ F : Subgroup Y, F ≤ E → Nat.card F = 3 → t ∉ Subgroup.normalizer (F : Set Y)) →
      E ⊓ Subgroup.centralizer (Lb : Set Y) ≠ ⊥

@[expose] def BlockIbAbFam (𝔉 : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Lb Pb D : Subgroup Y) (x : Y), BlockIbParab Lb Pb →
    𝔉 (↥Lb ⧸ Subgroup.center ↥Lb) → BlockIbData Lb Pb D x →
    ∀ U : Subgroup Y, U ≤ Subgroup.normalizer (Lb : Set Y) →
      U ≤ Subgroup.normalizer (Pb : Set Y) → U ≤ Subgroup.centralizer (D : Set Y) →
      IsPGroup 3 U → ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Lb : Set Y)

@[expose] def BlockIbRankRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (x : ↥M ⧸ CFSG.pCore 2 ↥M), BlockThreeIbHyp M S L D x → ¬ NineThreeTwo M S L →
    ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      E ≤ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      E ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      CFSG.Open.IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      ∀ t ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      t ∈ Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (∀ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), F ≤ E → Nat.card F = 3 →
        t ∉ Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M))) →
      E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≠ ⊥

@[expose] def BlockIbAbRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (x : ↥M ⧸ CFSG.pCore 2 ↥M), BlockThreeIbHyp M S L D x → ¬ NineThreeTwo M S L →
    ∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      U ≤ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      U ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsPGroup 3 U →
      ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

theorem nineThree_rest_of_not_two {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (h : BlockThreeIbHyp M S L D x) (h2 : ¬ NineThreeTwo M S L) :
    NineThreeThree M S L ∨ NineThreeFour M S L ∨ NineThreeFive M L ∨ NineThreeSix M S L ∨
      NineThreeSeven M S L ∨ NineThreeEight M S L := by
  obtain ⟨-, -, -, hc, hX, -⟩ := h
  rcases hc with h1 | h' | h'
  · exact absurd h1 hX
  · exact absurd h' h2
  · exact h'

end CFSG.HardMathSupport.Curtis.UnitaryLevi
