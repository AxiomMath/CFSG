module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

@[expose] def KFactCompParabSU38 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    ∀ (O W : Subgroup Y), O ≤ P → P ≤ Subgroup.normalizer (O : Set Y) →
      Nat.Coprime 3 (Nat.card O) → W ≤ P →
      P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup Y) : Set Y) → ⁅W, W⁆ = W →
      ∀ (d : TauCeti.ValidLieTypeIndex) (ψ : ↥W →* CatGroup d), IsUThreeEightIndex d →
        Function.Surjective ψ → 3 ^ 7 ∣ Nat.card P

@[expose] def KFactCompParabThreeFives : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    ∀ (O : Subgroup Y) (J : Fin 3 → Subgroup Y), O ≤ P → P ≤ Subgroup.normalizer (O : Set Y) →
      Nat.Coprime 5 (Nat.card O) →
      (∀ U : Subgroup Y, U ≤ P → ∀ (V : Subgroup U) [V.Normal], O.subgroupOf U ≤ V →
        IsSimpleGroup (U ⧸ V) → (∃ a b : U ⧸ V, a * b ≠ b * a) → Nat.card (U ⧸ V) = 60) →
      (∀ i, J i ≤ P ∧ ∃ φ : ↥(J i) →* alternatingGroup (Fin 5),
        Function.Surjective φ ∧ ∀ x : ↥(J i), φ x = 1 ↔ (x : Y) ∈ O) →
      (∀ i j, i ≠ j → ⁅J i, J j⁆ ≤ O) → 4 ≤ CFSG.Open.pRank 3 P

@[expose] def KFactCompParabLeviU42 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    ¬ 3 ∣ Nat.card (Subgroup.center ↥L) →
    ∀ (O W : Subgroup Y), O ≤ P → P ≤ Subgroup.normalizer (O : Set Y) →
      Nat.Coprime 3 (Nat.card O) → W ≤ P →
      P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup Y) : Set Y) → (W ⊔ O).relIndex P ≤ 2 →
      ⁅W, W⁆ = W → ∀ (d : TauCeti.ValidLieTypeIndex) (ψ : ↥W →* CatGroup d),
        IsUFourTwoIndex d → Function.Surjective ψ → Nat.Coprime 3 (Nat.card ψ.ker) →
        (∀ Q : Sylow 3 ↥P, Nat.card (Q : Subgroup ↥P) = 3 ^ 4) →
        (∃ d : TauCeti.ValidLieTypeIndex, IsUSixTwoIndex d ∧ Nonempty (↥L ≃* CatGroup d) ∧
            P.relIndex L = 693) ∨
          ∃ (m : ℕ) (d : TauCeti.ValidLieTypeIndex), 4 ≤ m ∧ IsOmegaMinusTwoIndex m d ∧
            Nonempty (↥L ≃* CatGroup d) ∧ P.relIndex L = omegaMinusFlagIndex m

@[expose] def SU38At {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) : Prop :=
  ∀ (O W : Subgroup Y), O ≤ P → P ≤ Subgroup.normalizer (O : Set Y) →
    Nat.Coprime 3 (Nat.card O) → W ≤ P →
    P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup Y) : Set Y) → ⁅W, W⁆ = W →
    ∀ (d : TauCeti.ValidLieTypeIndex) (ψ : ↥W →* CatGroup d), IsUThreeEightIndex d →
      Function.Surjective ψ → 3 ^ 7 ∣ Nat.card P

@[expose] def LeviU42At {Y : Type} [Group Y] [Finite Y] (L P : Subgroup Y) : Prop :=
  ¬ 3 ∣ Nat.card (Subgroup.center ↥L) →
    ∀ (O W : Subgroup Y), O ≤ P → P ≤ Subgroup.normalizer (O : Set Y) →
      Nat.Coprime 3 (Nat.card O) → W ≤ P →
      P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup Y) : Set Y) → (W ⊔ O).relIndex P ≤ 2 →
      ⁅W, W⁆ = W → ∀ (d : TauCeti.ValidLieTypeIndex) (ψ : ↥W →* CatGroup d),
        IsUFourTwoIndex d → Function.Surjective ψ → Nat.Coprime 3 (Nat.card ψ.ker) →
        (∀ Q : Sylow 3 ↥P, Nat.card (Q : Subgroup ↥P) = 3 ^ 4) →
        (∃ d : TauCeti.ValidLieTypeIndex, IsUSixTwoIndex d ∧ Nonempty (↥L ≃* CatGroup d) ∧
            P.relIndex L = 693) ∨
          ∃ (m : ℕ) (d : TauCeti.ValidLieTypeIndex), 4 ≤ m ∧ IsOmegaMinusTwoIndex m d ∧
            Nonempty (↥L ≃* CatGroup d) ∧ P.relIndex L = omegaMinusFlagIndex m

@[expose] def FivesAt {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) : Prop :=
  ∀ (O : Subgroup Y) (J : Fin 3 → Subgroup Y), O ≤ P → P ≤ Subgroup.normalizer (O : Set Y) →
    Nat.Coprime 5 (Nat.card O) →
    (∀ U : Subgroup Y, U ≤ P → ∀ (V : Subgroup U) [V.Normal], O.subgroupOf U ≤ V →
      IsSimpleGroup (U ⧸ V) → (∃ a b : U ⧸ V, a * b ≠ b * a) → Nat.card (U ⧸ V) = 60) →
    (∀ i, J i ≤ P ∧ ∃ φ : ↥(J i) →* alternatingGroup (Fin 5),
      Function.Surjective φ ∧ ∀ x : ↥(J i), φ x = 1 ↔ (x : Y) ∈ O) →
    (∀ i j, i ≠ j → ⁅J i, J j⁆ ≤ O) → 4 ≤ CFSG.Open.pRank 3 P

@[expose] def KFactCompParabSU38On (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → SU38At P

@[expose] def KFactCompParabLeviU42On (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → LeviU42At L P

@[expose] def KFactCompParabThreeFivesOn (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → FivesAt P

@[expose] def HasLeviBlocks (Q : Type) [Group Q] (𝒯 : Set ℕ) : Prop :=
  ∃ (k : ℕ) (G : Fin k → Type) (_ : ∀ j, Group (G j)) (_ : ∀ j, Finite (G j))
    (S : ∀ j, Subgroup (G j)) (β : Q →* ∀ j, G j), IsPGroup 2 β.ker ∧
    Subgroup.pi Set.univ S ≤ β.range ∧ ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S ∧
    (∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j)) ∧
    ∀ j, CFSG.Open.IsQuasisimple (S j) → Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) ∈ 𝒯

end CFSG.AGLEmbedding
