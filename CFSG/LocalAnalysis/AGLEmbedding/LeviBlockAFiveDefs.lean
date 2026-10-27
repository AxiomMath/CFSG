module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

@[expose] def IsFiveComponent {Y : Type} [Group Y] (P : Subgroup Y)
    (C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) : Prop :=
  IsComponentOf C ⊤ ∧ ∃ f : ↥C →* alternatingGroup (Fin 5), Function.Surjective f

@[expose] def TwoFivesSurvivor {Y : Type} [Group Y] (L P : Subgroup Y) : Prop :=
  (∃ (ρ : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2) →* ↥L)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL 4 (GaloisField 2 2)),
      Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2)) ∧
      (∀ g, e (QuotientGroup.mk (ρ g)) = LinearFlag.proj 4 (GaloisField 2 2) g) ∧
      (P.subgroupOf L).comap ρ = LinearFlag.flagStabilizer 4 (GaloisField 2 2) {2}) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 4 ∧
      ∃ ρ : StatedSp 3 K ≃* ↥L,
        (P.subgroupOf L).comap ρ.toMonoidHom = SymplecticHigher.flagStabilizer 3 K {2})

@[expose] def OneFiveOutcome {Y : Type} [Group Y] (L P : Subgroup Y) : Prop :=
  (∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      E ⊓ Subgroup.centralizer (L : Set Y) = ⊥) ∨
  ∃ (ρ : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2) →* ↥L)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL 3 (GaloisField 2 2)) (i : ℕ),
      Function.Bijective ρ ∧
      (∀ g, e (QuotientGroup.mk (ρ g)) = LinearFlag.proj 3 (GaloisField 2 2) g) ∧
      (i = 1 ∨ i = 2) ∧
      (P.subgroupOf L).comap ρ = LinearFlag.flagStabilizer 3 (GaloisField 2 2) {i}

@[expose] def LeviBlocksOfFiveComponents : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), P ≤ L →
    ∀ (K : Type) [Group K] [Finite K] (ρ : K →* ↥L), Function.Surjective ρ →
      ρ.ker ≤ Subgroup.center K →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ j, Group (G j)]
      [∀ j, Finite (G j)] (S : ∀ j, Subgroup (G j))
      (β : ↥((P.subgroupOf L).comap ρ) →* ∀ j, G j), IsPGroup 2 β.ker →
      Subgroup.pi Set.univ S ≤ β.range → ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S →
      (∀ j, Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j)) →
      (∀ C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), IsFiveComponent P C →
        ∃ j, Open.IsQuasisimple (S j) ∧ Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60) ∧
      (∀ C₁ C₂ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), C₁ ≠ C₂ → IsFiveComponent P C₁ →
        IsFiveComponent P C₂ → ∃ j₁ j₂, j₁ ≠ j₂ ∧ Open.IsQuasisimple (S j₁) ∧
          Open.IsQuasisimple (S j₂) ∧ Nat.card (↥(S j₁) ⧸ Subgroup.center ↥(S j₁)) = 60 ∧
          Nat.card (↥(S j₂) ⧸ Subgroup.center ↥(S j₂)) = 60)

@[expose] def KFactCompParabTwoFives : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P → Open.pRank 3 L ≤ 3 →
    ∀ C₁ C₂ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), C₁ ≠ C₂ → IsFiveComponent P C₁ →
      IsFiveComponent P C₂ → TwoFivesSurvivor L P

@[expose] def KFactCompParabOneFive : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    ∀ C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), IsFiveComponent P C → OneFiveOutcome L P

@[expose] def KFactCompParabTwoFivesOn (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → Open.pRank 3 L ≤ 3 →
    ∀ C₁ C₂ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), C₁ ≠ C₂ → IsFiveComponent P C₁ →
      IsFiveComponent P C₂ → TwoFivesSurvivor L P

@[expose] def KFactCompParabOneFiveOn (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) →
    ∀ C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), IsFiveComponent P C → OneFiveOutcome L P

theorem kFactCompParabTwoFives_of_families
    (hA : KFactCompParabTwoFivesOn (IsLieOf IdxA))
    (h2A : KFactCompParabTwoFivesOn (IsLieOf IdxTwistedA))
    (hB : KFactCompParabTwoFivesOn (IsLieOf IdxB))
    (hD : KFactCompParabTwoFivesOn (IsLieOf IdxD))
    (h2D : KFactCompParabTwoFivesOn (IsLieOf IdxTwistedD))
    (hG : KFactCompParabTwoFivesOn (IsLieOf IdxG2))
    (hS : KFactCompParabTwoFivesOn IsSmallTwoOrG2) : KFactCompParabTwoFives := by
  intro Y _ _ L P hCP h3
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h h3, h2A Y L P hCP h h3, hB Y L P hCP h h3, hD Y L P hCP h h3,
    h2D Y L P hCP h h3, hG Y L P hCP h h3, hS Y L P hCP h h3]

theorem kFactCompParabOneFive_of_families
    (hA : KFactCompParabOneFiveOn (IsLieOf IdxA))
    (h2A : KFactCompParabOneFiveOn (IsLieOf IdxTwistedA))
    (hB : KFactCompParabOneFiveOn (IsLieOf IdxB))
    (hD : KFactCompParabOneFiveOn (IsLieOf IdxD))
    (h2D : KFactCompParabOneFiveOn (IsLieOf IdxTwistedD))
    (hG : KFactCompParabOneFiveOn (IsLieOf IdxG2))
    (hS : KFactCompParabOneFiveOn IsSmallTwoOrG2) : KFactCompParabOneFive := by
  intro Y _ _ L P hCP
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h, h2A Y L P hCP h, hB Y L P hCP h, hD Y L P hCP h, h2D Y L P hCP h,
    hG Y L P hCP h, hS Y L P hCP h]

end CFSG.AGLEmbedding
