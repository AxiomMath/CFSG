module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

@[expose] def I294CrossLargePrimeOn (φ : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    (∃ a b : L, a * b ≠ b * a) → ∀ d : TauCeti.ValidLieTypeIndex, φ d.1 →
    d.1.characteristic ≠ p →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt p L →
    (∃ S : Sylow p L, ¬ IsMulCommutative (S : Subgroup L)) →
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup L)

@[expose] def I294CrossThreeRankThreeOn (φ : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, φ d.1 → d.1.characteristic ≠ 3 →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt 3 L →
    (∃ S : Sylow 3 L, ¬ IsMulCommutative (S : Subgroup L)) → ¬ 3 ^ 5 ∣ Nat.card L →
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3 →
    ∀ x : L, orderOf x = 3 → 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set L))

@[expose] def I294CrossThreeRankTwoOn (φ : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, φ d.1 → d.1.characteristic ≠ 3 →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt 3 L →
    (∃ S : Sylow 3 L, ¬ IsMulCommutative (S : Subgroup L)) →
    CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 2 → ¬ 3 ^ 4 ∣ Nat.card L →
      ∀ α : MulAut L, (∃ k : ℕ, α ^ 3 ^ k = 1) → α ∈ (MulAut.conj : L →* MulAut L).range

theorem I294CrossLargePrime.of_split {φ : TauCeti.LieTypeIndex → Prop}
    (h₁ : I294CrossLargePrimeOn φ) (h₂ : I294CrossLargePrimeOn fun d => ¬ φ d) :
    I294CrossLargePrime := by
  intro p hp h5 L _ _ hs hn d hd e hLU hS
  by_cases hφ : φ d.1
  · exact h₁ p hp h5 L hs hn d hφ hd e hLU hS
  · exact h₂ p hp h5 L hs hn d hφ hd e hLU hS

theorem I294CrossThreeRankThree.of_split {φ : TauCeti.LieTypeIndex → Prop}
    (h₁ : I294CrossThreeRankThreeOn φ) (h₂ : I294CrossThreeRankThreeOn fun d => ¬ φ d) :
    I294CrossThreeRankThree := by
  intro L _ _ hs hn d hd e hLU hS h5 hr x hx
  by_cases hφ : φ d.1
  · exact h₁ L hs hn d hφ hd e hLU hS h5 hr x hx
  · exact h₂ L hs hn d hφ hd e hLU hS h5 hr x hx

@[expose] def I294CrossIsG2 : TauCeti.LieTypeIndex → Prop
  | .G2 _ => True
  | _ => False

@[expose] def I294CrossIsReeF4 : TauCeti.LieTypeIndex → Prop
  | .reeF4 _ => True
  | _ => False

@[expose] def I294CrossIsTits : TauCeti.LieTypeIndex → Prop
  | .tits => True
  | _ => False

@[expose] def I294CrossIsClassical : TauCeti.LieTypeIndex → Prop
  | .A _ _ => True
  | .twistedA _ _ => True
  | .B _ _ => True
  | .C _ _ => True
  | .D _ _ => True
  | .twistedD _ _ => True
  | _ => False

theorem I294CrossThreeRankTwo.of_families (hG2 : I294CrossThreeRankTwoOn I294CrossIsG2)
    (hRee : I294CrossThreeRankTwoOn I294CrossIsReeF4)
    (hTits : I294CrossThreeRankTwoOn I294CrossIsTits)
    (hRest : I294CrossThreeRankTwoOn fun d =>
      ¬ I294CrossIsG2 d ∧ ¬ I294CrossIsReeF4 d ∧ ¬ I294CrossIsTits d) :
    I294CrossThreeRankTwo := by
  intro L _ _ hs hn d hd e hLU hS hr h81
  by_cases hG : I294CrossIsG2 d.1
  · exact hG2 L hs hn d hG hd e hLU hS hr h81
  · by_cases hR : I294CrossIsReeF4 d.1
    · exact hRee L hs hn d hR hd e hLU hS hr h81
    · by_cases hT : I294CrossIsTits d.1
      · exact hTits L hs hn d hT hd e hLU hS hr h81
      · exact hRest L hs hn d ⟨hG, hR, hT⟩ hd e hLU hS hr h81

theorem I294CrossThreeRankThree.of_classical (h₁ : I294CrossThreeRankThreeOn I294CrossIsClassical)
    (h₂ : I294CrossThreeRankThreeOn fun d => ¬ I294CrossIsClassical d) :
    I294CrossThreeRankThree :=
  I294CrossThreeRankThree.of_split h₁ h₂

theorem I294CrossLargePrime.of_classical (h₁ : I294CrossLargePrimeOn I294CrossIsClassical)
    (h₂ : I294CrossLargePrimeOn fun d => ¬ I294CrossIsClassical d) : I294CrossLargePrime :=
  I294CrossLargePrime.of_split h₁ h₂

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
