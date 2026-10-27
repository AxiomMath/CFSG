module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

@[expose] def KFactTwelveLeCartan : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A) (β : A),
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ →
    IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) → IsParabolicTwo Y P → P ≠ Y →
    ¬ IsSylowTwoOf (pCoreOf 2 P) Y →
    (∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) →
    orderOf β = 3 → β ∈ Subgroup.normalizer (Y : Set A) →
    β ∈ Subgroup.normalizer (P : Set A) → ParabComm.WCent P β → Open.pRank 3 Y ≤ 3 →
    (∀ y ∈ Y, β * y = y * β) ∨
      (∃ D : Subgroup A, Open.IsComponentOf D (Y ⊓ Subgroup.centralizer ({β} : Set A)) ∧
        3 ∣ Nat.card D) ∨
      ((IsLieOver (↥Y ⧸ Subgroup.center ↥Y) (.twistedA 3) 2 1 ∨
          IsLieOver ↥Y (.twistedD 4) 2 1) ∧
        ∀ T : Subgroup A, T ≤ P → IsPGroup 3 T → Nat.card T ≤ 9)

@[expose] def KFactTwelveLeSmall : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A) (β : A),
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ →
    ((∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧
        Nonempty (↥Y ⧸ Subgroup.center ↥Y ≃* alternatingGroup (Fin n))) ∨
      (∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
          (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (↥Y ⧸ Subgroup.center ↥Y ≃* (TauCeti.CFSGIndex.lie d).Group))) →
    IsParabolicTwo Y P → P ≠ Y → ¬ IsSylowTwoOf (pCoreOf 2 P) Y →
    (∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) →
    orderOf β = 3 → β ∈ Subgroup.normalizer (Y : Set A) →
    β ∈ Subgroup.normalizer (P : Set A) → ParabComm.WCent P β →
    ∀ y ∈ Y, β * y = y * β

@[expose] def KFactTwelveLeSolvThree : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A),
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ →
    (IsLieOver (↥Y ⧸ Subgroup.center ↥Y) (.twistedA 3) 2 1 ∨ IsLieOver ↥Y (.twistedD 4) 2 1) →
    IsParabolicTwo Y P → P ≠ Y → ¬ IsSylowTwoOf (pCoreOf 2 P) Y →
    (∀ J : Subgroup A, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J) →
    ∀ T : Subgroup A, T ≤ P → IsPGroup 3 T → Nat.card T ≤ 9

@[expose] def KFactTwelveLeE27 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P E : Subgroup A),
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ →
    (IsLieOver (↥Y ⧸ Subgroup.center ↥Y) (.twistedA 3) 2 1 ∨ IsLieOver ↥Y (.twistedD 4) 2 1) →
    IsParabolicTwo Y P → (∀ T : Subgroup A, T ≤ P → IsPGroup 3 T → Nat.card T ≤ 9) →
    IsElemAbelian 3 E → Nat.card E = 27 → E ≤ Subgroup.normalizer (Y : Set A) →
    E ≤ Subgroup.normalizer (P : Set A) → Open.pRank 3 (Y ⊔ E) ≤ 3 → False

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe
