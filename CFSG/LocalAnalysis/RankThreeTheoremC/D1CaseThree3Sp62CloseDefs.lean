module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62Rank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

@[expose] def KFactSp62Frame : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsSpSixTwoIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ T : Sylow 3 Y,
      ∃ (J : Subgroup Y) (b : Y), J ≤ (T : Subgroup Y) ∧ IsElemAbelian 3 J ∧
        Nat.card J = 3 ^ 3 ∧
        (∀ J' : Subgroup Y, J' ≤ (T : Subgroup Y) → IsElemAbelian 3 J' → Nat.card J' = 3 ^ 3 →
          J' = J) ∧
        (T : Subgroup Y) ⊓ Subgroup.centralizer (J : Set Y) ≤ J ∧
        48 ∣ (Subgroup.centralizer (J : Set Y)).relIndex (Subgroup.normalizer (J : Set Y)) ∧
        b ∈ J ∧ orderOf b = 3 ∧
        (Subgroup.normalizer ((Subgroup.zpowers b : Subgroup Y) : Set Y)).relIndex
          (Subgroup.normalizer (J : Set Y)) = 3 ∧
        ∀ Y₀ : Subgroup Y, (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ →
          ¬ Subgroup.centralizer ({b} : Set Y) ≤ Y₀

@[expose] def KFactOmega8Frame : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsOmegaMinusTwoIndex 4 d → L.Normal → Nonempty (L ≃* CatGroup d) →
    ∀ J : Subgroup Y, J ≤ L → IsElemAbelian 3 J → Nat.card J = 3 ^ 3 →
      (Subgroup.centralizer (J : Set Y)).relIndex (Subgroup.normalizer (J : Set Y)) ∣ 48 ∧
      ∀ b ∈ J, orderOf b = 3 →
        (Subgroup.normalizer ((Subgroup.zpowers b : Subgroup Y) : Set Y)).relIndex
          (Subgroup.normalizer (J : Set Y)) = 3 →
        ∃ W : Subgroup Y, W ≤ L ⊓ Subgroup.centralizer ({b} : Set Y) ∧ IsSimpleGroup W ∧
          (∃ x y : W, x * y ≠ y * x) ∧ 3 ∣ Nat.card W

variable {G : Type} [Group G] [Finite G]

structure Sp62CloseCtx [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R L : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (d : TauCeti.ValidLieTypeIndex) :
    Prop where
  cfg : D1ComponentConfig3 3 P M H R Rbar
  comp : IsComponentOf K ⊤
  uniq : ∀ L' : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L' ⊤ → L' = K
  cent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
    orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype
  idx : IsSpSixTwoIndex d
  iso : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
  shape : Sp62Omega8Shape M H R L
  rp : R = (P : Subgroup G)

end CFSG.LocalAnalysis.RankThreeTheoremC
