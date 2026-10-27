module

public import CFSG.Open.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open

@[expose] def IsL34Type (L : Type*) [Group L] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, (∃ Q : TauCeti.PrimePower, Q.card = 4 ∧ d.1 = .A 2 Q) ∧
    Nonempty ((L ⧸ Subgroup.center L) ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsA11Type (L : Type*) [Group L] : Prop :=
  Nonempty (L ≃* alternatingGroup (Fin 11))

@[expose] def IsA6Type (L : Type*) [Group L] : Prop :=
  Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6))

@[expose] def barInf {G : Type*} [Group G] (p : ℕ) (M H : Subgroup G) :
    Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H) :=
  ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))

structure DEmbConfig (X : Type*) [Group X] [Finite X] (Y : Subgroup X) (d : ℕ)
    (W : Subgroup X) : Prop where
  prime : d.Prime
  five_le : 5 ≤ d
  isKGroup : CFSG.Open.IsKGroup X
  pPrimeCore_eq_bot : CFSG.pPrimeCore 3 X = ⊥
  pRank_le_three : pRank 3 (⊤ : Subgroup X) ≤ 3
  not_dvd_card : ¬ d ∣ Nat.card Y
  isPGroup : IsPGroup d W
  three_le_pRank : 3 ≤ pRank d W
  no_normal_index : ∀ N : Subgroup X, N.Normal → N.index ≠ d

structure ZComponentData (X : Type*) [Group X] [Finite X] (Y : Subgroup X) : Prop where
  exists_shape : ∃ L : Subgroup X, CFSG.IsComponent L ∧ ¬ L ≤ Y ∧
    (IsL34Type ↥L ∨ IsA11Type ↥L)
  card_le_two : {C : Subgroup X | CFSG.IsComponent C ∧ ¬ C ≤ Y}.ncard ≤ 2
  two_shapes : ∀ C₁ C₂ : Subgroup X, CFSG.IsComponent C₁ → ¬ C₁ ≤ Y → CFSG.IsComponent C₂ →
    ¬ C₂ ≤ Y → C₁ ≠ C₂ →
      (IsL34Type ↥C₁ ∨ IsA6Type ↥C₁) ∧ (IsL34Type ↥C₂ ∨ IsA6Type ↥C₂)
  five_dvd : (∃ L : Subgroup X, CFSG.IsComponent L ∧ ¬ L ≤ Y ∧ IsA11Type ↥L) → 5 ∣ Nat.card Y

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
