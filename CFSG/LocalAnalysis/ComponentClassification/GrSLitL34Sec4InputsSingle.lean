module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

structure GSMaximalSetting (X : Type) [Group X] [Finite X] (a : X) (J : Subgroup X) : Prop where
  simple : IsSimpleGroup X
  nonabelian : ∃ g h : X, g * h ≠ h * g
  kProper : Assembly.KProper Blueprint.Catalog X
  notU : ¬ OutcomeLocal.UOutcome X
  orderOf_eq : orderOf a = 2
  le_centralizer : J ≤ centralizer ({a} : Set X)
  isPComponent : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X)))
  maximal : GSWeakMaximalComponent J
  rank : 3 ≤ pRank 2 ↥J
  not_sp4 : ¬ ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
    Nonempty (J ⧸ Open.fusionZStar J ≃*
      Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 F))
  type : (IsL34Type (J ⧸ Open.fusionZStar J) ∧ L34BaseSetting X) ∨
    IsHeldType (J ⧸ Open.fusionZStar J)

structure SingleComponentSetting (X : Type) [Group X] [Finite X] (a : X) (J W K : Subgroup X) :
    Prop extends GSMaximalSetting X a J where
  ne_bot : W ≠ ⊥
  odd_card : Odd (Nat.card W)
  normalizer_le : normalizer (J : Set X) ≤ normalizer (W : Set X)
  normalizer_ne_top : normalizer (W : Set X) ≠ ⊤
  le_normalizer : K ≤ normalizer (W : Set X)
  isPComponent_K : IsPComponent 2 (K.subgroupOf (normalizer (W : Set X)))
  sup_eq : J ⊔ oddIn (normalizer (W : Set X)) = K ⊔ oddIn (normalizer (W : Set X))

end CFSG.ComponentClassification.GrSLit
