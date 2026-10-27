module

public import CFSG.Yardstones.M0362f3a873a3.Definitions
public import CFSG.GH74.GLS.Classes
public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG.Open CFSG.Yardstones.M0362f3a873a3

@[expose] def HRClassical (Q : Type) [Group Q] : Prop :=
  ∃ (t : StatedLieTag) (n p f : ℕ), p.Prime ∧ p ≠ 2 ∧ StatedLieAdmissible t n p f ∧
    CFSG.Blueprint.LieModel Q t n p f ∧ CFSG.ClassicalInvolution.Generic.IsFundTag t ∧
    ¬ (t = .PSL ∧ n = 2) ∧ (5 ≤ p ^ f ∨ t = .trialityD4)

@[expose] def HRF3HigherRank (Q : Type) [Group Q] : Prop :=
  ∃ (t : StatedLieTag) (n : ℕ), CFSG.Blueprint.LieModel Q t n 3 1 ∧
    ((t = .PSL ∧ 5 ≤ n) ∨ (t = .PSU ∧ 5 ≤ n) ∨ (t = .PSp ∧ 3 ≤ n) ∨ (t = .POmegaOdd ∧ 4 ≤ n) ∨
      (t = .POmegaPlus ∧ 5 ≤ n) ∨ (t = .POmegaMinus ∧ 5 ≤ n) ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨
      t = .E8 ∨ t = .twistedE6)

@[expose] def HRG23 (Q : Type) [Group Q] : Prop :=
  CFSG.Blueprint.LieModel Q .G2 0 3 1

structure HRSetting (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop where
  std : CFSG.OddStandard.StandardSetting G L
  notCat : ¬ CFSG.Blueprint.Catalog G
  balanced : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥
  lie : CFSG.Blueprint.OddLieType (L ⧸ center L)
  notF3 : ¬ SmallF3LieQuotient (L ⧸ center L)
  notL2Ree : ¬ L2OrReeLieQuotient (L ⧸ center L)
  notA5 : ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5))
  notA6 : ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6))
  notHSF : ¬ CFSG.OddStandard.HarrisSolomonFritzScope L
  centre : Odd (Nat.card (center L)) ∨
    ∃ p n r : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < n ∧ 0 < r ∧
      (CFSG.Blueprint.LieModel (L ⧸ center L) .PSL (2 * n) p r ∨
        CFSG.Blueprint.LieModel (L ⧸ center L) .PSU (2 * n) p r) ∧
      ordProj[2] (Nat.card (center L)) ≠
        ordProj[2] (Nat.card (CFSG.Open.griessHopfMultiplier (L ⧸ center L)))
  cyclic : ∃ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G)))

@[expose] def CatalogCaseHolds : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.OddStandard.StandardSetting G L →
    CFSG.Blueprint.Catalog G → CFSG.Blueprint.OddLieType (L ⧸ center L) →
    ¬ SmallF3LieQuotient (L ⧸ center L) → ¬ L2OrReeLieQuotient (L ⧸ center L) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) → CFSG.Blueprint.OddLieType G

@[expose] def ClassicalFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L →
    HRClassical (L ⧸ center L) → False

@[expose] def F3HigherRankFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L →
    HRF3HigherRank (L ⧸ center L) → False

@[expose] def G23StandardFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L →
    HRG23 (L ⧸ center L) → False

@[expose] def BlowUpAFalse : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog X → ¬ CFSG.Blueprint.Catalog X →
    (∀ z : X, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set X)) = ⊥) →
    ∀ (v : X) (M : Subgroup X), orderOf v = 2 → M ≤ centralizer ({v} : Set X) →
      CFSG.IsPComponent 2 (M.subgroupOf (centralizer ({v} : Set X))) →
      CFSG.GH74.GLS.IsL34Quotient (↥M ⧸ CFSG.pPrimeCore 2 ↥M) →
      Nat.card ↥(center (↥M ⧸ CFSG.pPrimeCore 2 ↥M)) = 16 → False

end CFSG.OddStandard.HigherRank
