module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def ReeF4CompInner : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G),
    Setup p L J A d b → catalogIs (PSimple p L) (onLie fun i => ∃ k, i = .reeF4 k) →
      ¬ I171.I171LieShapeAt p L → InducesInnerMod p L b → InnDiagOn p (Subgroup.zpowers b) J

@[expose] def ReeF4CompInnerLarge : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G),
    Setup p L J A d b → 5 ≤ p → catalogIs (PSimple p L) (onLie fun i => ∃ k, i = .reeF4 k) →
      ¬ I171.I171LieShapeAt p L → InducesInnerMod p L b → InnDiagOn p (Subgroup.zpowers b) J

@[expose] def ReeF4CompInnerThree : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G),
    Setup p L J A d b → p = 3 → catalogIs (PSimple p L) (onLie fun i => ∃ k, i = .reeF4 k) →
      ¬ I171.I171LieShapeAt p L → InducesInnerMod p L b → InnDiagOn p (Subgroup.zpowers b) J

theorem reeF4CompInner_of_large_of_three (h : ReeF4CompInnerLarge)
    (h3 : ReeF4CompInnerThree) : ReeF4CompInner := by
  intro G _ _ p L J A d b hS hcat hshape hin
  rcases Nat.lt_or_ge p 5 with hp | hp
  · have hp3 : p = 3 := by
      have h3le : 3 ≤ p := by
        have h2 : 2 ≤ p := hS.prime.two_le
        have ho : p ≠ 2 := hS.odd
        omega
      rcases Nat.lt_or_ge p 4 with h4 | h4
      · omega
      · have hp4 : p = 4 := by omega
        subst hp4
        exact absurd hS.prime (by norm_num)
    exact h3 p L J A d b hS hp3 hcat hshape hin
  · exact h p L J A d b hS hp hcat hshape hin

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
