module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I171Facts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Torus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent

@[expose] def TwE6Marking : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G), Setup 3 L J A d b →
    catalogIs (PSimple 3 L) (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧ i = .twistedE6 q) →
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ n ∧ 3 ∣ 2 ^ n + 1 ∧
      Nat.card K = (2 ^ n) ^ 2 ∧ IsSimpleGroup (TwE6Delta.RecipeR K n) ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K n,
        ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n,
          LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ

@[expose] def E6Marking : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G), Setup 3 L J A d b →
    catalogIs (PSimple 3 L) (onLie fun i => ∃ q, I171.I171LieShape 3 i ∧ i = .E6 q) →
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ n ∧ 3 ∣ 2 ^ n - 1 ∧
      Nat.card K = 2 ^ n ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃*
          LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false),
        ∀ a ∈ A, ∃ φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K
            (LargeEvenChevH (LargeEvenCartanE 6) K false),
          LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ

@[expose] def TwE6BigToralExit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ)
    (K : Type) [Field K] [Finite K], 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
    Setup 3 L J A d b →
    ∀ (θ : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K n)
      (E : Subgroup (MulAut (TwE6Delta.RecipeR K n))),
      IsElemAbelian 3 E → 3 ^ 5 ≤ Nat.card E → (∀ φ ∈ E, φ ∈ TwE6Delta.RecipeI K n) →
      (∃ φ ∈ E, LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d) φ) →
      (∃ φ ∈ E, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      InnDiagOn 3 (Subgroup.zpowers b) J

@[expose] def E6BigToralExit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ)
    (K : Type) [Field K] [Finite K], 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
    Setup 3 L J A d b →
    ∀ (θ : ↥L ⧸ Subgroup.center ↥L ≃*
        LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
      (E : Subgroup (MulAut (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)))),
      IsElemAbelian 3 E → 3 ^ 5 ≤ Nat.card E →
      (∀ φ ∈ E, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenChevH (LargeEvenCartanE 6) K false)) →
      (∃ φ ∈ E, LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d) φ) →
      (∃ φ ∈ E, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      InnDiagOn 3 (Subgroup.zpowers b) J

@[expose] def TwE6W0TorusExit :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ)
    (K : Type) [Field K] [Finite K] (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2),
    3 ∣ 2 ^ n + 1 → Setup 3 L J A d b →
    ∀ (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
      (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K n)
      (wd wb : ↥(RecipeExcLang.twInndiagGroup K σ)),
      LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d)
        (TwE6Transport.recipeConj σ ε wd) →
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
        (TwE6Transport.recipeConj σ ε wb) →
      ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
        (g : ModGL Tag.E6 (AlgebraicClosure K)), g ∈ adjointGroup Tag.E6 (AlgebraicClosure K) →
        g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
          TwistedDiag.n0 (AlgebraicClosure K) →
        (∀ w ∈ ({wd, wb} : Set ↥(RecipeExcLang.twInndiagGroup K σ)),
          g⁻¹ * ((NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr w :
              ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr)) :
                ModGL Tag.E6 (AlgebraicClosure K)) * g ∈
            torusGroup Tag.E6 (AlgebraicClosure K)) →
        InnDiagOn 3 (Subgroup.zpowers b) J

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
