module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDesc
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Lang.E6Descent

@[expose] def TwE6W0ToralComponentAction :
    Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2), 3 ∣ 2 ^ n + 1 →
    ∀ (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
      (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
      (wd wb : ↥(RecipeExcLang.twInndiagGroup K σ)) (hwd3 : wd ^ 3 = 1)
      (hwd1 : wd ≠ 1) (hwb3 : wb ^ 3 = 1)
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
      (g : ModGL Tag.E6 (AlgebraicClosure K)), g ∈ adjointGroup Tag.E6 (AlgebraicClosure K) →
      g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
        TwistedDiag.n0 (AlgebraicClosure K) →
      (∀ w ∈ ({wd, wb} : Set ↥(RecipeExcLang.twInndiagGroup K σ)),
        g⁻¹ * ((NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ
            Fr hFr w : ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr)) :
              ModGL Tag.E6 (AlgebraicClosure K)) * g ∈
          torusGroup Tag.E6 (AlgebraicClosure K)) →
      ∀ Kc : Subgroup (TwE6Delta.RecipeR K n),
        CFSG.Assembly.IsComponentOf Kc
          (fixedSubgroup (TwE6Transport.recipeConj σ ε wd)) →
        (∀ x ∈ Kc, TwE6Transport.recipeConj σ ε wb x ∈ Kc) →
        InnDiagOn 3 (Subgroup.zpowers (TwE6Transport.recipeConj σ ε wb))
          (Kc.map (MulAut.conj :
            TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)))

@[expose] def TwE6W0ComponentCore :
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
      InnDiagOn 3 (Subgroup.zpowers (TwE6Transport.recipeConj σ ε wb))
        (((J.subgroupOf L).map (piCenterQuot θ)).map (MulAut.conj :
          TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
