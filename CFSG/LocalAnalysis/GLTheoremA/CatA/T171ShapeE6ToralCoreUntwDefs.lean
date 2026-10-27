module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralExitDefs
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDesc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE

noncomputable abbrev e6RecipeConj
    {K : Type} [Field K] [Finite K] (w : ↥(TableBExc.E6Three.hatGroup Tag.E6 K)) :
    MulAut (TableBExc.RecipeGroup Tag.E6 K) :=
  MulAut.congr (TableBExc.recipeEquiv Tag.E6 K).symm
    (TableBExc.E6Three.hatAut Tag.E6 K w)

@[expose] def E6ToralComponentAction :
    Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP (AlgebraicClosure K) 2]
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n), 3 ∣ 2 ^ n - 1 →
    ∀ (wd wb : ↥(TableBExc.E6Three.hatGroup Tag.E6 K)) (hwd3 : wd ^ 3 = 1)
      (hwd1 : wd ≠ 1) (hwb3 : wb ^ 3 = 1) (w : WeylGroup Tag.E6)
      (g0 : ModGL Tag.E6 (AlgebraicClosure K)),
      g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K) →
      entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 n g0 =
        g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w →
      (∀ x ∈ ({(wd : ModGL Tag.E6 K), (wb : ModGL Tag.E6 K)} : Set (ModGL Tag.E6 K)),
        baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
          (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
            (entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 n)).map
            (MulAut.conj g0).toMonoidHom) →
      ∀ Kc : Subgroup (TableBExc.RecipeGroup Tag.E6 K),
        CFSG.Assembly.IsComponentOf Kc (fixedSubgroup (e6RecipeConj wd)) →
        (∀ x ∈ Kc, e6RecipeConj wb x ∈ Kc) →
        InnDiagOn 3 (Subgroup.zpowers (e6RecipeConj wb))
          (Kc.map (MulAut.conj :
            TableBExc.RecipeGroup Tag.E6 K →* MulAut (TableBExc.RecipeGroup Tag.E6 K)))

@[expose] def E6ComponentCore :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ)
    (K : Type) [Field K] [Finite K] [CharP (AlgebraicClosure K) 2]
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n),
    3 ∣ 2 ^ n - 1 → Setup 3 L J A d b →
    ∀ (θ : ↥L ⧸ Subgroup.center ↥L ≃* TableBExc.RecipeGroup Tag.E6 K)
      (wd wb : ↥(TableBExc.E6Three.hatGroup Tag.E6 K)),
      LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d) (e6RecipeConj wd) →
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (e6RecipeConj wb) →
      ∀ (w : WeylGroup Tag.E6) (g0 : ModGL Tag.E6 (AlgebraicClosure K)),
      g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K) →
      entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 n g0 =
        g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w →
      (∀ x ∈ ({(wd : ModGL Tag.E6 K), (wb : ModGL Tag.E6 K)} : Set (ModGL Tag.E6 K)),
        baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
          (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
            (entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 n)).map
            (MulAut.conj g0).toMonoidHom) →
      InnDiagOn 3 (Subgroup.zpowers (e6RecipeConj wb))
        (((J.subgroupOf L).map (piCenterQuot θ)).map (MulAut.conj :
          TableBExc.RecipeGroup Tag.E6 K →* MulAut (TableBExc.RecipeGroup Tag.E6 K)))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
