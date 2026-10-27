module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.RankThree.PartOne.KE.CTLang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE

@[expose] def E6LangTorusExit :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ)
    (K : Type) [Field K] [Finite K] [CharP (AlgebraicClosure K) 2]
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n),
    3 ∣ 2 ^ n - 1 → Setup 3 L J A d b →
    ∀ (θ : ↥L ⧸ Subgroup.center ↥L ≃* TableBExc.RecipeGroup Tag.E6 K)
      (wd wb : ↥(TableBExc.E6Three.hatGroup Tag.E6 K)),
      LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d)
        (MulAut.congr (TableBExc.recipeEquiv Tag.E6 K).symm
          (TableBExc.E6Three.hatAut Tag.E6 K wd)) →
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
        (MulAut.congr (TableBExc.recipeEquiv Tag.E6 K).symm
          (TableBExc.E6Three.hatAut Tag.E6 K wb)) →
      ∀ (w : WeylGroup Tag.E6) (g0 : ModGL Tag.E6 (AlgebraicClosure K)),
        g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K) →
        entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 n g0 =
          g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w →
        (∀ x ∈ ({(wd : ModGL Tag.E6 K), (wb : ModGL Tag.E6 K)} : Set (ModGL Tag.E6 K)),
          baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
            (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
              (entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 n)).map
              (MulAut.conj g0).toMonoidHom) →
        InnDiagOn 3 (Subgroup.zpowers b) J

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
