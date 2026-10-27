module

public import CFSG.HardMathSupport.Solomon.LocalBalance.InnDiagThree
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EInputs
public import CFSG.Quasithin.Background.F918Z4bAut
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped MatrixGroups

@[expose] def InducesNontrivialFieldAut {X : Type} [Group X] (L : Subgroup X) (y : X) : Prop :=
  ∃ h : y ∈ normalizer (L : Set X),
    IsFieldAutThree (barAut 3 L ⟨y, h⟩) ∧ barAut 3 L ⟨y, h⟩ ≠ 1

@[expose] def InducesInnDiagNonInner {X : Type} [Group X] (L : Subgroup X) (x : X) : Prop :=
  ∃ h : x ∈ normalizer (L : Set X), IsInnDiagThree (barAut 3 L ⟨x, h⟩) ∧
    barAut 3 L ⟨x, h⟩ ∉ (MulAut.conj : ↥L ⧸ CFSG.Open.GLAPPrimeCore 3 ↥L →* _).range

@[expose] def InducesFieldAutL227 {X : Type} [Group X] (L : Subgroup X) (x : X) : Prop :=
  ∃ (e : ↥L ≃* PSL(2, GaloisField 3 3)) (h : x ∈ normalizer (L : Set X)),
    CFSG.Quasithin.autFieldPart (GaloisField 3 3)
      (MulAut.congr e (L.normalizerMonoidHom ⟨x, h⟩)) ≠ 1

@[expose] def GL83I291Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    primeComplementCore (G := X) 3 = ⊥ →
    ∀ L : Subgroup X, IsComponentOf L ⊤ → (∀ K : Subgroup X, IsComponentOf K ⊤ → K = L) →
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ x : X, orderOf x = 3 → CFSG.Open.pRank 3 (centralizer ({x} : Set X)) = 2 →
      IsCyclic (CFSG.pCore 3 X) ∧ (∀ y ∈ CFSG.pCore 3 X, y ^ 3 = 1 → y ∈ L) ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 ∧
      ((CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeEps (↥L ⧸ center ↥L) ∧
          Nat.card (center ↥L) ∣ 3 ∧ InducesInnDiagNonInner L x ∧
          HasNormalPComplement 3 ↥(centralizer ({x} : Set X)) ∧
          ((∃ y : X, IsPGroup 3 (zpowers y) ∧ InducesNontrivialFieldAut L y) ∨
            9 ≤ Nat.card (CFSG.pCore 3 X))) ∨
        InducesFieldAutL227 L x)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
