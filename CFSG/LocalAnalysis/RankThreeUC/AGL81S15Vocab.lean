module

public import CFSG.Quasithin.Background.C1GNDefs
public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutCentralAtDef
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E1Sections
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

section XLevel

variable {X : Type} [Group X] [Finite X]

abbrev toStar (T : Subgroup X) : X →* X ⧸ gnC T := QuotientGroup.mk' (gnC T)

@[expose] def O2In (L : Subgroup X) : Subgroup X := L ⊓ CFSG.pCore 2 X

@[expose] def oddHull (L : Subgroup X) : Subgroup X :=
  Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)}

@[expose] def IsC2 (L : Subgroup X) : Prop :=
  CFSG.Open.IsSubnormal L ⊤ ∧ oddHull L = L ∧
    CFSG.Open.IsComponentOf (L.map (QuotientGroup.mk' (CFSG.pCore 2 X))) ⊤

@[expose] def LiftOf (T L : Subgroup X) (Ls : Subgroup (X ⧸ gnC T)) : Prop :=
  IsC2 L ∧ L.map (toStar T) = Ls

@[expose] def Ystar (T T₁ T₂ : Subgroup X) : Subgroup (X ⧸ gnC T) :=
  ⨆ L ∈ {L : Subgroup (X ⧸ gnC T) | GNYComponent T T₁ T₂ L}, L

@[expose] def Y0 (T T₁ T₂ : Subgroup X) : Subgroup X := (Ystar T T₁ T₂).comap (toStar T)

@[expose] def CY (T T₁ T₂ : Subgroup X) : Set (Subgroup X) :=
  {L | ∃ Ls, GNYComponent T T₁ T₂ Ls ∧ LiftOf T L Ls}

noncomputable abbrev mS (T Ti : Subgroup X) (p : ℕ) (Ls : Subgroup (X ⧸ gnC T)) : ℕ :=
  CFSG.Open.pRank p (gnA T Ti Ls)

noncomputable abbrev mN (Ti : Subgroup X) (p : ℕ) : ℕ :=
  CFSG.Open.pRank p (Subgroup.normalizer (Ti : Set X))

@[expose] def GNFactor (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ x : X, ∃ a ∈ Subgroup.centralizer (T₁ : Set X), ∃ y ∈ Y0 T T₁ T₂,
    ∃ b ∈ Subgroup.normalizer (T₂ : Set X), x = a * y * b

@[expose] def gnLayerPre (T : Subgroup X) : Subgroup X :=
  (CFSG.Open.rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T))).comap (toStar T)

@[expose] def GNCoverP (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ A B : Subgroup X, A.Normal → B.Normal → gnC T ≤ B → B ≤ A →
    A ⊓ gnLayerPre T ≤ B → p ∣ B.relIndex A →
      ∃ x ∈ A, x ∉ B ∧ (∃ k : ℕ, orderOf x = p ^ k) ∧
        (x ∈ Subgroup.centralizer (T₁ : Set X) ∨ x ∈ Subgroup.normalizer (T₂ : Set X))

@[expose] def GNCoverSec (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ (S : Type) [Group S], CFSG.Quasithin.E1.IsCompositionFactor X S → ¬ Group.IsSolvable S →
    (∃ (A : Subgroup X) (f : ↥A →* S),
        A ≤ Subgroup.normalizer (T₁ : Set X) ∧ Function.Surjective f) ∨
    (∃ (A : Subgroup X) (f : ↥A →* S),
        A ≤ Subgroup.normalizer (T₂ : Set X) ∧ Function.Surjective f) ∨
    ∃ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls ∧
      ∃ (A : Subgroup (X ⧸ gnC T)) (f : ↥A →* S), A ≤ Ls ∧ Function.Surjective f

@[expose] def RankOneChevTwo (S : Type) [Group S] : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex,
      ((∃ Q : TauCeti.PrimePower, Q.p = 2 ∧ d.1 = .A 1 Q) ∨
        (∃ Q : TauCeti.PrimePower, Q.p = 2 ∧ d.1 = .twistedA 2 Q)) ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    Nonempty (S ≃* alternatingGroup (Fin 5))

@[expose] def GNShape (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
    ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls ∧
      ((IsClassicalTwoOrG2 (↥Ls ⧸ Subgroup.center ↥Ls) ∧
          ¬ RankOneChevTwo (↥Ls ⧸ Subgroup.center ↥Ls)) ∨
        ∃ n : ℕ, (n = 7 ∨ (8 < n ∧ Even n)) ∧ Nonempty (↥Ls ≃* alternatingGroup (Fin n)))

structure GNGood (T T₁ T₂ : Subgroup X) : Prop where
  pair : IsGNPair T T₁ T₂
  parabolic : GNParabolic T T₁ T₂
  three : GNThree T T₁ T₂
  centre : GNCentre T T₁ T₂
  alt7 : GNAlt7 T T₁ T₂
  altBig : GNAltBig T T₁ T₂
  factor : GNFactor T T₁ T₂
  shape : GNShape T T₁ T₂
  c118 : CFSG.Quasithin.IsC118Pair T T₁ T₂
  factorSub : ∀ X₁ : Subgroup X, T ≤ X₁ → GNSetting ↥X₁ (T.subgroupOf X₁) →
    GN15.JOutCentralAt (T.subgroupOf X₁) →
    GNFactor (T.subgroupOf X₁) (T₁.subgroupOf X₁) (T₂.subgroupOf X₁)
  cover : GNCoverP T T₁ T₂ ∧ GNCoverSec T T₁ T₂

@[expose] def S15GNInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∃ T₁ T₂ : Subgroup X, GNGood T T₁ T₂

end XLevel

end CFSG.LocalAnalysis.RankThreeUC.S15
