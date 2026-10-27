module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRGN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRNoX
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Sec4.T444.Statement
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

namespace KFactsPair

@[expose] def indexQ : TauCeti.LieTypeIndex → ℕ
  | .A _ Q | .twistedA _ Q | .B _ Q | .D _ Q | .twistedD _ Q | .G2 Q => Q.card
  | _ => 0

@[expose] def IsLThreeOfExp (n : ℕ) (S : Type) [Group S] : Prop :=
  (n = 1 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), q.card = 7 ∧
      d.1 = .A 1 q ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (2 ≤ n ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 ∧
      Q.exponent = n ∧ d.1 = .A 2 Q ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))

@[expose] def IsLThreeOdd (S : Type) [Group S] : Prop :=
  ∃ n : ℕ, Odd n ∧ IsLThreeOfExp n S

@[expose] def IsUFourOdd (S : Type) [Group S] : Prop :=
  ∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 ∧ Odd Q.exponent ∧
    d.1 = .twistedA 3 Q ∧ Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsLTwoTwoPow (S : Type) [Group S] : Prop :=
  (∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 ∧ d.1 = .A 1 Q ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    Nonempty (S ≃* alternatingGroup (Fin 5))

@[expose] def HasLThreeCore {Y : Type} [Group Y] (A : Subgroup Y) : Prop :=
  IsLThreeOdd ↥(pElementSubgroup 2 (⊤ : Subgroup (↥A ⧸ CFSG.pCore 2 ↥A)))

@[expose] def IsTwoFourSFive {Y : Type} [Group Y] (P : Subgroup Y) : Prop :=
  CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 P) ∧ Nat.card (CFSG.Open.pCoreOf 2 P) = 2 ^ 4 ∧
    Nonempty ((↥P ⧸ CFSG.pCore 2 ↥P) ≃* Equiv.Perm (Fin 5))

@[expose] def IsAltSixCoverThree (L : Type) [Group L] : Prop :=
  CFSG.Open.IsQuasisimple L ∧ Nat.card (Subgroup.center L) = 3 ∧
    Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6))

@[expose] def centerIn {Y : Type} [Group Y] (H : Subgroup Y) : Subgroup Y :=
  (Subgroup.center ↥H).map H.subtype

@[expose] def conjSub {Y : Type} [Group Y] (g : Y) (H : Subgroup Y) : Subgroup Y :=
  H.map (MulAut.conj g).toMonoidHom

@[expose] def IsNaturalLThreeTwo {Y : Type} [Group Y] (L N : Subgroup Y) : Prop :=
  CFSG.Open.IsElemAbelian 2 N ∧ Nat.card N = 2 ^ 3 ∧ L ≤ Subgroup.normalizer (N : Set Y) ∧
    (Subgroup.centralizer (N : Set Y)).relIndex L = 168

end KFactsPair

open KFactsPair

@[expose] def K517_4a : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X), GNSetting X T → GNGood T T₁ T₂ →
    ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ p : ℕ, p.Prime → p ∣ indexQ d.1 ^ 2 - 1 →
          p ∣ Nat.card (gnA T T₁ Ls) ∧ p ∣ Nat.card (gnA T T₂ Ls)

@[expose] def K517_4b : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X), GNSetting X T → GNGood T T₁ T₂ →
    ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ q : ℕ, q.Prime → q ∣ indexQ d.1 - 1 →
          1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls

@[expose] def K517_6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X), GNSetting X T → GNGood T T₁ T₂ →
    ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) → 2 < CFSG.Open.pRank 3 Ls →
      mS T T₁ 3 Ls = 1 → mS T T₂ 3 Ls = 1 →
        IsUFourOdd ↥Ls ∨
          (CFSG.Open.pRank 3 Ls = 3 ∧ (HasLThreeCore (gnA T T₁ Ls) ∨ HasLThreeCore (gnA T T₂ Ls)))

@[expose] def K518 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X), GNSetting X T → GNGood T T₁ T₂ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (Ls : Subgroup (X ⧸ gnC T)) (L : Subgroup X),
      GNYComponent T T₁ T₂ Ls → LiftOf T L Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      mS T T₁ p Ls = 1 → mS T T₂ p Ls = 1 → mN T₁ p = 1 → mN T₂ p = 1 →
        ¬ p ∣ Nat.card (gnC T) ∧
          ((∀ Is, GNYComponent T T₁ T₂ Is → Is ≠ Ls → ¬ p ∣ Nat.card ↥Is) →
            pElementSubgroup p (⊤ : Subgroup X) ≤ Ls.comap (toStar T))

@[expose] def K57 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls →
      ∀ n : ℕ, 0 < n → Even n →
        Nonempty (↥Ls ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) →
        ∀ x : X, toStar T x ∉ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
          centerIn Ls ≠ centerIn (conjSub (toStar T x) Ls)

@[expose] def K541 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls →
      ∀ n : ℕ, IsLThreeOfExp n (↥Ls ⧸ Subgroup.center ↥Ls) →
        Nonempty (↥Ls ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))

@[expose] def KParU5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ∀ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 → d.1 = .twistedA 4 Q →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∃ P : Subgroup (X ⧸ gnC T), IsMinOverBorel Ls (gnImg T T ⊓ Ls) P ∧
          ∀ q : ℕ, q.Prime → q ∣ Q.card + 1 → 2 ≤ CFSG.Open.pRank q (pElementSubgroup 2 P)

@[expose] def K5192 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X), GNSetting X T → GNGood T T₁ T₂ →
    ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      Nonempty (↥Ls ≃* alternatingGroup (Fin 10)) →
      ∃ P₁ P₂ : Subgroup (X ⧸ gnC T), P₁ ≤ Ls ∧ P₂ ≤ Ls ∧
        Nonempty (↥P₁ ≃* Equiv.Perm (Fin 8)) ∧ IsTwoFourSFive P₂ ∧
        oddHull P₁ ≤ gnA T T₁ Ls ∧ (oddHull P₂ ≤ gnA T T₁ Ls ∨ oddHull P₂ ≤ gnA T T₂ Ls)

@[expose] def K55 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls → IsLThreeOfExp 1 ↥Ls →
      ∃ N₁ N₂ : Subgroup X, IsNaturalLThreeTwo (Ls.comap (toStar T)) N₁ ∧
        N₁ ⊔ N₂ = ⁅gnV T, Ls.comap (toStar T)⁆ ∧
        (N₂ = ⊥ ∨ (IsNaturalLThreeTwo (Ls.comap (toStar T)) N₂ ∧ N₁ ⊓ N₂ = ⊥ ∧
          ∃ f : ↥N₁ ≃* ↥N₂, ∀ l ∈ Ls.comap (toStar T), ∀ a b : ↥N₁,
            (b : X) = l * (a : X) * l⁻¹ → (f b : X) = l * (f a : X) * l⁻¹))

@[expose] def K58 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls →
      IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) → ¬ IsLTwoTwoPow (↥Ls ⧸ Subgroup.center ↥Ls) →
      (Nonempty (↥Ls ≃* alternatingGroup (Fin 6)) ∨ IsUThreeThree ↥Ls) →
      ∃ S₀ P : Subgroup (X ⧸ gnC T), CFSG.QuasithinUnique.IsSylowTwoOf S₀ Ls ∧
        IsMinOverBorel Ls S₀ P ∧
        pElementSubgroup 2 (P.comap (toStar T)) ≤
          Subgroup.centralizer ((gnV T ⊓ Subgroup.centralizer
            ((T ⊓ Subgroup.normalizer ((Ls.comap (toStar T) : Subgroup X) : Set X) : Subgroup X) :
              Set X) : Subgroup X) : Set X) ∧
        pElementSubgroup 2 (P.comap (toStar T)) ≤
          Subgroup.centralizer ((CFSG.Quasithin.omegaOneCenterOf T : Subgroup X) : Set X)

@[expose] def K534 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls → IsAltSixCoverThree ↥Ls →
        Nat.card ↥⁅gnV T, Ls.comap (toStar T)⁆ = 2 ^ 6

@[expose] def K542 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls →
      (Nonempty (↥Ls ≃* alternatingGroup (Fin 6)) ∨
        ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), q.card = 3 ∧
          d.1 = .twistedA 2 q ∧ Nonempty (↥Ls ≃* (TauCeti.CFSGIndex.lie d).Group)) →
      ∀ x : X, toStar T x ∈ Subgroup.centralizer (Ls : Set (X ⧸ gnC T)) →
        ∀ u ∈ ⁅gnV T, Ls.comap (toStar T)⁆,
          x * u * x⁻¹ * u⁻¹ ∈ ⁅gnV T, Ls.comap (toStar T)⁆ ⊓
            Subgroup.centralizer ((Ls.comap (toStar T) : Subgroup X) : Set X)

end CFSG.LocalAnalysis.RankThreeUC.S15
