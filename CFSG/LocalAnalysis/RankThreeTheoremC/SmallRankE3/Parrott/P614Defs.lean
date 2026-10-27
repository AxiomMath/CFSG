module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Fail614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3ZJAny
public import CFSG.LocalAnalysis.GL83PartI.I_28_3_S3
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo pElementSubgroup)
open CFSG.QuasithinUnique.Setup.Family (GL32)
open scoped MatrixGroups

section Data

variable {G : Type} [Group G] [Finite G]

structure Hyp (P : Sylow 3 G) (M : Subgroup G) (x z : G) (H S : Subgroup G) : Prop where
  setting : RankThreeTheoremC.Setting G
  u0 : FullCoreLocal G
  d1 : TheoremD1 G
  situation : SmallRankSituation G 3 P M
  alphaDelta : HasPrimeConstraint (G := M) 3 ∨ SmallRankCaseDelta3 P M
  point : SmallRankPoint P M x
  central : SmallRankCentral P z
  optimal : Fail614Optimal M x z H S
  core_le : rankThreePrimeCore 3 H ≤ M

structure Sit (P : Sylow 3 G) (M : Subgroup G) (x z : G) : Prop where
  setting : RankThreeTheoremC.Setting G
  u0 : FullCoreLocal G
  d1 : TheoremD1 G
  situation : SmallRankSituation G 3 P M
  point : SmallRankPoint P M x
  central : SmallRankCentral P z

structure LocalPair (M : Subgroup G) (x z : G) (N T : Subgroup G) : Prop where
  twoLocal : IsTwoLocal N
  le : zpowers x ⊔ zpowers z ≤ N
  not_le : ¬ N ≤ M
  maxInv : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) N T
  char_le : ∀ S₀ : Subgroup G, S₀ ≤ T → S₀ ≠ ⊥ → (S₀.subgroupOf T).Characteristic →
    normalizer (S₀ : Set G) ≤ M

@[expose] def OmegaLe (x z : G) (N : Subgroup G) : Prop :=
  ∀ Q : Subgroup G, Q ≤ N → IsPGroup 3 Q → zpowers x ⊔ zpowers z ≤ Q →
    ∀ q ∈ Q, q ^ 3 = 1 → q ∈ zpowers x ⊔ zpowers z

structure PComp (p : ℕ) {A : Type} [Group A] [Finite A] (Y H K : Subgroup A) (z : A) :
    Prop where
  le : K ≤ H
  normal : H ≤ normalizer (K : Set A)
  not_le : ¬ K ≤ Y
  mem : zpowers z ≤ K
  rank_one : CFSG.Open.pRank p K = 1
  perfect : ⁅K, K⁆ = K
  lt : K ⊓ rankThreePrimeCore p H < K
  maximal : ∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal →
    K ⊓ rankThreePrimeCore p H ≤ N → N = K ⊓ rankThreePrimeCore p H ∨ N = K

abbrev Kbar (K : Subgroup G) : Type := ↥K ⧸ CFSG.pPrimeCore 3 ↥K

@[expose] def ChevTwoOrAlt (Y : Type) [Group Y] : Prop :=
  IsChevTwo Y ∨ ∃ n : ℕ, Nonempty (Y ≃* alternatingGroup (Fin n))

structure Stage618 (M H K : Subgroup G) (z : G) : Prop where
  comp : PComp 3 M H K z
  alpha : HasPrimeConstraint (G := M) 3
  core_eq : rankThreePrimeCore 3 H = pCoreOf 2 H
  chevAlt : ChevTwoOrAlt (Kbar K)

@[expose] def kRad (H S K : Subgroup G) : Subgroup G :=
  S ⊓ (K ⊔ pCoreOf 2 H)

@[expose] def kPar (H S K : Subgroup G) : Subgroup G :=
  (K ⊔ pCoreOf 2 H) ⊓ normalizer (kRad H S K : Set G)

@[expose] def A5Case (H S K : Subgroup G) : Prop :=
  ∃ f : ↥(K ⊔ S) →* Equiv.Perm (Fin 5), Function.Surjective f ∧
    ∀ y : ↥(K ⊔ S), f y = 1 ↔ (y : G) ∈ pCoreOf 2 H

structure LieCase (M H S K : Subgroup G) (x z : G) : Prop where
  chev : IsChevTwo (Kbar K)
  not_bender : ¬ CFSG.Open.fusionIsBenderGroup (Kbar K)
  rad_gt : pCoreOf 2 H < kRad H S K
  rad_not_sylow : 2 ∣ ((kRad H S K).subgroupOf (K ⊔ pCoreOf 2 H)).index
  par_core : pCoreOf 2 (kPar H S K) = kRad H S K
  par_sylow : ∃ T : Subgroup G, T ≤ kPar H S K ∧ IsPGroup 2 T ∧
    ¬ 2 ∣ (T.subgroupOf (K ⊔ pCoreOf 2 H)).index
  par_mem : zpowers z ≤ kPar H S K
  par_inv : S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (kPar H S K : Set G)
  par_le : kPar H S K ≤ M

@[expose] def KbarA5 (H K : Subgroup G) : Prop :=
  ∃ f : ↥K →* alternatingGroup (Fin 5), Function.Surjective f ∧
    ∀ k : ↥K, f k = 1 ↔ (k : G) ∈ pCoreOf 2 H

@[expose] def KbarL32 (H K : Subgroup G) : Prop :=
  ∃ f : ↥K →* GL32, Function.Surjective f ∧ ∀ k : ↥K, f k = 1 ↔ (k : G) ∈ pCoreOf 2 H

structure Stage620 (H S K : Subgroup G) (x z b : G) : Prop where
  kbar : (KbarA5 H K ∧ A5Case H S K) ∨ KbarL32 H K
  b_mem : b ∈ zpowers x ⊔ zpowers z
  b_not_mem : b ∉ zpowers z
  b_cent : ⁅zpowers b, K⁆ ≤ pCoreOf 2 H

structure Stage620iii (H S : Subgroup G) (z : G) : Prop where
  core : (centralizer (zpowers z : Set G)).relIndex (pCoreOf 2 H) = 4
  sylow : (centralizer (zpowers z : Set G)).relIndex S ≤ 16

end Data

@[expose] def KFact64ii : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (H Q M₀ : Subgroup A) (x z : A),
    p.Prime → p ≠ 2 → CFSG.Open.IsKGroup ↥H → orderOf x = p → orderOf z = p →
    x * z = z * x → x ∉ zpowers z → CFSG.ABGLocalTools.IsSylowOf p Q H →
    zpowers x ⊔ zpowers z ≤ Q → (∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z) →
    x ∉ (frattini ↥Q).map Q.subtype →
    (∀ h ∈ H, h * z * h⁻¹ ∈ zpowers x ⊔ zpowers z → h * z * h⁻¹ ∈ zpowers z) →
    Q ≤ M₀ → M₀ ≤ H → normalizer (zpowers z : Set A) ⊓ H ≤ M₀ →
    ¬ H ≤ M₀ ⊔ rankThreePrimeCore p H →
    (∃ K : Subgroup A, PComp p (M₀ ⊔ rankThreePrimeCore p H) H K z) ∧
      ∃ b ∈ zpowers x ⊔ zpowers z, b ∉ zpowers z ∧
        ¬ CFSG.HasNormalPComplement p ↥(H ⊓ centralizer ({b} : Set A))

@[expose] def KFact64iii : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X Q B U Y S : Subgroup A),
    CFSG.Open.IsKGroup ↥X → CFSG.Open.pRank 3 X = 2 →
    CFSG.ABGLocalTools.IsSylowOf 3 Q X → IsCyclic (Subgroup.center ↥Q) →
    B ≤ Q → IsElemAbelian 3 B → Nat.card B = 9 →
    U ≤ Q → IsElemAbelian 3 U → Nat.card U = 9 →
    (∀ g ∈ X, B.map (MulAut.conj g).toMonoidHom ≠ U) →
    (∀ w ∈ Q, orderOf w = 3 → (∀ q ∈ Q, q * w = w * q) →
      ∀ g ∈ X, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w) →
    Y ≤ X → Y ≠ X →
    (∀ R : Subgroup A, R ≤ U → 1 ≤ CFSG.Open.pRank 3 R → normalizer (R : Set A) ⊓ X ≤ Y) →
    (∀ R : Subgroup A, R ≤ Q → 2 ≤ CFSG.Open.pRank 3 R → normalizer (R : Set A) ⊓ X ≤ Y) →
    X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X →
    rankThreePrimeCore 3 X = pCoreOf 2 X →
    IsMaxTwoInvariantIn B X S → Y ⊔ S ≠ X →
    ∃ Z₀ : Subgroup A, Z₀ ≤ S ∧ Z₀ ≠ ⊥ ∧ (Z₀.subgroupOf S).Characteristic ∧
      X ≤ Y ⊔ (X ⊓ normalizer (Z₀ : Set A))

@[expose] def KFact278 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X Q B U Y : Subgroup A),
    CFSG.Open.IsKGroup ↥X → CFSG.Open.pRank 3 X = 2 →
    CFSG.ABGLocalTools.IsSylowOf 3 Q X → IsCyclic (Subgroup.center ↥Q) →
    B ≤ Q → IsElemAbelian 3 B → Nat.card B = 9 →
    U ≤ Q → IsElemAbelian 3 U → Nat.card U = 9 →
    (∀ g ∈ X, B.map (MulAut.conj g).toMonoidHom ≠ U) →
    (∀ w ∈ Q, orderOf w = 3 → (∀ q ∈ Q, q * w = w * q) →
      ∀ g ∈ X, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w) →
    Y ≤ X → Y ≠ X →
    (∀ R : Subgroup A, R ≤ U → 1 ≤ CFSG.Open.pRank 3 R → normalizer (R : Set A) ⊓ X ≤ Y) →
    (∀ R : Subgroup A, R ≤ Q → 2 ≤ CFSG.Open.pRank 3 R → normalizer (R : Set A) ⊓ X ≤ Y) →
    ∃ K : Subgroup A, K ≤ X ∧ X ≤ normalizer (K : Set A) ∧ ⁅K, K⁆ = K ∧
      K ⊓ rankThreePrimeCore 3 X < K ∧
      (∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal → K ⊓ rankThreePrimeCore 3 X ≤ N →
        N = K ⊓ rankThreePrimeCore 3 X ∨ N = K) ∧
      X ≤ (Y ⊔ K) ⊔ rankThreePrimeCore 3 X ∧
      (Nonempty (Kbar K ≃* (TauCeti.CFSGIndex.sporadic .M12).Group) ∨
        Nonempty (Kbar K ≃* (TauCeti.CFSGIndex.sporadic .M24).Group) ∨
        Nonempty (Kbar K ≃* (TauCeti.CFSGIndex.sporadic .He).Group) ∨
        Nonempty (Kbar K ≃* PSL(3, GaloisField 2 2))) ∧
      (Nonempty (Kbar K ≃* PSL(3, GaloisField 2 2)) →
        ∀ S : Subgroup A, IsTwoInvariantIn B X S → Y ⊔ S ≠ X →
          (rankThreePrimeCore 3 X).relIndex S ≤ 2)

@[expose] def KFactBenderGen : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.fusionIsBenderGroup K →
    ∀ T P : Subgroup K, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → P ≤ normalizer (T : Set K) →
      (Nat.card P).Prime → Odd (Nat.card P) → normalizer (P : Set K) ⊔ T = ⊤

@[expose] def KFactBenderTI : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.fusionIsBenderGroup K →
    ∀ T T' : Sylow 2 K, (T : Subgroup K) ⊓ (T' : Subgroup K) ≠ ⊥ → T = T'

@[expose] def KFact135 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsChevTwo K → ∀ R : Subgroup K, IsPGroup 2 R → R ≠ ⊥ →
      pCoreOf 2 (normalizer (R : Set K)) = R →
      ∃ T : Subgroup K, T ≤ normalizer (R : Set K) ∧ IsPGroup 2 T ∧ ¬ 2 ∣ T.index

@[expose] def KFactTransvRankOne : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ (X K : Subgroup (MulAut V)) (τ : MulAut V), pCoreOf 2 X = ⊥ → τ ∈ X → τ ∉ K →
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsTransvection τ →
      K ≤ X → (K.subgroupOf X).Normal → IsSimpleGroup ↥K → (∃ a b : ↥K, a * b ≠ b * a) →
      (∀ E : Subgroup (MulAut V), E ≤ K → IsElemAbelian 3 E → Nat.card E ≤ 3) →
      X = K ⊔ zpowers τ →
      Nonempty (↥K ≃* alternatingGroup (Fin 5)) ∧ Nonempty (↥X ≃* Equiv.Perm (Fin 5))

@[expose] def KFact3010 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (W K : Subgroup A) (y b : A),
    IsElemAbelian 2 W → K ≤ normalizer (W : Set A) →
    ((∃ f : ↥K →* alternatingGroup (Fin 5), Function.Surjective f ∧
        ∀ k : ↥K, f k = 1 → ∀ w ∈ W, (k : A) * w = w * k) ∨
      (∃ f : ↥K →* GL32, Function.Surjective f ∧
        ∀ k : ↥K, f k = 1 → ∀ w ∈ W, (k : A) * w = w * k)) →
    (∀ U : Subgroup A, U ≤ W → K ≤ normalizer (U : Set A) → U = ⊥ ∨ U = W) →
    y ∈ K → orderOf y = 3 → (centralizer ({y} : Set A)).relIndex W = 4 →
    b ∈ normalizer (W : Set A) →
    (∀ k ∈ K, ∀ w ∈ W, b * (k * w * k⁻¹) * b⁻¹ = k * (b * w * b⁻¹) * k⁻¹) →
    ∀ w ∈ W, b * w = w * b

@[expose] def KFact292 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    primeComplementCore (G := X) 3 = ⊥ →
    ∀ L : Subgroup X, CFSG.Open.IsComponentOf L ⊤ →
      (∀ K : Subgroup X, CFSG.Open.IsComponentOf K ⊤ → K = L) →
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    (∀ (N : Subgroup X) [N.Normal], IsPGroup 3 (X ⧸ N) → N = ⊤) →
    ∀ x : X, orderOf x = 3 → CFSG.Open.pRank 3 (centralizer ({x} : Set X)) = 2 →
    ∀ Px B : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 Px (centralizer ({x} : Set X)) →
      B ≤ Px → IsElemAbelian 3 B → (∀ q ∈ Px, q ^ 3 = 1 → q ∈ B) →
      ∀ T : Subgroup X, IsMaxTwoInvariantIn B ⊤ T →
        CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ CFSG.Open.pRank 3 (normalizer (T : Set X))

@[expose] def PieceDelta4 : Prop :=
  KFactProofs.T29.GL83I291Three → KFactProofs.T29.NoncyclicCentreRank →
    KFactThreeComponentsQRank →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G),
    RankThreeTheoremC.Setting G → FullCoreLocal G → TheoremD1 G →
    SmallRankSituation G 3 P M → SmallRankPoint P M x → SmallRankCentral P z →
    ¬ HasPrimeConstraint (G := M) 3 →
    CFSG.HasNormalPComplement 3 ↥(centralizer ({x} : Set G))

@[expose] def PieceNotDelta : Prop :=
  KFact64ii → KFactSylowNormalizerIrreducible → KFactOutThreePrimeSimple →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (H S : Subgroup G), Hyp P M x z H S → OmegaLe x z H →
    ¬ CFSG.HasNormalPComplement 3 ↥(centralizer ({x} : Set G))

@[expose] def CoreTwo (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G) (x z : G), Sit P M x z → HasPrimeConstraint (G := M) 3 →
    ∀ N T : Subgroup G, LocalPair M x z N T → rankThreePrimeCore 3 N = pCoreOf 2 N

@[expose] def PieceCoreTwo : Prop :=
  KFactRankTwoUniqueness → KFactRankThreeStructure → KFactBlockFactorThreePrime →
    ∀ (G : Type) [Group G] [Finite G], CoreTwo G

@[expose] def OmegaFalse (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G) (x z : G), Sit P M x z →
    ∀ N T : Subgroup G, LocalPair M x z N T → rankThreePrimeCore 3 N = pCoreOf 2 N →
      OmegaLe x z N

@[expose] def PieceOmega : Prop :=
  KFact64iii → ∀ (G : Type) [Group G] [Finite G], OmegaFalse G

@[expose] def PieceDeltaOmega : Prop :=
  KFact64iii → KFactZJFactorizationAny → KFactBlockFactorThreePrime →
    KFactProofs.T29.GL83I291Three → KFactProofs.T29.NoncyclicCentreRank →
    KFactThreeComponentsQRank →
  ∀ (G : Type) [Group G] [Finite G], OmegaFalse G →
  ∀ (P : Sylow 3 G) (M : Subgroup G) (x z : G) (H S : Subgroup G),
    Hyp P M x z H S → ¬ HasPrimeConstraint (G := M) 3 → OmegaLe x z H

@[expose] def PieceCompSylow : Prop :=
  KFactSylowNormalizerIrreducible → KFactOutThreePrimeSimple →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (H S : Subgroup G), Hyp P M x z H S → ¬ 3 ∣ (zpowers x ⊔ zpowers z).relIndex H →
      ∃ K : Subgroup G, PComp 3 M H K z

@[expose] def PieceCompOmega : Prop :=
  KFact64ii →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (H S : Subgroup G), Hyp P M x z H S → OmegaLe x z H →
      3 ∣ (zpowers x ⊔ zpowers z).relIndex H → ∃ K : Subgroup G, PComp 3 M H K z

@[expose] def PieceChevAlt : Prop :=
  KFactZJFactorizationAny →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (H S K : Subgroup G), Hyp P M x z H S → HasPrimeConstraint (G := M) 3 →
    rankThreePrimeCore 3 H = pCoreOf 2 H → PComp 3 M H K z → ChevTwoOrAlt (Kbar K)

@[expose] def Piece620iii : Prop :=
  KFactCampbell → KFactLemma2813 → GL83.I_28_3_S3 →
  ∀ (G : Type) [Group G] [Finite G], OmegaFalse G → CoreTwo G →
  ∀ (P : Sylow 3 G) (M : Subgroup G) (x z : G) (H S K : Subgroup G) (b : G),
    Hyp P M x z H S → Stage618 M H K z → A5Case H S K ∨ LieCase M H S K x z →
    Stage620 H S K x z b → Stage620iii H S z

@[expose] def PieceClosing : Prop :=
  KFact3010 →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (H S K : Subgroup G) (b : G), Hyp P M x z H S → Stage618 M H K z →
    Stage620 H S K x z b → Stage620iii H S z → False

@[expose] def PieceCaseDelta : Prop :=
  KFact292 → KFactProofs.T29.GL83I291Three → KFactProofs.T29.NoncyclicCentreRank →
    KFactThreeComponentsQRank →
  ∀ (G : Type) [Group G] [Finite G], RankThreeTheoremC.Setting G → TheoremD1 G →
    ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z → SmallRankCaseDelta3 P M →
        Fail614NormalizerRank P M (zpowers x ⊔ zpowers z)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
