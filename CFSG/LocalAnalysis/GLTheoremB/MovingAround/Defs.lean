module

public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs
public import CFSG.LocalAnalysis.GLTheoremB.Prop95
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut IsLocallyBalanced IsWeaklyLocallyBalanced)
open scoped MatrixGroups

section Vocabulary
variable {G : Type*} [Group G]

abbrev Cg (x : G) : Subgroup G := Subgroup.centralizer ({x} : Set G)

abbrev Cg2 (x y : G) : Subgroup G := Subgroup.centralizer ({x, y} : Set G)

@[expose] def IsSylowIn (p : ℕ) (Y R : Subgroup G) : Prop :=
  R ≤ Y ∧ IsPGroup p ↥R ∧ ∀ R' : Subgroup G, R' ≤ Y → IsPGroup p ↥R' → R ≤ R' → R' = R

@[expose] def centerOf (H : Subgroup G) : Subgroup G := (Subgroup.center ↥H).map H.subtype

@[expose] def omegaOne (p : ℕ) (H : Subgroup G) : Subgroup G := Subgroup.closure {x | x ∈ H ∧ x ^ p = 1}

@[expose] noncomputable def thompsonJ [Finite G] (p : ℕ) (R : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : IsEkIn p (CFSG.Open.pRank p R) R E), E

@[expose] def derivedInf (H : Subgroup G) : Subgroup G := ⨅ n : ℕ, (derivedSeries ↥H n).map H.subtype

@[expose] def Covers (p : ℕ) (X M K : Subgroup G) : Prop := barX p X K ≤ barX p X M

@[expose] noncomputable def centBar (p : ℕ) (X L : Subgroup G) : Subgroup G :=
  ((MonoidHom.ker (barAut p L)).map (Subgroup.normalizer (L : Set G)).subtype) ⊓ X

@[expose] def IsMaxInvTwoSub (X A T : Subgroup G) : Prop :=
  T ≤ X ∧ IsPGroup 2 ↥T ∧ A ≤ Subgroup.normalizer (T : Set G) ∧
    ∀ T' : Subgroup G, T' ≤ X → IsPGroup 2 ↥T' → A ≤ Subgroup.normalizer (T' : Set G) → T ≤ T' →
      T' = T

@[expose] def IsInvThreePrimeSub (X A T : Subgroup G) : Prop :=
  T ≤ X ∧ Nat.Coprime 3 (Nat.card T) ∧ A ≤ Subgroup.normalizer (T : Set G)

@[expose] def GConj (A B : Subgroup G) : Prop := ∃ g : G, GLBConj g A = B

@[expose] def IsKConnStep (p k : ℕ) (X U V : Subgroup G) : Prop :=
  IsEkIn p k X U ∧ IsEkIn p k X V ∧ U ≤ Subgroup.centralizer (V : Set G)

@[expose] def IsKConnectedIn (p k : ℕ) (X A B : Subgroup G) : Prop :=
  A ≤ X ∧ IsElemAbelian p A ∧ p ^ k ≤ Nat.card A ∧ B ≤ X ∧ IsElemAbelian p B ∧ p ^ k ≤ Nat.card B ∧
    (A ≤ Subgroup.centralizer (B : Set G) ∨
      ∃ U V : Subgroup G, IsEkIn p k X U ∧ IsEkIn p k X V ∧ A ≤ Subgroup.centralizer (U : Set G) ∧
        Relation.ReflTransGen (IsKConnStep p k X) U V ∧ V ≤ Subgroup.centralizer (B : Set G))

end Vocabulary
section SCstar
variable {G : Type*} [Group G] [Finite G]

@[expose] def IsSCstar (p : ℕ) (M A : Subgroup G) : Prop := IsSCp p M A ∧ 3 ≤ CFSG.Open.pRank p A

@[expose] def inD (p : ℕ) (M A : Subgroup G) : Prop := IsSCstar p M A ∧ IsUniquenessTwoLocal p A M

@[expose] def inDp (p : ℕ) (M A : Subgroup G) : Prop := IsSCstar p M A ∧ ¬ IsUniquenessTwoLocal p A M

@[expose] def inD0 (p : ℕ) (M A₀ : Subgroup G) : Prop :=
  A₀ ≤ M ∧ IsElemAbelian p A₀ ∧ ∃ A : Subgroup G, inD p M A ∧ A₀ ≤ A

@[expose] def inDDp (p : ℕ) (M E A : Subgroup G) : Prop :=
  inD p M E ∧ inDp p M A ∧ 2 ≤ CFSG.Open.pRank p (E ⊓ A)

open scoped Classical in
@[expose] noncomputable def ddKey (p : ℕ) (E A : Subgroup G) : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (CFSG.Open.pRank p (E ⊓ A), toLex (min (CFSG.Open.pRank p E) (CFSG.Open.pRank p A),
    toLex (CFSG.Open.pRank p E, toLex (CFSG.Open.pRank p A, if IsPGroup p ↥(E ⊔ A) then 1 else 0))))

@[expose] def IsDDpStar (p : ℕ) (M E A : Subgroup G) : Prop :=
  inDDp p M E A ∧ ∀ E' A' : Subgroup G, inDDp p M E' A' → ddKey p E' A' ≤ ddKey p E A

@[expose] def TheoremTwoStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M →
      IsUniquenessTwoLocal p B M →
        (GLAWeakCoreLocal G p ∨ GLADeltaZero G p) ∨
          ∀ A : Subgroup G, IsSCstar p M A → IsUniquenessTwoLocal p A M

end SCstar
section Glue
variable {G : Type*} [Group G] [Finite G] {p : ℕ}
end Glue
section Settings
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G}

structure Sec10 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M : Subgroup G) : Prop where
  standing : GLStanding G m p
  bOne : IsBOneMax p B
  pre : IsPreUniquenessTwoLocal p B M
  uniq : IsUniquenessTwoLocal p B M

structure Sec10Fails (G : Type) [Group G] [Finite G] (m p : ℕ) (B M : Subgroup G) : Prop
    extends Sec10 G m p B M where
  notB : ¬ GLAWeakCoreLocal G p
  notStar : ∃ A : Subgroup G, IsSCstar p M A ∧ ¬ IsUniquenessTwoLocal p A M

structure Sec11 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) : Prop
    extends Sec10Fails G m p B M where
  pair : IsDDpStar p M E A

end Settings
section Sec10Statements
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G}

@[expose] def alphaStarOf (p : ℕ) (M : Subgroup G) : Subgroup G :=
  pCoreOf 2 M ⊔ ⨆ (J : Subgroup G) (_ : p = 3 ∧ J ≤ M ∧ IsSubnormal J M ∧ ⁅J, J⁆ = J ∧
    Nonempty ((↥J ⧸ CFSG.pCore 2 ↥J) ≃* alternatingGroup (Fin 7))), J

@[expose] def Lemma912 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M → p = 3 →
      ∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
        IsTwoPrimeComp (alphaStarOf p M ⊓ Subgroup.centralizer ({b} : Set G)) J →
          IsTwoPrimeComp (Subgroup.centralizer ({b} : Set G)) J

end Sec10Statements
section Types

@[expose] def IsAltType (n : ℕ) (X : Type*) [Group X] : Prop := Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def IsSporType (name : TauCeti.SporadicName) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic name).Group)

@[expose] def IsLieChar (P : ℕ → Prop) (X : Type*) [Group X] : Prop :=
  ∃ idx : TauCeti.ValidLieTypeIndex,
    Nonempty ((X ⧸ Subgroup.center X) ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧
      P idx.1.characteristic

@[expose] def IsLTwoTwentySeven (X : Type*) [Group X] : Prop := Nonempty (X ≃* PSL(2, GaloisField 3 3))

@[expose] def IsLpType (p Q : ℕ) (X : Type*) [Group X] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = Q ∧
    Nonempty (X ≃* StatedProj (StatedSL p F))

@[expose] def IsUpType (p Q : ℕ) (X : Type*) [Group X] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = Q ^ 2 ∧
    Nonempty (X ≃* StatedProj (StatedSU p Q F))

@[expose] def IsUnitaryAut {X : Type*} [Group X] (φ : MulAut X) : Prop :=
  orderOf φ = 2 ∧ ∃ P : Subgroup X, IsPGroup 3 ↥P ∧ 9 ∣ Nat.card P ∧ ∀ x ∈ P, φ x = x

end Types
section Balance2

@[expose] def localDeltaTwoIn {M : Type*} [Group M] (H D : Subgroup M) : Subgroup M :=
  ⨅ (d : M) (_ : d ∈ D) (_ : d ≠ 1), pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set M))

@[expose] def IsLocallyOTwoBalanced (p k : ℕ) {K : Type*} [Group K] (A : Subgroup (MulAut K)) : Prop :=
  ∀ D : Subgroup (MulAut K), IsEkIn p k A D → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
    D ≤ Subgroup.normalizer (H : Set (MulAut K)) → localDeltaTwoIn H D = ⊥

@[expose] def IsWeaklyLocallyOTwoBalanced (p k : ℕ) {K : Type*} [Group K] (A : Subgroup (MulAut K)) : Prop :=
  ∀ D : Subgroup (MulAut K), IsEkIn p k A D → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
    A ≤ Subgroup.normalizer (H : Set (MulAut K)) → ⁅localDeltaTwoIn H D, A⁆ = ⊥

@[expose] def IsLocallyOTwoBalancedWrtP (p k : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ A : Subgroup (MulAut K), IsElemAbelian p A → IsLocallyOTwoBalanced p k A

@[expose] def IsWeaklyLocallyOTwoBalancedWrtP (p k : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ A : Subgroup (MulAut K), IsElemAbelian p A → IsWeaklyLocallyOTwoBalanced p k A

variable {G : Type*} [Group G]

@[expose] def IsCompLocallyOTwoBalanced (p k : ℕ) (B L : Subgroup G) : Prop :=
  IsLocallyOTwoBalanced p k (autBar p B L)

end Balance2
section Notation
variable {G : Type*} [Group G] [Finite G]

@[expose] def Lstar (p : ℕ) (X : Subgroup G) : Subgroup G :=
  GLAPPrimeCoreOf p X ⊔ GLAPLayer p X ⊔
    ⨆ (Q : Subgroup G) (_ : IsSylowIn p (GLAPLayer p X) Q),
      GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (Q : Set G))

@[expose] def InducesInner (p : ℕ) (L : Subgroup G) (x : G) : Prop :=
  ∃ k ∈ L, k⁻¹ * x ∈ centBar p ⊤ L

@[expose] def InducesFaithfulInner (p : ℕ) (A₀ K : Subgroup G) : Prop :=
  A₀ ≤ Subgroup.normalizer (K : Set G) ∧ (∀ x ∈ A₀, x ∈ centBar p ⊤ K → x = 1) ∧
    ∀ x ∈ A₀, InducesInner p K x

@[expose] def NormalizesCyc (M A : Subgroup G) (a : G) : Prop :=
  M ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)

end Notation
section PartIInputs

@[expose] def Input31_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ R : Subgroup G, IsPGroup p ↥R →
    ∀ k : ℕ, k ≤ 4 → k ≤ CFSG.Open.pRank p R → ∃ E : Subgroup G, IsEkIn p k R E ∧ (E.subgroupOf R).Normal

@[expose] def Input31_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ R : Subgroup G, IsPGroup p ↥R →
    (∀ A B : Subgroup G, IsEkIn p 5 R A → IsEkIn p 5 R B → IsKConnectedIn p 3 R A B) ∧
      (∀ A B : Subgroup G, IsEkIn p 3 R A → IsEkIn p 3 R B → IsKConnectedIn p 2 R A B)

@[expose] def Input31_7_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ R : Subgroup G, IsPGroup p ↥R →
    ∀ U₁ U₂ : Subgroup G, IsEkIn p 2 R U₁ → IsEkIn p 2 R U₂ → (U₁.subgroupOf R).Normal →
      (U₂.subgroupOf R).Normal → U₁ ≠ U₂ → U₁ ≤ Subgroup.centralizer (U₂ : Set G) →
        ∀ A : Subgroup G, IsEkIn p 4 R A → IsKConnectedIn p 3 R A (U₁ ⊔ U₂)

@[expose] def Input31_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p k : ℕ), p.Prime → 3 ≤ k → ∀ R : Subgroup G, IsPGroup p ↥R →
    ∀ A B : Subgroup G, IsEkIn p k R A → IsEkIn p k R B →
      Relation.ReflTransGen
        (fun U V : Subgroup G => IsEkIn p k R U ∧ IsEkIn p k R V ∧ 2 ≤ CFSG.Open.pRank p (U ⊓ V)) A B

@[expose] def Input31_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p r : ℕ), p.Prime → p ≠ 2 → 2 ≤ r → ¬ (p = 3 ∧ r = 2) →
    ∀ R : Subgroup G, IsPGroup p ↥R → ∀ A B : Subgroup G, IsEkIn p (p ^ (r - 1)) R A →
      IsEkIn p (p ^ (r - 1)) R B → IsKConnectedIn p (r + 1) R A B

@[expose] def Input19_19 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ((∃ n : ℕ, 5 ≤ n ∧ IsAltType n (K ⧸ Subgroup.center K) ∧
        (n % p = 2 ∨ n % p = 4 ∨ (p = 3 ∧ n % 3 ≠ 0))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (K ⧸ Subgroup.center K) ∧
        HasFixedPointFreeOrder ε n p) ∨
      (p = 5 ∧ IsSporType .Fi22 (K ⧸ Subgroup.center K)) ∨
      (p = 3 ∧ (IsLThreeFour (K ⧸ Subgroup.center K) ∨ IsLpType 2 7 (K ⧸ Subgroup.center K) ∨
        IsSporType .He (K ⧸ Subgroup.center K)))) →
    ¬ IsLocallyOTwoBalancedWrtP p 1 K

end PartIInputs
section Sec11Statements
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}
structure Cfg113 (G : Type) [Group G] [Finite G] (m : ℕ) (B M E A : Subgroup G) (a e : G)
    (K Q : Subgroup G) : Prop extends Sec11 G m 3 B M E A where
  ha : a ∈ A ∧ a ≠ 1
  hna : ¬ ∃ A1 : Subgroup G, inD 3 M A1 ∧ a ∈ A1
  h4 : CFSG.Open.pRank 3 E = 4
  h3 : CFSG.Open.pRank 3 A = 3
  he : e ∈ E ⊓ A ∧ e ≠ 1
  hK : GLAPComponent 3 (Cg e) K ∧ IsLTwoTwentySeven (barOf 3 K)
  hQ : IsSylowIn 3 (Cg e) Q ∧ E ⊔ A ≤ Q

@[expose] def Claim113A (E A : Subgroup G) (e : G) (K Q : Subgroup G) : Prop :=
  omegaOne 3 (centerOf Q) = E ⊓ A ∧ Q ≤ M ∧ Cg e ≤ Subgroup.normalizer (K : Set G) ∧
    IsCyclic ↥(centBar 3 Q K) ∧ omegaOne 3 Q = E ⊔ A ∧ E = thompsonJ 3 Q ∧
    ∃ g : G, GLBConj g (Subgroup.zpowers e) ≤ Q ∧ GLBConj g (Subgroup.zpowers e) ≠ Subgroup.zpowers e

@[expose] def Claim113C (E A Q : Subgroup G) : Prop :=
  IsSylowIn 3 (Subgroup.centralizer (E : Set G)) E ∧ Nat.card Q = 3 ^ 5 ∧
    ∃ R : Subgroup G, IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R ∧ Q ≤ R ∧ Nat.card R = 3 ^ 8 ∧
      E = thompsonJ 3 R ∧ IsSylowIn 3 ⊤ R

structure Fails112 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (e a : G) :
    Prop extends Sec11 G m p B M E A where
  ha : a ∈ A ∧ a ≠ 1
  he : e ∈ E ⊓ A ∧ e ≠ 1
  not_i : ¬ GLAPPrimeCoreOf p (Cg2 e a) ≤ M
  not_ii : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1

@[expose] def Type117a (p : ℕ) (E A K : Subgroup G) : Prop :=
  ∃ n : ℕ, IsAltType n (barOf p K) ∧ p ^ CFSG.Open.pRank p (E ⊓ A) < n ∧ ¬ p ∣ n

@[expose] def Type117b (p : ℕ) (K : Subgroup G) : Prop := p = 5 ∧ IsSporType .Fi22 (barOf p K)

@[expose] def Type117c (p : ℕ) (A K : Subgroup G) : Prop :=
  p = 3 ∧ CFSG.Open.pRank p A = 3 ∧ IsLThreeFour (barOf p K ⧸ Subgroup.center (barOf p K))

structure Cex117Base (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G)
    (K : Subgroup G) : Prop extends Sec11 G m p B M E A where
  ha : a ∈ A ∧ a ≠ 1
  hK : GLAPComponent p (Cg a) K
  ht : Type117a p E A K ∨ Type117b p K ∨ Type117c p A K
  notM : ¬ K ≤ M
  notD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1

structure Cex117 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G)
    (K : Subgroup G) : Prop extends Cex117Base G m p B M E A a K where
  choice : (∃ (E' A' : Subgroup G) (a' : G) (K' : Subgroup G),
      Cex117Base G m p B M E' A' a' K' ∧ ¬ NormalizesCyc M A' a') → ¬ NormalizesCyc M A a

@[expose] def InHFamily (A K : Subgroup G) (a : G) (H : Subgroup G) : Prop :=
  IsTwoLocal H ∧ A ≤ H ∧ Covers 3 (Cg a) H K

structure HeisenbergPair (p : ℕ) (A₀ K : Subgroup G) : Prop where
  placeholder : True

end Sec11Statements
section Sec12Statements
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}

@[expose] def Tof (p : ℕ) (M : Subgroup G) (a : G) : Subgroup G := pCoreOf 2 (alphaOf p M ⊓ Cg a)

@[expose] def pPrimePCore (p : ℕ) (X : Subgroup G) : Subgroup G :=
  (((CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map
    X.subtype)

structure Cex121 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G) :
    Prop extends Sec11 G m p B M E A where
  ha : a ∈ A ∧ a ≠ 1
  fails : ¬ Tof p M a ≤ pCoreOf 2 (Cg a)

@[expose] def Kx (p : ℕ) (J : Subgroup G) (x : G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer p (Cg x), GLBConj g J

structure Cex127 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A N D : Subgroup G) : Prop
    extends Sec11 G m p B M E A where
  twoLocal : IsTwoLocal N
  plane : IsEkIn p 2 A D
  hO : pCoreOf 2 M ≤ N
  hD : Subgroup.normalizer (D : Set G) ≤ N
  fails : ¬ pCoreOf 2 M ≤ pCoreOf 2 N

@[expose] def IsPCentralIn (p : ℕ) (X : Subgroup G) (z : G) : Prop :=
  ∃ R : Subgroup G, IsSylowIn p X R ∧ z ∈ centerOf R

@[expose] def Shears (Y : Subgroup G) (z z' : G) : Prop := ∃ y ∈ Y, y⁻¹ * z * y = z * z'

@[expose] def permImage129 {N K : Subgroup G} (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13)))
    (H : Subgroup (↥N ⧸ GLAPPrimeCore 3 ↥N)) : Subgroup (Equiv.Perm (Fin 13)) :=
  (H.subgroupOf (barX 3 N K)).map ((alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom)

@[expose] def Lemma129IvAOrbit {N K : Subgroup G} (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13)))
    (E A : Subgroup G) : Prop :=
  ∃ i : Fin 13, Set.ncard (MulAction.orbit ↥(permImage129 φ (barX 3 N (E ⊓ A))) i) = 9

@[expose] def Lemma129IvAComplement {N K : Subgroup G}
    (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13))) (A F : Subgroup G) (a : G) : Prop :=
  IsEkIn 3 2 A F ∧
    Set.ncard {j : Fin 13 | ∀ g ∈ permImage129 φ (barX 3 N F), g j = j} = 4 ∧
    (∀ j k : Fin 13, (∃ g ∈ permImage129 φ (barX 3 N F), g j ≠ j) →
        (∃ g ∈ permImage129 φ (barX 3 N F), g k ≠ k) →
        ∃! g : Equiv.Perm (Fin 13), g ∈ permImage129 φ (barX 3 N F) ∧ g j = k) ∧
    a ∈ A ∧ A = F ⊔ Subgroup.zpowers a ∧ F ⊓ Subgroup.zpowers a = ⊥ ∧
    ∀ g ∈ permImage129 φ (barX 3 N (Subgroup.zpowers a)), g ≠ 1 →
      Equiv.Perm.IsThreeCycle g ∧
        ∀ j : Fin 13, (∃ h ∈ permImage129 φ (barX 3 N F), h j ≠ j) → g j = j

@[expose] def Lemma129IvAData (N K E A : Subgroup G) : Prop :=
  ∃ φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13)),
    Lemma129IvAOrbit φ E A ∧ ∃ (F : Subgroup G) (a : G), Lemma129IvAComplement φ A F a

@[expose] def Lemma129IvBData (p : ℕ) (N K E A : Subgroup G) : Prop :=
  ∃ (D : Type) (_ : Group D), ((∃ q : ℕ, p ∣ q - 1 ∧ IsLpType p q D) ∨ (p = 5 ∧ IsSporType .Fi22 D)) ∧
    ∃ e : ↥(barX p N (⨆ g ∈ A, GLBConj g K) ⊔ barX p N A) ≃*
        RegularWreathProduct D (Multiplicative (ZMod p)),
      ∃ F : Subgroup G, IsEkIn p 2 A F ∧ barX p N F ≤ barX p N (⨆ g ∈ A, GLBConj g K) ∧
        ∃ a ∈ E ⊓ A, A = F ⊔ Subgroup.zpowers a ∧
          Subgroup.map (RegularWreathProduct.rightHom.comp e.toMonoidHom)
              ((barX p N (Subgroup.zpowers a)).subgroupOf
                (barX p N (⨆ g ∈ A, GLBConj g K) ⊔ barX p N A)) = ⊤

@[expose] def Lemma129Common (p : ℕ) (M E A N K : Subgroup G) : Prop :=
  GLAPComponent p N K ∧ (CFSG.Open.pRank p A = 3 ∧ CFSG.Open.pRank p (E ⊓ A) = 2) ∧
    ¬ Covers p N M K ∧
    (GLAPLayer p N = ⨆ g ∈ A, GLBConj g K ∧ CFSG.pCore p (↥N ⧸ GLAPPrimeCore p ↥N) = ⊥)

end Sec12Statements
section Sec13Statements
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}

@[expose] def Iof (p : ℕ) (M D : Subgroup G) : Subgroup G :=
  ⨆ (L : Subgroup G) (_ : GLAPComponent p M L ∧
    ¬ barX p M (gammaStar p D) ≤
      Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M))), L

@[expose] def Istar (p : ℕ) (M D : Subgroup G) : Subgroup G := ⨆ g ∈ M, GLBConj g (Iof p M D)

structure Sec13 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A D T : Subgroup G) : Prop
    extends Sec11 G m p B M E A where
  hD : IsEkIn p 2 A D
  hT1 : pCoreOf 2 M ≤ T
  hT2 : T ≤ gammaStar p D
  hN : ¬ Subgroup.normalizer (T : Set G) ≤ M
  hAB : IsPGroup p ↥(A ⊔ B)
  choiceB : ∀ B' : Subgroup G, (∃ y ∈ M, B' = GLBConj y B) → IsPGroup p ↥(A ⊔ B') →
    B' ≤ Subgroup.normalizer (T : Set G) → B ≤ Subgroup.normalizer (T : Set G)

structure Cex134 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A D T L : Subgroup G) : Prop
    extends Sec13 G m p B M E A D T where
  hL : GLAPComponent p (Iof p M D) L
  notAB : ¬ (Prop95Alpha p M D L ∨ Prop95Beta p M D L)

@[expose] def Lstarsub (D L : Subgroup G) : Subgroup G := ⨆ d ∈ D, GLBConj d L

abbrev Nof (T : Subgroup G) : Subgroup G := Subgroup.normalizer (T : Set G)

@[expose] def Prop139a (p : ℕ) (M D : Subgroup G) : Prop :=
  3 < p ∧ Iof p M D = Istar p M D ∧ ∃ L : Subgroup G, GLAPComponent p (Iof p M D) L ∧
    Iof p M D = L ∧ CFSG.Open.pRank p L = 1 ∧
      (IsAltType (p + 2) (barOf p L) ∨
        ∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) (barOf p L) ∧
          HasFixedPointFreeOrder ε n p)

@[expose] def Prop139b (p : ℕ) (M D : Subgroup G) : Prop :=
  p = 3 ∧ ∀ L : Subgroup G, GLAPComponent p (Istar p M D) L → IsAltType 5 (barOf p L)

structure Cex1310 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A D T R L0 : Subgroup G) (d : G) :
    Prop extends Sec13 G m p B M E A D T where
  h139 : Prop139a p M D ∨ Prop139b p M D
  hd : d ∈ D ∧ d ≠ 1
  hL0 : GLAPComponent p (piLayer p (Istar p M D ⊓ Cg d)) L0
  notCov : ¬ barX p M L0 ≤ barX p M (piStar p D)
  hR : IsSylowIn p M R ∧ A ⊔ B ≤ R
  hL0iso : ∀ L : Subgroup G, GLAPComponent p (Istar p M D) L → Nonempty (barOf p L0 ≃* barOf p L)

@[expose] def L1of (p : ℕ) (M D L0 : Subgroup G) : Subgroup G := ⨆ g ∈ Istar p M D, GLBConj g L0

@[expose] def IsU1312 (p : ℕ) (B M D L0 : Subgroup G) (d : G) (U : Subgroup G) : Prop :=
  IsEkIn p 2 B U ∧ U ≤ Cg d ∧ U ⊓ L0 ≠ ⊥ ∧ centBar p U (L1of p M D L0) ≠ ⊥

end Sec13Statements
section Assembly
variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G}
end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
