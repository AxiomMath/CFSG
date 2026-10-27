module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut IsLocallyBalanced IsWeaklyLocallyBalanced)
open scoped MatrixGroups

@[expose] def Clause_d_of_clause_cStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {p : ℕ} {A N : Subgroup G} (hN : GLAIsMaxTwoLocal N) (hAN : A ≤ N)
    (hA : IsElemAbelian p A) (hA2 : 2 ≤ CFSG.Open.pRank p A)
    (hc : ∀ D : Subgroup G, D ≤ A → IsPPlane p D →
      pCoreOf 2 N ≤ gammaStar p D ∧ ∀ T : Subgroup G, pCoreOf 2 N ≤ T → T ≤ gammaStar p D →
        Subgroup.normalizer (T : Set G) ≤ N),
    GLBCore p 2 A ≤ N
@[expose] def IsUniquenessTwoLocal_conjStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {p : ℕ} {A N : Subgroup G} (h : IsUniquenessTwoLocal p A N) {y : G}
    (hy : y ∈ N),
    IsUniquenessTwoLocal p (GLBConj y A) N
@[expose] def Lemma912Statement : Prop :=
    Lemma912
@[expose] def Lemma101_iStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M) {A F : Subgroup G} {y : G} (hy : y ∈ M)
    (hA : inD p M A) (hF : inDp p M F),
    inD p M (GLBConj y A) ∧ inDp p M (GLBConj y F)
@[expose] def Lemma101_iiStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M),
    inD p M B
@[expose] def Lemma102Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M) {Q : Subgroup G} (hQM : Q ≤ M) (hQ : IsPGroup p ↥Q)
    {k : ℕ} (hk : 2 ≤ k) (hne : ∃ E : Subgroup G, IsEkIn p k Q E)
    (hsub : ∀ E : Subgroup G, IsEkIn p k Q E → inD0 p M E),
    Subgroup.normalizer (Q : Set G) ≤ M
@[expose] def Lemma103Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M),
    ∃ E A : Subgroup G, inDDp p M E A
@[expose] def Lemma104_iStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M) {E A : Subgroup G} (hEA : IsDDpStar p M E A),
    IsPGroup p ↥(E ⊔ A)
@[expose] def Lemma104_iiStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M) {E A : Subgroup G} (hEA : IsDDpStar p M E A),
    IsSCp p ⊤ E ∧ IsSCp p ⊤ A
@[expose] def Lemma104_iiiStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M) {E A : Subgroup G} (hEA : IsDDpStar p M E A)
    {Es E0 : Subgroup G} (hEs : IsSCp p ⊤ Es) (hE0 : inD p M E0)
    (hconn : IsKConnectedIn p (CFSG.Open.pRank p (E ⊓ A) + 1) ⊤ Es E0),
    inD p M Es
@[expose] def Lemma104_ivStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M) {E A : Subgroup G} (hEA : IsDDpStar p M E A)
    (hk : CFSG.Open.pRank p (E ⊓ A) = 2) {R : Subgroup G} (hR : IsSylowIn p M R),
    (∀ E5 : Subgroup G, IsEkIn p 5 R E5 → inD0 p M E5) ∧ GLBCore p 5 R ≤ M ∧ IsSylowIn p ⊤ R
@[expose] def Lemma104_vStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M) {E A : Subgroup G} (hEA : IsDDpStar p M E A)
    (h3 : CFSG.Open.pRank p E = 3 ∨ CFSG.Open.pRank p A = 3) {R : Subgroup G} (hR : IsSylowIn p M R),
    (∀ E4 : Subgroup G, IsEkIn p 4 R E4 → inD0 p M E4) ∧ GLBCore p 4 R ≤ M
@[expose] def Lemma104_viStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M) {E A : Subgroup G} (hEA : IsDDpStar p M E A)
    (h3 : CFSG.Open.pRank p E = 3),
    CFSG.Open.pRank p A = 3
@[expose] def Lemma113_iStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hna : ¬ ∃ A1 : Subgroup G, inD 3 M A1 ∧ a ∈ A1),
    4 ≤ CFSG.Open.pRank 3 E
@[expose] def Lemma113_ii_piece0Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G} (h : Cfg113 G m B M E A a e K Q),
    ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G)
@[expose] def Lemma113_ii_pieceAStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G} (h : Cfg113 G m B M E A a e K Q)
    (h0 : ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G)),
    Claim113A (M := M) E A e K Q
@[expose] def Lemma113_ii_pieceBStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G} (h : Cfg113 G m B M E A a e K Q)
    (hA : Claim113A (M := M) E A e K Q),
    ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)
@[expose] def Lemma113_ii_pieceCStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G} (h : Cfg113 G m B M E A a e K Q)
    (hA : Claim113A (M := M) E A e K Q)
    (hB : ¬ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)),
    Claim113C E A Q
@[expose] def Lemma113_ii_pieceDStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G} (h : Cfg113 G m B M E A a e K Q)
    (hC : Claim113C E A Q),
    False
@[expose] def Lemma114Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {e a : G} (h : Fails112 G m p B M E A e a),
    GLAPPrimeCoreOf p (Cg e) ≤ M ∧ CFSG.Open.pRank p (E ⊓ A) = 2 ∧
      ∃ K : Subgroup G, GLAPComponent p (Cg e) K ∧
        ⁅barX p (Cg e) K, barX p (Cg e) (GLAPPrimeCoreOf p (Cg2 e a))⁆ ≠ ⊥ ∧
          ¬ Covers p (Cg e) (M ⊓ Cg e) K
@[expose] def Prop112Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A) {a e : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (he : e ∈ E ⊓ A) (he1 : e ≠ 1),
    GLAPPrimeCoreOf p (Cg2 e a) ≤ M ∨ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1
@[expose] def Prop111Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1),
    GLAPPrimeCoreOf p (Cg a) ≤ M
@[expose] def Lemma116Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A) {a e : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (he : e ∈ E ⊓ A) (he1 : e ≠ 1) {K : Subgroup G} (hK : GLAPComponent p (Cg e) K) {n : ℕ}
    (hn : IsAltType n (barOf p K)) (hpn : ¬ p ∣ n),
    K ≤ M ∨ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1
@[expose] def Prop115Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A) {a e : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (he : e ∈ E ⊓ A) (he1 : e ≠ 1) {J : Subgroup G} (hJ : GLAPComponent p (Cg2 e a) J)
    (h1 : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p J))
    (h2 : p = 3 → IsLTwoTwentySeven (barOf p J) → ¬ IsCompLocallyOTwoBalanced p 1 A J),
    J ≤ M ∨ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1
@[expose] def Lemma118Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K),
    Type117b p K ∨ Type117c p A K
@[expose] def Lemma119Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K),
    CFSG.Open.pRank p (E ⊓ A) = 2 ∧ InducesFaithfulInner p (E ⊓ A) K
@[expose] def Lemma1110Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K),
    Type117c p A K
@[expose] def Lemma1111Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K),
    p = 3 ∧ CFSG.Open.pRank 3 A = 3 ∧ IsLThreeFour (barOf 3 K)
@[expose] def Lemma1112Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K),
    (IsSylowIn 3 (centBar 3 (Cg a) K) (Subgroup.zpowers a) ∧ CFSG.Open.pRank 3 (Cg a) = 3) ∧
      E ⊓ A = A ⊓ K ∧
        ∀ U : Subgroup G, IsEkIn 3 1 A U → (¬ U ≤ E ⊓ A ↔ GConj (Subgroup.zpowers a) U)
@[expose] def Lemma1113Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K),
    ∀ e ∈ E ⊓ A, e ≠ 1 → GLAPLayer 3 (M ⊓ Cg e) = ⊥ ∧
      GLAPPrimeCoreOf 3 (M ⊓ Cg e) ≤ GLAPPrimeCoreOf 3 M
@[expose] def Lemma1114Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K),
    (⨆ (T : Subgroup G) (_ : IsInvThreePrimeSub ⊤ A T), T) ≤ GLAPPrimeCoreOf 3 M
@[expose] def Lemma1115_iStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K),
    ∃ H : Subgroup G, InHFamily A K a H
@[expose] def Lemma1115_iiStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K) {H T : Subgroup G}
    (hH : InHFamily A K a H) (hT : IsMaxInvTwoSub H A T),
    ∃ T0 : Subgroup G, T0 ≠ ⊥ ∧ IsCharIn T0 T ∧ InHFamily A K a (Subgroup.normalizer (T0 : Set G))
@[expose] def Lemma1115_iiiStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K) {H : Subgroup G}
    (hH : InHFamily A K a H),
    ¬ barX 3 M ⊤ ≤ barX 3 M H
@[expose] def Prop117_cex_falseStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K),
    False
@[expose] def Prop1116Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {K : Subgroup G}
    (hK : GLAPComponent p (Cg a) K) (hq : IsLieChar (fun q => q ≠ 2 ∧ q ≠ p) (barOf p K)),
    K ≤ M ∨ (∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1) ∨
      ((∃ Q : ℕ, (IsLpType p Q (barOf p K ⧸ Subgroup.center (barOf p K)) ∧ p ∣ Q - 1) ∨
          (IsUpType p Q (barOf p K ⧸ Subgroup.center (barOf p K)) ∧ p ∣ Q + 1)) ∧
        E ⊓ A ≤ Subgroup.normalizer (K : Set G) ∧ Nat.card (E ⊓ A : Subgroup G) = p ^ 2 ∧
          (∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1) ∧ HeisenbergPair p (E ⊓ A) K) ∨
      (p = 13 ∧ CFSG.Open.pRank 13 A = 3 ∧ (IsLpType 3 (3 ^ 13) (barOf p K) ∨ IsLieChar (· = 3) (barOf p K)))
@[expose] def Prop1117Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1),
    piOf p a ≤ M
@[expose] def Lemma122_i_iiStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a),
    (∀ e ∈ E ⊓ A, e ≠ 1 → Tof p M a ⊓ Cg e ≤ pCoreOf 2 (Cg2 e a)) ∧
      ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1
@[expose] def Lemma122_iiiStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a) {F : Subgroup G} (hF : IsEkIn p 2 A F),
    ∃ V : G → Subgroup G,
      (∀ x ∈ F, x ≠ 1 → V x ≤ Tof p M a ⊓ Subgroup.centralizer (A : Set G)) ∧
      Tof p M a ⊓ Subgroup.centralizer (A : Set G) =
        (Tof p M a ⊓ Subgroup.centralizer (A : Set G) ⊓ pCoreOf 2 M) ⊔
          ⨆ (x : G) (_ : x ∈ F) (_ : x ≠ 1), V x ∧
      ∀ x ∈ F, x ≠ 1 →
        V x ≤ derivedInf (⨆ g ∈ (alphaOf p M ⊓ Cg x), GLBConj g (V x))
@[expose] def Lemma123Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a),
    p = 3 ∧ ∃ K : Subgroup G, GLAPComponent 3 (Cg a) K ∧
      (IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) ∧ ¬ Covers 3 (Cg a) (M ⊓ Cg a) K) ∧
      (∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
        ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩)) ∧
      (Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K) ∧
      Tof p M a ≤ Lstar p (Cg a)
@[expose] def Lemma124Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a) {K : Subgroup G}
    (hK : GLAPComponent 3 (Cg a) K) (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (hu₀ : ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K),
    let F := centBar 3 A K
    let J := GLAPLayer 3 (K ⊓ Subgroup.centralizer (F : Set G))
    (A = (E ⊓ A) ⊔ F ∧ (E ⊓ A) ⊓ F = ⊥ ∧ A = (A ⊓ J) ⊔ F ∧ (A ⊓ J) ⊓ F = ⊥ ∧
      Nat.card (A ⊓ J : Subgroup G) = 9 ∧ CFSG.Open.pRank 3 F = 2 ∧ CFSG.Open.pRank 3 A = 4) ∧
    (∀ x ∈ F, x ≠ 1 →
      Cg x ≤ Subgroup.normalizer (Kx 3 J x : Set G) ∧ barX 3 (Kx 3 J x) J = ⊤) ∧
    (IsLThreeFour (barOf 3 J) ∧ ∀ x ∈ F, x ≠ 1 → IsLThreeFour (barOf 3 (Kx 3 J x))) ∧
    (∃ u ∈ pCoreOf 2 M ⊓ Tof p M a ⊓ Subgroup.centralizer (A : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (J : Set G), IsUnitaryAut (barAut 3 J ⟨u, hu⟩))
@[expose] def Lemma125Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a) {K : Subgroup G}
    (hK : GLAPComponent 3 (Cg a) K) (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (hu₀ : ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K),
    let F := centBar 3 A K
    let J := GLAPLayer 3 (K ⊓ Subgroup.centralizer (F : Set G))
    let W := ⨆ (x : G) (_ : x ∈ F) (_ : x ≠ 1), M ⊓ Cg x
    (J ⊔ W ≠ ⊤) ∧ pCoreOf 2 (J ⊔ W) ≤ pCoreOf 2 M ∧
      ∃ Js : Subgroup G, IsTwoPrimeComp (J ⊔ W) Js ∧ J ≤ Js ∧
        IsLThreeFour (↥Js ⧸ CFSG.pCore 2 ↥Js)
@[expose] def Prop121_of_cexStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a),
    False
@[expose] def Prop121_corStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1),
    pCoreOf 2 M ⊓ Cg a ≤ pCoreOf 2 (Cg a)
@[expose] def Prop126Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {J : Subgroup G}
    (hJ : IsTwoPrimeComp (alphaOf 3 M ⊓ Cg a) J),
    IsTwoPrimeComp (Cg a) J
@[expose] def Lemma128Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A) (hE : CFSG.Open.pRank 3 E ≤ 4) (hA : CFSG.Open.pRank 3 A = 3) {x : G}
    (hx : x ∈ M) (hx3 : orderOf x = 3),
    pCoreOf 2 M ⊓ Cg x ≤ pCoreOf 2 (Cg x)
@[expose] def Lemma129Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {N D : Subgroup G} (h : Cex127 G m p B M E A N D),
    ∃ K : Subgroup G, GLAPComponent p N K ∧
      (CFSG.Open.pRank p A = 3 ∧ CFSG.Open.pRank p (E ⊓ A) = 2) ∧ ¬ Covers p N M K ∧
      (GLAPLayer p N = ⨆ g ∈ A, GLBConj g K ∧
        CFSG.pCore p (↥N ⧸ GLAPPrimeCore p ↥N) = ⊥) ∧
      ((p = 3 ∧ 5 ≤ CFSG.Open.pRank 3 E ∧ IsAltType 13 (barOf 3 K) ∧ barX 3 N A ≤ barX 3 N K) ∨
        (((∃ Q : ℕ, p ∣ Q - 1 ∧ IsLpType p Q (barOf p K)) ∨ (p = 5 ∧ IsSporType .Fi22 (barOf p K))) ∧
          ∃ F : Subgroup G, IsEkIn p 2 A F ∧ ∃ a ∈ E ⊓ A, A = F ⊔ Subgroup.zpowers a))
@[expose] def Lemma129PrintedStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {N D : Subgroup G} (h : Cex127 G m p B M E A N D),
    ∃ K : Subgroup G, Lemma129Common p M E A N K ∧
      ((p = 3 ∧ 5 ≤ CFSG.Open.pRank 3 E ∧ IsAltType 13 (barOf 3 K) ∧ barX 3 N A ≤ barX 3 N K ∧
          Lemma129IvAData N K E A) ∨
        (((∃ Q : ℕ, p ∣ Q - 1 ∧ IsLpType p Q (barOf p K)) ∨ (p = 5 ∧ IsSporType .Fi22 (barOf p K))) ∧
          Lemma129IvBData p N K E A))
@[expose] def Lemma1210Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {N D : Subgroup G} (h : Cex127 G m p B M E A N D) {K F : Subgroup G}
    {a : G} (hK : Lemma129Common p M E A N K)
    (h3 : p = 3 ∧ 5 ≤ CFSG.Open.pRank 3 E ∧ IsAltType 13 (barOf 3 K) ∧ barX 3 N A ≤ barX 3 N K)
    (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13))) (hOrb : Lemma129IvAOrbit φ E A)
    (hF : Lemma129IvAComplement φ A F a),
    ∃ z ∈ A, z ≠ 1 ∧ IsPCentralIn p M z ∧ ¬ Cg z ≤ M ∧
      (∀ x ∈ A, x ≠ 1 → ∃ Q : Subgroup G, IsSylowIn 3 N Q ∧ x ∈ centerOf Q ∧ A ≤ Q ∧ ¬ Q ≤ M) ∧
      (z ∈ F ∨ ∃ z' ∈ F, z' ≠ 1 ∧ Shears (N ⊓ M ⊓ Subgroup.normalizer (A : Set G)) z z')
@[expose] def Lemma1210_bStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {N D : Subgroup G} (h : Cex127 G m p B M E A N D) {K : Subgroup G}
    (hK : Lemma129Common p M E A N K)
    (hb : ((∃ Q : ℕ, p ∣ Q - 1 ∧ IsLpType p Q (barOf p K)) ∨ (p = 5 ∧ IsSporType .Fi22 (barOf p K))) ∧
      Lemma129IvBData p N K E A),
    ∃ z ∈ A, z ≠ 1 ∧ IsPCentralIn p M z ∧ ¬ Cg z ≤ M
@[expose] def Lemma1211Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {N D : Subgroup G} (h : Cex127 G m p B M E A N D) {z : G} (hz : z ∈ A ∧ z ≠ 1)
    (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M),
    (∃ R : Subgroup G, IsSylowIn p (Cg z) R ∧ A ≤ R ∧ R ≤ M) ∧
      p = 3 ∧
      ∀ R : Subgroup G, IsSylowIn 3 (Cg z) R → A ≤ R → R ≤ M →
        let R₁ := R ⊓ pPrimePCore 3 (Cg z)
        (IsCyclic (centerOf R₁) ∧ R₁ = centerOf R₁ ⊔ omegaOne 3 R₁ ∧ Nat.card (omegaOne 3 R₁) = 3 ^ 5 ∧
          ⁅omegaOne 3 R₁, omegaOne 3 R₁⁆ = centerOf (omegaOne 3 R₁) ∧
          Nat.card (centerOf (omegaOne 3 R₁)) = 3) ∧ A ≤ R₁
@[expose] def Prop127_of_cexStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {N D : Subgroup G} (h : Cex127 G m p B M E A N D),
    False
@[expose] def Sec10Fails_conjStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M) {y : G} (hy : y ∈ M),
    Sec10Fails G m p (GLBConj y B) M
@[expose] def Exists_conj_pGroupStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M : Subgroup G} (h : Sec10Fails G m p B M) {A : Subgroup G} (hA : IsElemAbelian p A)
    (hAM : A ≤ M),
    ∃ y ∈ M, IsPGroup p ↥(A ⊔ GLBConj y B)
@[expose] def Prop131Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A) {D : Subgroup G} (hD : IsEkIn p 2 A D),
    pCoreOf 2 M ≤ gammaStar p D ∧ gammaStar p D ≤ M
@[expose] def Prop132Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A),
    ∃ D T : Subgroup G, IsEkIn p 2 A D ∧ pCoreOf 2 M ≤ T ∧ T ≤ gammaStar p D ∧
      ¬ Subgroup.normalizer (T : Set G) ≤ M
@[expose] def Lemma133Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G} (h : Sec13 G m p B M E A D T),
    Iof p M D ≠ ⊥ ∧ ∀ L : Subgroup G, GLAPComponent p (Istar p M D) L →
      (IsGLBlock M L ∧ IsPiGroup p (↥L ⧸ CFSG.pCore 2 ↥L) ∧
        ¬ IsHatSeven (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
      (B ≤ Subgroup.normalizer (L : Set G) ∧ B = (B ⊓ L) ⊔ centBar p B L ∧
        (B ⊓ L) ⊓ centBar p B L = ⊥ ∧ CFSG.Open.pRank p (B ⊓ L) = CFSG.Open.pRank p L)
@[expose] def Lemma135_iStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T L : Subgroup G} (h : Cex134 G m p B M E A D T L),
    barX 3 M B ⊓ Subgroup.centralizer
      ((barX 3 M D ⊔ barX 3 M (Lstarsub D L) : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≠ ⊥
@[expose] def Lemma135_iiStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T L : Subgroup G} (h : Cex134 G m p B M E A D T L)
    (hDL : barX 3 M D ≤ Subgroup.normalizer ((barX 3 M L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore 3 ↥M)))
    (hnn : ¬ barX 3 M L ≤ ⊥ ∧ ¬ (∀ g : ↥M ⧸ GLAPPrimeCore 3 ↥M,
      g ∈ Subgroup.normalizer ((barX 3 M L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)))),
    2 ≤ CFSG.Open.pRank 3 (barX 3 M B ⊓ Subgroup.centralizer
      ((barX 3 M D ⊔ barX 3 M L : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)))
@[expose] def Lemma136Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T L : Subgroup G} (h : Cex134 G m p B M E A D T L),
    (D ≤ Subgroup.normalizer (L : Set G) ∧ ∀ x ∈ D, x ∈ centBar 3 ⊤ L → x = 1) ∧
      ∀ d ∈ D, d ≠ 1 → pCoreOf 2 (L ⊓ Cg d) ≤ GLAPPrimeCoreOf 3 (Cg d)
@[expose] def Prop134_of_cexStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T L : Subgroup G} (h : Cex134 G m p B M E A D T L),
    False
@[expose] def Lemma137_iStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G} (h : Sec13 G m p B M E A D T),
    B ≤ Nof T
@[expose] def Lemma137_ii_iiiStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G} (h : Sec13 G m p B M E A D T) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) (hL1 : 3 < p ∨ 2 ≤ CFSG.Open.pRank p L),
    barX p (Nof T) (derivedInf (Nof T ⊓ L)) =
        ⁅barX p (Nof T) (Nof T ⊓ L), barX p (Nof T) (Nof T ⊓ L)⁆ ∧
      IsSimpleGroup ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) ∧
      ¬ IsMulCommutative ↥(barX p (Nof T) (derivedInf (Nof T ⊓ L))) ∧
      (∀ (ε : Bool) (n : ℕ), IsOmegaTwo ε (n + 1) (↥L ⧸ CFSG.pCore 2 ↥L) →
        (barX p M T ≤ Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
            Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
          IsOmegaTwo ε (n + 1) ↥(barX p (Nof T) (Nof T ⊓ L))) ∧
        (¬ barX p M T ≤ Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
            Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
          Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* ↥(StatedSp n (ZMod 2))))) ∧
      (∀ k : ℕ, IsAltType (k * p + 2) (↥L ⧸ CFSG.pCore 2 ↥L) →
        (barX p M T ≤ Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
            Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
          IsAltType (k * p + 2) ↥(barX p (Nof T) (Nof T ⊓ L))) ∧
        (¬ barX p M T ≤ Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
            Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
          Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* Equiv.Perm (Fin (k * p)))))
@[expose] def Lemma137_iv_vStatement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G} (h : Sec13 G m p B M E A D T) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) (hL1 : 3 < p ∨ 2 ≤ CFSG.Open.pRank p L),
    (∃ F : Subgroup G, F ≤ B ∧ Nat.card B ≤ p ^ 2 * Nat.card F ∧
      GLAPLayer p (barX p (Nof T) (derivedInf (Nof T ⊓ L)) ⊓
        Subgroup.centralizer ((barX p (Nof T) F : Subgroup (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T))) :
          Set (↥(Nof T) ⧸ GLAPPrimeCore p ↥(Nof T)))) ≠ ⊥) ∧
    (B = (B ⊓ L) ⊔ centBar p B L ∧ (B ⊓ L) ⊓ centBar p B L = ⊥) ∧
    (B = (B ⊓ derivedInf (Nof T ⊓ L)) ⊔ centBar p B (derivedInf (Nof T ⊓ L)) ∧
      CFSG.Open.pRank p (B ⊓ derivedInf (Nof T ⊓ L)) = CFSG.Open.pRank p (derivedInf (Nof T ⊓ L)))
@[expose] def Lemma138Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G} (h : Sec13 G m p B M E A D T) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) (hL1 : 3 < p ∨ 2 ≤ CFSG.Open.pRank p L),
    IsComponentOf (barX p (Nof T) (derivedInf (Nof T ⊓ L))) ⊤
@[expose] def Prop139Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G} (h : Sec13 G m p B M E A D T),
    Prop139a p M D ∨ Prop139b p M D
@[expose] def Lemma1311Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G} (h : Sec13 G m p B M E A D T)
    (h139 : Prop139a p M D ∨ Prop139b p M D),
    barX p M (Istar p M D) =
        ⨆ (d : G) (_ : d ∈ D) (_ : d ≠ 1), barX p M (piLayer p (Istar p M D ⊓ Cg d)) ∧
      ∀ d ∈ D, d ≠ 1 → ∀ J : Subgroup G, GLAPComponent p (piLayer p (Istar p M D ⊓ Cg d)) J →
        ∀ L : Subgroup G, GLAPComponent p (Istar p M D) L → Nonempty (barOf p J ≃* barOf p L)
@[expose] def Lemma1312Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T R L0 : Subgroup G} {d : G} (h : Cex1310 G m p B M E A D T R L0 d),
    ∃ U : Subgroup G, IsU1312 p B M D L0 d U ∧ (Prop139a p M D → U ≤ centerOf R)
@[expose] def Lemma1313Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T R L0 : Subgroup G} {d : G} (h : Cex1310 G m p B M E A D T R L0 d)
    {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) {b : G} (hb : b ∈ centBar p U (L1of p M D L0))
    (hb1 : b ≠ 1),
    let L1b := GLAPLayer p (L1of p M D L0 ⊓ Cg b)
    let L0b := GLAPLayer p (L0 ⊓ Cg b)
    let L := ⨆ g ∈ GLAPLayer p (Cg d), GLBConj g L0b
    (∃ S : Set (Subgroup G), (∀ X ∈ S, GLAPComponent p (Cg b) X) ∧ L1b = ⨆ X ∈ S, X) ∧
    (GLAPComponent p (Cg d) L ∧ GLAPComponent p (L ⊓ Cg b) L0b ∧
      ∀ L' : Subgroup G, GLAPComponent p (Istar p M D) L' → Nonempty (barOf p L0b ≃* barOf p L')) ∧
    ¬ L ≤ M ∧ ¬ L ≤ piOf p d
@[expose] def Lemma1314Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T R L0 : Subgroup G} {d : G} (h : Cex1310 G m p B M E A D T R L0 d)
    (h139a : Prop139a p M D),
    (R = (R ⊓ Iof p M D) ⊔ centBar p R (Iof p M D) ∧ (R ⊓ Iof p M D) ⊓ centBar p R (Iof p M D) = ⊥ ∧
        CFSG.Open.pRank p (R ⊓ Iof p M D) = 1) ∧
      (¬ ∃ A1 : Subgroup G, inD p M A1 ∧ d ∈ A1) ∧
      (∀ U : Subgroup G, IsU1312 p B M D L0 d U → U ≤ centerOf R → ∃ z ∈ U, z ≠ 1 ∧ ∃ H0 : Subgroup G,
        GLAPComponent p (Cg2 d z) H0 ∧ ¬ H0 ≤ M ∧
          (Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0)))) ∧
      CFSG.Open.pRank p A = 3
@[expose] def Lemma1315Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T R L0 : Subgroup G} {d : G} (h : Cex1310 G m p B M E A D T R L0 d)
    (h139a : Prop139a p M D) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) (hUR : U ≤ centerOf R)
    {z : G} {H0 : Subgroup G} (hz : z ∈ U ∧ z ≠ 1)
    (hH0 : GLAPComponent p (Cg2 d z) H0) (hH0M : ¬ H0 ≤ M)
    (hH0t : Prop95Iv.InChevTwo (barOf p H0) ∨ (p = 5 ∧ IsAltType 7 (barOf p H0))),
    let H := ⨆ g ∈ GLAPLayer p (Cg z), GLBConj g H0
    ((p = 5 ∨ p = 7) ∧ IsLpType 2 p (barOf p H0) ∧ IsLpType 2 (p ^ p) (barOf p H) ∧
        IsCyclic ↥(centBar p R H) ∧ d ∈ Subgroup.normalizer (H : Set G) ∧ ¬ InducesInner p H d) ∧
      IsSylowIn p ⊤ R ∧ R ≤ Subgroup.normalizer (B : Set G) ∧
        Subgroup.zpowers z = omegaOne p (R ⊓ Iof p M D)
@[expose] def Lemma1316Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T R L0 : Subgroup G} {d : G} (h : Cex1310 G m p B M E A D T R L0 d),
    ¬ Prop139a p M D
@[expose] def Prop1310_a5Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T R L0 : Subgroup G} {d : G} (h : Cex1310 G m p B M E A D T R L0 d)
    (h139b : Prop139b p M D),
    False
@[expose] def Prop1310Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G} (h : Sec13 G m p B M E A D T),
    barX p M (Istar p M D) ≤ barX p M (piStar p D)
@[expose] def Final_of_prop1310Statement : Prop :=
∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G} (h : Sec13 G m p B M E A D T)
    (hcov : barX p M (Istar p M D) ≤ barX p M (piStar p D)),
    False
structure MovingAroundLeaves : Prop where
  clause_d_of_clause_c : Clause_d_of_clause_cStatement
  isUniquenessTwoLocal_conj : IsUniquenessTwoLocal_conjStatement
  lemma912 : Lemma912Statement
  lemma101_i : Lemma101_iStatement
  lemma101_ii : Lemma101_iiStatement
  lemma102 : Lemma102Statement
  lemma103 : Lemma103Statement
  lemma104_i : Lemma104_iStatement
  lemma104_ii : Lemma104_iiStatement
  lemma104_iii : Lemma104_iiiStatement
  lemma104_iv : Lemma104_ivStatement
  lemma104_v : Lemma104_vStatement
  lemma104_vi : Lemma104_viStatement
  lemma113_i : Lemma113_iStatement
  lemma113_ii_piece0 : Lemma113_ii_piece0Statement
  lemma113_ii_pieceA : Lemma113_ii_pieceAStatement
  lemma113_ii_pieceB : Lemma113_ii_pieceBStatement
  lemma113_ii_pieceC : Lemma113_ii_pieceCStatement
  lemma113_ii_pieceD : Lemma113_ii_pieceDStatement
  lemma114 : Lemma114Statement
  prop112 : Prop112Statement
  prop111 : Prop111Statement
  lemma116 : Lemma116Statement
  prop115 : Prop115Statement
  lemma118 : Lemma118Statement
  lemma119 : Lemma119Statement
  lemma1110 : Lemma1110Statement
  lemma1111 : Lemma1111Statement
  lemma1112 : Lemma1112Statement
  lemma1113 : Lemma1113Statement
  lemma1114 : Lemma1114Statement
  lemma1115_i : Lemma1115_iStatement
  lemma1115_ii : Lemma1115_iiStatement
  lemma1115_iii : Lemma1115_iiiStatement
  prop117_cex_false : Prop117_cex_falseStatement
  prop1116 : Prop1116Statement
  prop1117 : Prop1117Statement
  lemma122_i_ii : Lemma122_i_iiStatement
  lemma122_iii : Lemma122_iiiStatement
  lemma123 : Lemma123Statement
  lemma124 : Lemma124Statement
  lemma125 : Lemma125Statement
  prop121_of_cex : Prop121_of_cexStatement
  prop121_cor : Prop121_corStatement
  prop126 : Prop126Statement
  lemma128 : Lemma128Statement
  lemma129 : Lemma129Statement
  lemma129_printed : Lemma129PrintedStatement
  lemma1210 : Lemma1210Statement
  lemma1210_b : Lemma1210_bStatement
  lemma1211 : Lemma1211Statement
  prop127_of_cex : Prop127_of_cexStatement
  sec10Fails_conj : Sec10Fails_conjStatement
  exists_conj_pGroup : Exists_conj_pGroupStatement
  prop131 : Prop131Statement
  prop132 : Prop132Statement
  lemma133 : Lemma133Statement
  lemma135_i : Lemma135_iStatement
  lemma135_ii : Lemma135_iiStatement
  lemma136 : Lemma136Statement
  prop134_of_cex : Prop134_of_cexStatement
  lemma137_i : Lemma137_iStatement
  lemma137_ii_iii : Lemma137_ii_iiiStatement
  lemma137_iv_v : Lemma137_iv_vStatement
  lemma138 : Lemma138Statement
  prop139 : Prop139Statement
  lemma1311 : Lemma1311Statement
  lemma1312 : Lemma1312Statement
  lemma1313 : Lemma1313Statement
  lemma1314 : Lemma1314Statement
  lemma1315 : Lemma1315Statement
  lemma1316 : Lemma1316Statement
  prop1310_a5 : Prop1310_a5Statement
  prop1310 : Prop1310Statement
  final_of_prop1310 : Final_of_prop1310Statement

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
