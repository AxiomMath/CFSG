module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

@[expose] def KFactM11TwoSignalizer : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group) →
    ∀ (Q : Sylow 3 K), IsElemAbelian 3 (Q : Subgroup K) ∧
      ∀ u ∈ (Q : Subgroup K), orderOf u = 3 →
        ⊤ ≤ rankThreeGamma 1 3 (Q : Subgroup K) ⊔
          sSup {T : Subgroup K | IsPGroup 2 T ∧ u ∈ normalizer (T : Set K)}

@[expose] def reducedCentralizerOfJ {G : Type} [Group G] [Finite G] (x : G) (J : Subgroup G) :
    Subgroup (GenericReduced 3 x) :=
  Subgroup.centralizer ((((J.subgroupOf (centralizer ({x} : Set G))).map
    (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)) :
      Subgroup (GenericReduced 3 x))) : Set (GenericReduced 3 x))

structure IsM11Normal {G : Type} [Group G] [Finite G] (M : Subgroup G) (x : G)
    (J : Subgroup G) : Prop where
  le_centralizer : J ≤ centralizer ({x} : Set G)
  centralizer_le : centralizer ({x} : Set G) ≤ normalizer (J : Set G)
  perfect : Group.IsPerfect J
  not_le : ¬ J ≤ M
  lt_core : rankThreePrimeCore 3 J < J
  minimal : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore 3 J ≤ N →
    N = rankThreePrimeCore 3 J ∨ N = J
  iso : ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
    ψ.ker = (rankThreePrimeCore 3 J).subgroupOf J ∧
    Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group)

@[expose] def M11Prop34 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (x : G) : Prop :=
  IsMulCommutative (P : Subgroup G) ∧
  ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x

@[expose] def M11Lemma42 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (M : Subgroup G)
    (x : G) : Prop :=
  ∀ U : Subgroup G, U ≤ (P : Subgroup G) → IsElemAbelian p U → Nat.card U = p ^ 2 → x ∈ U →
    ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M

@[expose] def M11Lemma43 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (M : Subgroup G)
    (x : G) : Prop :=
  ∃ U : Subgroup G, U ≤ (P : Subgroup G) ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧ x ∈ U ∧
    (∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      CFSG.ABGLocalTools.IsSylowOf 2 (Y ⊓ GLBPrimeCore p M) (GLBPrimeCore p M) →
      normalizer (Y : Set G) ≤ M)

@[expose] def M11PlaneData (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (M : Subgroup G) (x : G) : Prop :=
  M11Prop34 p P x ∧ M11Lemma42 p P M x ∧ M11Lemma43 p P M x

@[expose] def GenericM11At (G : Type) [Group G] [Finite G]
    (Φ : ∀ p : ℕ, Sylow p G → Subgroup G → G → Prop) : Prop :=
  GenericAt G fun p P M x => p = 3 → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J →
      Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group) →
      Φ p P M x

@[expose] def GL83GenericPrimeThreeM11Prop34 (G : Type) [Group G] [Finite G] : Prop :=
  GenericM11At G fun p P _ x => M11Prop34 p P x

@[expose] def GL83GenericPrimeThreeM11Lemma42 (G : Type) [Group G] [Finite G] : Prop :=
  GenericM11At G fun p P M x => M11Prop34 p P x → M11Lemma42 p P M x

@[expose] def GL83GenericPrimeThreeM11Lemma43 (G : Type) [Group G] [Finite G] : Prop :=
  GenericM11At G fun p P M x => M11Prop34 p P x → M11Lemma43 p P M x

@[expose] def GL83GenericPrimeThreeTypes4 (G : Type) [Group G] [Finite G] : Prop :=
  GenericRedThreeAt G fun Q _ =>
    Nonempty (Q ≃* PSL(2, GaloisField 3 2)) ∨
    (∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ IsoLie Q (.twistedA 2 q)) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ IsoLie Q (.A 2 q)) ∨
    IsoLie Q (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
