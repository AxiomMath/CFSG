module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S10

@[expose] def isYs09Type (i : TauCeti.CFSGIndex) : Prop :=
  S9.isU5two i ∨ S9.isU6two i ∨ S9.isSp8two i ∨ S9.isD4two i

@[expose] def isL2eight : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A 1 q => q.card = 8 | _ => False

@[expose] def isA6 : TauCeti.CFSGIndex → Prop
  | .alternating n _ => n = 6
  | _ => False

@[expose] def isStdSubList (i : TauCeti.CFSGIndex) : Prop :=
  S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i ∨ isA6 i ∨ isL2eight i

end S10

@[expose] def LabelDictAt : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
    catalogIs (X ⧸ Subgroup.center X) S10.isYs09Type →
    ∀ P : GLAMarkProp X, GLAMarking X P →
      GLAMarking X (fun lab R inst I F θ => Ys09Label lab ∧ @P lab R inst I F θ)

@[expose] def I1015fourAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ K : Subgroup G, CFSG.Open.IsQuasisimple ↥K → catalogIs (↥K ⧸ Subgroup.center ↥K) S10.isYs09Type →
    ∃ F T : Subgroup G, F ≤ K ∧ IsElemAbelian 3 F ∧ T ≤ K ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      F ≤ Subgroup.normalizer (T : Set G) ∧
      3 ^ 3 * Nat.card ↥(F ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card F

@[expose] def StdSubTableAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (a : G) (J D K : Subgroup G), GLASStar 3 B a J → catalogIs (PSimple 3 J) S10.isYs09Type →
    InnDiagOn 3 B J → GLAStdSubPre 3 B a J D K →
    catalogIs (↥K ⧸ Subgroup.center ↥K) S10.isStdSubList ∧
      (catalogIs (↥K ⧸ Subgroup.center ↥K) S10.isA6 → catalogIs ↥K S10.isA6) ∧
      (catalogIs (↥K ⧸ Subgroup.center ↥K) S10.isL2eight → catalogIs (PSimple 3 J) S9.isU6two)

@[expose] def I171At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), GLASStar 3 B x L → 3 ^ 4 ≤ Nat.card B →
    IsChevSimple 2 (PSimple 3 L) → CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) →
    InnerDiagMarking B L → CentModEqZpowers 3 B L x →
    (∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥) →
    (∃ D K : Subgroup G, GLAStdSubPre 3 B x L D K) →
    (∀ D K : Subgroup G, GLAStdSubPre 3 B x L D K → GLASmall K) →
    catalogIs (↥L ⧸ Subgroup.center ↥L) (fun i => S9.isU5two i ∨ S9.isU6two i ∨ S9.isD4two i) ∧
      ∀ D K : Subgroup G, GLAStdSubPre 3 B x L D K → catalogIs ↥K S9.isU4two

@[expose] def U6D0RankAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (J D₀ K : Subgroup G), (∃ X : Subgroup G, GLAPComponent 3 X J) → catalogIs (PSimple 3 J) S9.isU6two →
    D₀ ≤ Subgroup.normalizer (J : Set G) → IsElemAbelian 3 D₀ → Nat.card D₀ = 3 ^ 2 → InnDiagOn 3 D₀ J →
    K = GLALayer (J ⊓ Subgroup.centralizer (D₀ : Set G)) → catalogIs (↥K ⧸ Subgroup.center ↥K) S10.isL2eight →
    ∀ A : Subgroup G, A ≤ Subgroup.normalizer (J : Set G) → A ≤ Subgroup.centralizer (D₀ : Set G) →
      IsElemAbelian 3 A → Nat.card A ≤ 3 ^ 3 * Nat.card ↥(A ⊓ centModSubgroup 3 J)

@[expose] def I1431Chev2At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (b' a : G) (Kstar K : Subgroup G), CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({b'} : Set G)) →
    a ∈ Subgroup.centralizer ({b'} : Set G) → a ^ 3 = 1 → GLAPComponent 3 (Subgroup.centralizer ({b'} : Set G)) Kstar →
    a ∈ Subgroup.normalizer (Kstar : Set G) → GLAPComponent 3 (Kstar ⊓ Subgroup.centralizer ({a} : Set G)) K →
    catalogIs (PSimple 3 K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) →
    ¬ Kstar ≤ K ⊔ GLAPPrimeCoreOf 3 Kstar → GLATwoLocalRank 3 G ≤ 4 →
    ¬ catalogIs (PSimple 3 Kstar) (fun i => i = .sporadic .Co2) → IsChevSimple 2 (PSimple 3 Kstar)

@[expose] def I144oneAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (b' a : G) (Kstar K : Subgroup G), a ∈ Subgroup.centralizer ({b'} : Set G) → a ^ 3 = 1 →
    GLAPComponent 3 (Subgroup.centralizer ({b'} : Set G)) Kstar → CFSG.Open.IsQuasisimple ↥Kstar →
    IsChevSimple 2 (PSimple 3 Kstar) →
    a ∈ Subgroup.normalizer (Kstar : Set G) → GLAPComponent 3 (Kstar ⊓ Subgroup.centralizer ({a} : Set G)) K →
    catalogIs (PSimple 3 K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) →
    ¬ Kstar ≤ K ⊔ GLAPPrimeCoreOf 3 Kstar →
    GLAMarking ↥Kstar (fun lab _ _ _ _ _ => lab.n = 1) ∨
      GLAMarking ↥Kstar (fun lab _ _ I F θ =>
        GLAPrimeField 3 lab I F (GLAInduces θ fun j j' => (j' : G) = a⁻¹ * j * a))

@[expose] def I112SingleStdAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X : Subgroup G) (z : G) (E J : Subgroup G), CFSG.Open.IsKGroup ↥X → z ∈ E → E ≤ X → IsElemAbelian 3 E →
    3 ^ GLATwoLocalRank 3 ↥X ≤ Nat.card E →
    GLAPComponent 3 (X ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)) J →
    E ≤ Subgroup.normalizer (J : Set G) →
    catalogIs (PSimple 3 J) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) →
    ∃ K : Subgroup G, GLAPComponent 3 X K ∧ J ≤ K ∧ E ≤ Subgroup.normalizer (K : Set G)

@[expose] def StdSubFAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ K : Subgroup G, CFSG.Open.IsQuasisimple ↥K →
    catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) →
    ∃ F T E : Subgroup G, F ≤ K ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 2 ∧ T ≤ K ∧ IsPGroup 2 T ∧
      F ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, F⁆ : Subgroup G) ≠ ⊥ ∧ IsEmpty (T ≃* QuaternionGroup 2) ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K ∧
      (∃ g ∈ K ⊓ Subgroup.centralizer (F : Set G), g ^ 3 = 1 ∧ g ∉ F) ∧
      E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
      (∀ g ∈ K ⊓ Subgroup.centralizer (K : Set G), g ^ 3 = 1 → g = 1)

@[expose] def I113NormAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X B L : Subgroup G), CFSG.Open.IsKGroup ↥X → B ≤ X → IsElemAbelian 3 B →
    3 ^ GLATwoLocalRank 3 ↥X ≤ Nat.card B →
    (∃ U : Subgroup G, U ≤ X ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G)) →
    GLAPComponent 3 X L → (∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3) →
    B ≤ Subgroup.normalizer (L : Set G)

end CFSG.LocalAnalysis.GLTheoremA
