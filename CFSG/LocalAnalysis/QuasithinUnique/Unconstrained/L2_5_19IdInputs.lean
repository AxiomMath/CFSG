module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

section Vocabulary

variable {G : Type} [Group G]

@[expose] def oddLayer (H : Subgroup G) : Subgroup G :=
  ((CFSG.layer (↥H ⧸ CFSG.oddCore ↥H)).comap (QuotientGroup.mk' (CFSG.oddCore ↥H))).map H.subtype

@[expose] def oddTwoCore (L : Subgroup G) : Subgroup ↥L :=
  (CFSG.pCore 2 (↥L ⧸ CFSG.oddCore ↥L)).comap (QuotientGroup.mk' (CFSG.oddCore ↥L))

instance (L : Subgroup G) : (oddTwoCore L).Normal := by
  unfold oddTwoCore
  infer_instance

@[expose] def OddTwoIso (J L : Subgroup G) : Prop :=
  Nonempty ((↥J ⧸ oddTwoCore J) ≃* (↥L ⧸ oddTwoCore L))

@[expose] def IsTwoComponentIn (L X : Subgroup G) : Prop :=
  L ∈ cComp X ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.oddCore ↥L)

@[expose] def Is121List (X : Type) [Group X] : Prop :=
  IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ 2 ∣ Nat.card X ∧
    ((∃ n : ℕ, 2 ≤ n ∧ StatedClassicalModel X .PSL 2 2 n) ∨
      (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ SuzukiModel X 2 n) ∨
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ StatedClassicalModel X .PSL 2 p 1) ∨
      Nonempty (X ≃* NativeSporadic.Carrier .J1))

end Vocabulary

@[expose] def LemmaI32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), CFSG.SectionRank.IsKGroupCat ↥H →
    ∀ t ∈ H, t ≠ 1 → t ^ 2 = 1 →
    ∀ L : Subgroup G, IsTwoComponentIn L (H ⊓ Subgroup.centralizer ({t} : Set G)) →
      ((IsTwoComponentIn (⨆ g ∈ oddLayer H, CFSG.conjugate L g) H ∧
          t ∈ Subgroup.normalizer ((⨆ g ∈ oddLayer H, CFSG.conjugate L g : Subgroup G) : Set G)) ∨
        ∃ J : Subgroup G, IsTwoComponentIn J H ∧ J ≠ CFSG.conjugate J t ∧
          (⨆ g ∈ oddLayer H, CFSG.conjugate L g) = J ⊔ CFSG.conjugate J t ∧ OddTwoIso J L)

@[expose] def Prop121Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    QTKECore G → ∀ H : Subgroup G, pCoreOf 2 H ≠ ⊥ → ∀ L ∈ cComp H,
      H ≤ Subgroup.normalizer (L : Set G) ∨
        (Nat.card {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate L h} = 2 ∧
          Is121List (↥L ⧸ CFSG.pCore 2 ↥L))

@[expose] def Prop121Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    QTKECore G → ∀ H : Subgroup G, pCoreOf 2 H ≠ ⊥ → ∀ L ∈ cComp H,
      pCoreOf 2 L ≤ Subgroup.centralizer (L : Set G) →
      (∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 2 E ∧ Nat.card E = 4) →
        CFSG.IsQuasisimple ↥L

section Patterns

variable {G : Type} [Group G]

@[expose] def IsA6 (K : Subgroup G) : Prop := Nonempty (↥K ≃* alternatingGroup (Fin 6))

@[expose] def IsL32 (K : Subgroup G) : Prop := StatedClassicalModel ↥K .PSL 3 2 1

@[expose] def IsL2pBig (K : Subgroup G) : Prop :=
  ∃ p : ℕ, IsFermatOrMersenne p ∧ 7 < p ∧ StatedClassicalModel ↥K .PSL 2 p 1

@[expose] def IsKType (K : Subgroup G) : Prop := IsL2pBig K ∨ IsL32 K ∨ IsA6 K

@[expose] def PatA (X K : Subgroup G) (t : G) : Prop :=
  IsL32 K ∧ StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∧ InducesOuter t X

@[expose] def PatB (X K : Subgroup G) (t : G) : Prop :=
  IsL32 K ∧ Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .J2) ∧ InducesOuter t X

@[expose] def PatSp4 (X K : Subgroup G) : Prop :=
  IsA6 K ∧ StatedClassicalModel ↥X .PSp 2 2 2

@[expose] def PatL5 (X K : Subgroup G) : Prop :=
  IsA6 K ∧ StatedClassicalModel ↥X .PSL 5 2 1

@[expose] def PatHS (X K : Subgroup G) (t : G) : Prop :=
  IsA6 K ∧ Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .HS) ∧
    Ch1.InducesInner t X

@[expose] def PatA8 (X K : Subgroup G) (t : G) : Prop :=
  IsA6 K ∧ ∃ (φ : ↥X ≃* alternatingGroup (Fin 8)) (a b : Fin 8), a ≠ b ∧
    InducesAut t X φ (MulAut.conjNormal (Equiv.swap a b))

@[expose] def IsCaseGroup (X : Subgroup G) : Prop :=
  StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
    Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .J2) ∨
    Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .HS) ∨
    Nonempty (↥X ≃* alternatingGroup (Fin 8)) ∨ StatedClassicalModel ↥X .PSL 5 2 1 ∨
    StatedClassicalModel ↥X .PSp 2 2 2 ∨ Nonempty (↥X ≃* alternatingGroup (Fin 6))

end Patterns

@[expose] def TabCover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G), CFSG.IsQuasisimple ↥X →
    (∃ z : G, Lemma115Cases X z) → IsL2pType ↥K →
      Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* ↥K) → Nonempty (↥X ≃* ↥K)

structure TabThreeRank : Prop where
  list : ∀ (X : Type) [Group X], Is121List X → ∀ A : Subgroup X, IsElemAbelian 3 A → Nat.card A ≤ 3
  nine : ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G), CFSG.IsQuasisimple ↥X →
    IsPGroup 2 (Subgroup.center ↥X) → IsCaseGroup X →
      ∃ A : Subgroup G, A ≤ X ∧ IsElemAbelian 3 A ∧ Nat.card A = 9

@[expose] def TabIdent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    (∃ z : G, Lemma115Cases X z) → t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 →
    ⁅X, Subgroup.zpowers t⁆ = X →
    IsComponentIn K (X ⊓ Subgroup.centralizer ({t} : Set G)) → IsKType K →
      IsPGroup 2 (Subgroup.center ↥X) ∧
        K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
          (X ⊓ Subgroup.centralizer ({t} : Set G)) ∧
        ¬ IsL2pBig K ∧ (IsL32 K → PatA X K t ∨ PatB X K t) ∧
        (IsA6 K → PatSp4 X K ∨ PatL5 X K ∨ PatHS X K t ∨ PatA8 X K t)

@[expose] def TabAutCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    (PatA X K t ∨ PatB X K t ∨ PatSp4 X K ∨ PatL5 X K ∨ PatA8 X K t) →
    ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (X : Set G) → Y ≤ Subgroup.centralizer (K : Set G) →
      (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2

@[expose] def TabAutCentHS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) → PatHS X K t →
    ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (X : Set G) → Y ≤ Subgroup.centralizer (K : Set G) →
      t ∈ Y →
      (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 4 ∧
      ((Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y = 4 →
        (∀ y ∈ Y, y * y ∈ Subgroup.centralizer (X : Set G)) ∧
        (∃ Y₁ : Subgroup G, Y ⊓ Subgroup.centralizer (X : Set G) ≤ Y₁ ∧ Y₁ ≤ Y ∧
          Y₁.relIndex Y = 2 ∧ t ∉ Y₁) ∧
        ∀ Y₁ : Subgroup G, Y ⊓ Subgroup.centralizer (X : Set G) ≤ Y₁ → Y₁ ≤ Y →
          Y₁.relIndex Y = 2 → t ∉ Y₁ →
          ∃ A : Subgroup G, A = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
              (X ⊓ Subgroup.centralizer (Y₁ : Set G)) ∧
            CFSG.IsQuasisimple ↥A ∧ K < A)

structure TabNonEmbed : Prop where
  no_pair : ∀ (G : Type) [Group G] [Finite G] (X A B : Subgroup G), CFSG.IsQuasisimple ↥X →
    IsPGroup 2 (Subgroup.center ↥X) →
    (StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
      Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .J2)) →
    A ≤ X → B ≤ X → ⁅A, B⁆ = ⊥ → A ⊓ B = ⊥ → IsL2pType ↥A → IsL2pType ↥B → False
  no_comp : ∀ (G : Type) [Group G] [Finite G] (X Y : Subgroup G) (i : G), CFSG.IsQuasisimple ↥X →
    IsPGroup 2 (Subgroup.center ↥X) →
    (StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
      Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .J2)) →
    i ∈ Subgroup.normalizer (X : Set G) → i * i = 1 → ⁅X, Subgroup.zpowers i⁆ = X →
    IsComponentIn Y (X ⊓ Subgroup.centralizer ({i} : Set G)) →
      ¬ (StatedClassicalModel (↥Y ⧸ Subgroup.center ↥Y) .PSL 3 2 2 ∨
        Nonempty ((↥Y ⧸ Subgroup.center ↥Y) ≃* NativeSporadic.Carrier .J2))

structure Inputs2519 : Prop where
  i32 : LemmaI32
  p121_3 : Prop121Three
  p121_5 : Prop121Five
  list115 : Lemma115_3_List
  cover : TabCover
  ident : TabIdent
  autCent : TabAutCent
  autCentHS : TabAutCentHS
  threeRank : TabThreeRank
  nonEmbed : TabNonEmbed

end CFSG.QuasithinUnique.Id2519
