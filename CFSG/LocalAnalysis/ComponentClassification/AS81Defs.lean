module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Vocabulary

variable {G : Type} [Group G]

@[expose] def centerIn (H : Subgroup G) : Subgroup G := H ⊓ centralizer (H : Set G)

@[expose] def pointsIn (R E : Subgroup G) : Set (Subgroup G) :=
  {Q | Q ≤ E ∧ ∃ x : G, Q = rightConjugate R x}

@[expose] def oddNStar [Finite G] (E : Subgroup G) : Set (Subgroup G) :=
  {X | Maximal (fun Y : Subgroup G => Odd (Nat.card Y) ∧ E ≤ normalizer (Y : Set G)) X}

end Vocabulary

abbrev TypeL34 (Q : Type) [Group Q] : Prop :=
  Assembly.LowTwoRank.StatedClassicalModel Q .PSL 3 2 2

abbrev TypeG24 (Q : Type) [Group Q] : Prop :=
  ChevalleyExceptionalModel Q .G2 2 2

structure Base (G : Type) [Group G] [Finite G] (A : Subgroup G) : Prop where
  hyp : RankTwoHypNF G A
  oddCore : standardComponentOddCore G = ⊥
  hypII : AS76b.HypII A
  type : TypeL34 (rankTwoQuot A) ∨ TypeG24 (rankTwoQuot A)

theorem Base.hyp31 {G : Type} [Group G] [Finite G] {A : Subgroup G} (h : Base G A) :
    AS76b.Hyp31 A :=
  ⟨h.hyp.standard, h.hypII, h.oddCore, by have := h.hyp.rank; omega, h.hyp.not_normal⟩

structure BaseK (G : Type) [Group G] [Finite G] (A : Subgroup G) : Prop where
  hyp : RankTwoHyp G A
  oddCore : standardComponentOddCore G = ⊥
  hypII : AS76b.HypII A
  type : TypeL34 (rankTwoQuot A) ∨ TypeG24 (rankTwoQuot A)

theorem BaseK.hyp31 {G : Type} [Group G] [Finite G] {A : Subgroup G} (h : BaseK G A) :
    AS76b.Hyp31 A :=
  ⟨h.hyp.standard, h.hypII, h.oddCore, by have := h.hyp.rank; omega, h.hyp.not_normal⟩

theorem BaseK.toBase {G : Type} [Group G] [Finite G] {A : Subgroup G} (h : BaseK G A) :
    Base G A :=
  ⟨h.hyp.toNF, h.oddCore, h.hypII, h.type⟩

structure Frame (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G)
    (E F : Subgroup G) : Prop where
  base : Base G A
  le : A₁ ≤ A
  quasisimple : Open.IsQuasisimple A₁
  typeA₁ : TypeL34 (↥A₁ ⧸ center ↥A₁)
  sylowR : IsSylowOf 2 R (centralizer (A : Set G))
  elemR : IsElemAbelian 2 R
  cardR : Nat.card R = 4
  not_mem : g ∉ normalizer (A : Set G)
  comm : rightConjugate R g ≤ centralizer (R : Set G)
  conj_le : rightConjugate R g ≤ A₁ ⊔ R
  E_le : E ≤ A₁ ⊔ R
  F_le : F ≤ A₁ ⊔ R
  R_le_E : R ≤ E
  R_le_F : R ≤ F
  elemE : IsElemAbelian 2 E
  elemF : IsElemAbelian 2 F
  cardE : Nat.card E = 64
  cardF : Nat.card F = 64
  ne : E ≠ F
  inf_eq : E ⊓ F = R ⊔ rightConjugate R g
  inf_eq_center : E ⊓ F = centerIn (E ⊔ F)
  sylow : IsSylowOf 2 (E ⊔ F) (A₁ ⊔ R)

@[expose] def L34HypII : Prop :=
  ∀ (A : Type) [Group A] [Finite A], commutator A = ⊤ → TypeL34 (A ⧸ center A) → AS76b.HypII A

@[expose] def Step11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Base G A →
    ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
      IsElemAbelian 2 R ∧
        (∃ g : G, g ∉ normalizer (A : Set G) ∧ rightConjugate R g ≤ centralizer (R : Set G)) ∧
        ∀ g : G, g ∉ normalizer (A : Set G) → rightConjugate R g ≤ centralizer (R : Set G) →
          rightConjugate R g ≤ A ⊔ R

@[expose] def Step14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Base G A → TypeL34 (rankTwoQuot A) →
    ∀ R : Subgroup G, IsSylowOf 2 R (centralizer (A : Set G)) →
      ∃ (g : G) (E F : Subgroup G), Frame G A A R g E F

@[expose] def Step15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G),
    Frame G A A₁ R g E F → Odd (Nat.card (center A₁)) →
      (∀ e ∈ E, e ∉ A₁ → ∃ Q ∈ pointsIn R E, e ∈ Q) ∧
      (∀ Q₁ ∈ pointsIn R E, ∀ Q₂ ∈ pointsIn R E, Q₁ ≠ Q₂ → Q₁ ⊓ Q₂ = ⊥) ∧
      Nat.card (pointsIn R E) = 16 ∧
      ∃ P₀ P : Subgroup G, P₀ ≤ normalizer (E : Set G) ∧
        normalizer (E : Set G) ≤ normalizer (P₀ : Set G) ∧
        normalizer (E : Set G) = P₀ ⊔ (normalizer (E : Set G) ⊓ normalizer (R : Set G)) ∧
        (∀ p ∈ P₀, ∀ q ∈ P₀, p * p ∈ centralizer (E : Set G) ∧
          p * q * p⁻¹ * q⁻¹ ∈ centralizer (E : Set G)) ∧
        (P₀ ⊓ centralizer (E : Set G)).relIndex P₀ = 16 ∧
        (∀ Q ∈ pointsIn R E, ∃ p ∈ P₀, rightConjugate R p = Q) ∧
        IsPGroup 2 P ∧ P ≤ P₀ ∧ P₀ = AS76b.oddCoreIn (centralizer (E : Set G)) ⊔ P ∧
        AS76b.oddCoreIn (centralizer (E : Set G)) ≤ centralizer (P : Set G)

@[expose] def Step16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Frame G A A R g E F → Even (Nat.card (center A)) →
      R ≤ A ∧ Nat.card (pointsIn R E) = 6 ∧
      (∃ L : Subgroup G, centralizer (E : Set G) ≤ L ∧ L ≤ normalizer (E : Set G) ∧
        normalizer (E : Set G) ≤ normalizer (L : Set G) ∧
        ⁅L, L⁆ ⊔ centralizer (E : Set G) = L ∧ (centralizer (E : Set G)).relIndex L = 1080) ∧
      ∃ y : G, y ∈ normalizer (A : Set G) ∧ (∃ k : ℕ, orderOf y = 3 ^ k) ∧
        (∀ a ∈ A, ¬ ∀ x ∈ A, y⁻¹ * x * y = a⁻¹ * x * a) ∧
        ∀ r ∈ R, r ≠ 1 → y * r ≠ r * y

@[expose] def Step17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Frame G A A R g E F → TypeL34 (rankTwoQuot A) → L34GeneralBelow (Nat.card G) →
    ∀ X ∈ oddNStar E, X ≠ ⊥ →
      (∀ h ∈ normalizer (E : Set G),
        X = AS76b.oddCoreIn (centralizer (rightConjugate A h : Set G))) ∧
      A ≤ normalizer (X : Set G) ∧
      L34Conclusion (A.subgroupOf (normalizer (X : Set G)))

@[expose] def Step18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Frame G A A R g E F → TypeL34 (rankTwoQuot A) → L34GeneralBelow (Nat.card G) →
    ∀ z ∈ E, orderOf z = 2 →
      (∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ centralizer ({z} : Set G)) →
      (∀ x : G, z ∉ rightConjugate R x) →
        AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥

structure Hyp19 (G : Type) [Group G] [Finite G] (z : G) (X T : Subgroup G) : Prop where
  order : orderOf z = 2
  twoCentral : ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧
    (S : Subgroup G) ≤ centralizer ({z} : Set G)
  le : X ≤ centralizer ({z} : Set G)
  extraspecial : CFSG.IsExtraspecialPGroup 2 X
  card : Nat.card X = 2 ^ 7 ∨ Nat.card X = 2 ^ 9
  sylow : IsSylowOf 2 (zpowers z) (centralizer (X : Set G))
  sylowT : IsSylowOf 2 T (centralizer ({z} : Set G))
  le_T : X ≤ T
  weak : ∀ h ∈ centralizer ({z} : Set G), rightConjugate X h ≤ T → rightConjugate X h = X
  rank : ∀ h ∈ centralizer ({z} : Set G), 1 < Open.pRank 2 (X ⊓ rightConjugate X h) →
    rightConjugate X h = X

@[expose] def Step110 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (X T : Subgroup G), Hyp19 G z X T →
    ∀ x ∈ X, ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * x * h ∈ T → h⁻¹ * x * h ∈ X

@[expose] def Sec2Suz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Frame G A A R g E F → TypeL34 (rankTwoQuot A) → Odd (Nat.card (center A)) →
    L34GeneralBelow (Nat.card G) → IsSporadic (rankTwoX A) .Suz

@[expose] def Sec4He : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Frame G A A R g E F → TypeL34 (rankTwoQuot A) → Even (Nat.card (center A)) →
    L34GeneralBelow (Nat.card G) →
      Nonempty (center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
        IsSporadic (rankTwoX A) .He

@[expose] def Sec2SuzXR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Frame G A A R g E F → TypeL34 (rankTwoQuot A) → Odd (Nat.card (center A)) →
    L34GeneralBelow (Nat.card G) → rankTwoX A ⊔ R = ⊤ → IsSporadic (rankTwoX A) .Suz

@[expose] def Sec4HeXR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Frame G A A R g E F → TypeL34 (rankTwoQuot A) → Even (Nat.card (center A)) →
    L34GeneralBelow (Nat.card G) → rankTwoX A ⊔ R = ⊤ →
      Nonempty (center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
        IsSporadic (rankTwoX A) .He

theorem sec2SuzXR_of (h : Sec2Suz) : Sec2SuzXR :=
  fun G _ _ A R g E F hF hL ho hb _ => h G A R g E F hF hL ho hb

theorem sec4HeXR_of (h : Sec4He) : Sec4HeXR :=
  fun G _ _ A R g E F hF hL he hb _ => h G A R g E F hF hL he hb

end CFSG.ComponentClassification.AS81
