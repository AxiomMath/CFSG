module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakMaximalDef
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

section Vocabulary

variable {G : Type*} [Group G]

@[expose] def wGroup (A : Subgroup G) : Subgroup G :=
  ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : 4 ≤ Nat.card B) (_ : ∀ b ∈ B, b * b = 1),
    ⨅ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
      (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype

@[expose] def IsUnbalancingComponent (J : Subgroup G) : Prop :=
  ∃ a x : G, GSUnbalancingTriple a x J

@[expose] def LocallyTwoBalanced (G : Type*) [Group G] : Prop :=
  ∀ J : Subgroup G, IsUnbalancingComponent J → ∀ a : G, orderOf a = 2 →
    J ≤ centralizer ({a} : Set G) →
    ∀ E : Subgroup G, E ≤ normalizer (J : Set G) ⊓ centralizer ({a} : Set G) →
      Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      ⁅J, wGroup E ⊓ centralizer ({a} : Set G)⁆ ≤
        (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype

@[expose] def IsExtremalIn (S : Subgroup G) (b : G) : Prop :=
  b ∈ S ∧ ∃ P : Sylow 2 ↥(centralizer ({b} : Set G)),
    (P : Subgroup _) = (S ⊓ centralizer ({b} : Set G)).subgroupOf (centralizer ({b} : Set G))

@[expose] def IsAbelianTwoOfRank [Finite G] (k : ℕ) (A : Subgroup G) : Prop :=
  IsPGroup 2 A ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ k ≤ pRank 2 ↥A

@[expose] def AbelianConnected [Finite G] (k : ℕ) (A B : Subgroup G) : Prop :=
  IsAbelianTwoOfRank k A ∧
    Relation.ReflTransGen (fun A' B' : Subgroup G => IsAbelianTwoOfRank k B' ∧
      ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) A B

@[expose] def AbelianConnectedIn [Finite G] (S : Subgroup G) (k : ℕ) (A B : Subgroup G) : Prop :=
  A ≤ S ∧ IsAbelianTwoOfRank k A ∧
    Relation.ReflTransGen (fun A' B' : Subgroup G => B' ≤ S ∧ IsAbelianTwoOfRank k B' ∧
      ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) A B

@[expose] def GWTwoBalanced (G : Type*) [Group G] : Prop :=
  ∀ E : Subgroup G, Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
    ∀ x : G, orderOf x = 2 → (∀ e ∈ E, e * x = x * e) →
      (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
          (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype) ⊓
          centralizer ({x} : Set G) ≤
        (pPrimeCore 2 (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype

end Vocabulary

@[expose] def L34BaseSetting (G : Type) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G ∧ (∃ g h : G, g * h ≠ h * g) ∧ Assembly.KProper Blueprint.Catalog G ∧
    (∃ z : G, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set G)) ≠ ⊥) ∧
    ¬ OutcomeLocal.UOutcome G ∧ LocallyTwoBalanced G ∧
    (¬ ∃ (t : G) (L : Subgroup G), orderOf t = 2 ∧ L ≤ centralizer ({t} : Set G) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He)) ∧
    ∀ (c v : G) (K : Subgroup G), GSUnbalancingTriple c v K →
      IsL2Type 5 (K ⧸ pPrimeCore 2 K) ∨ IsL2Type 7 (K ⧸ pPrimeCore 2 K) ∨
        IsL34Type (K ⧸ Open.fusionZStar K)

@[expose] def MaximalTwoComponentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) →
    Assembly.KProper Blueprint.Catalog G →
    ∀ J : Subgroup G, GSWeakMaximalComponent J → 2 ≤ pRank 2 ↥J →
    (¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
        Nonempty (J ⧸ Open.fusionZStar J ≃*
          Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K))) →
    ((IsL34Type (J ⧸ Open.fusionZStar J) ∧ L34BaseSetting G) ∨
      IsHeldType (J ⧸ Open.fusionZStar J)) →
    ∀ t : G, orderOf t = 2 → J ≤ centralizer ({t} : Set G) →
      (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
          (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ⊔
            J ∧
      (3 ≤ pRank 2 ↥J → ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤
        (pPrimeCore 2 J).map J.subtype ⊓
          (pPrimeCore 2 (conjugate J g)).map (conjugate J g).subtype)

@[expose] def MaximalTwoComponentInputTyped : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) →
    Assembly.KProper Blueprint.Catalog G →
    ∀ J : Subgroup G, GSWeakMaximalComponent J → 2 ≤ pRank 2 ↥J →
    (¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
        Nonempty (J ⧸ Open.fusionZStar J ≃*
          Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K))) →
    (IsL34Type (J ⧸ Open.fusionZStar J) ∨ IsHeldType (J ⧸ Open.fusionZStar J)) →
    ∀ t : G, orderOf t = 2 → J ≤ centralizer ({t} : Set G) →
      (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
          (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ⊔
            J ∧
      (3 ≤ pRank 2 ↥J → ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤
        (pPrimeCore 2 J).map J.subtype ⊓
          (pPrimeCore 2 (conjugate J g)).map (conjugate J g).subtype)

theorem MaximalTwoComponentInputTyped.base (h : MaximalTwoComponentInputTyped) :
    MaximalTwoComponentInput :=
  fun G _ _ _ hsF hnF hoF hK J hJ h2 hSp htype =>
    h G hsF hnF hoF hK J hJ h2 hSp (htype.imp_left And.left)

@[expose] def MaximalTwoComponentInputAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) →
    Assembly.KProper Blueprint.Catalog G →
    ∀ J : Subgroup G, GSWeakMaximalComponent J → 2 ≤ pRank 2 ↥J →
    (¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
        Nonempty (J ⧸ Open.fusionZStar J ≃*
          Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K))) →
    ∀ t : G, orderOf t = 2 → J ≤ centralizer ({t} : Set G) →
      (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
          (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ⊔
            J ∧
      (3 ≤ pRank 2 ↥J → ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤
        (pPrimeCore 2 J).map J.subtype ⊓
          (pPrimeCore 2 (conjugate J g)).map (conjugate J g).subtype)

theorem MaximalTwoComponentInputAll.typed (h : MaximalTwoComponentInputAll) :
    MaximalTwoComponentInput :=
  fun G _ _ _ hsF hnF hoF hK J hJ h2 hSp _ => h G hsF hnF hoF hK J hJ h2 hSp

@[expose] def SolomonCommutingCoreInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S T : Subgroup G), S ≠ ⊥ → T ≠ ⊥ →
    (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) → (∀ x ∈ S, x * x = 1) →
    (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) → (∀ x ∈ T, x * x = 1) →
    (∀ x ∈ S, ∀ y ∈ T, x * y = y * x) →
    let C := centralizer (T : Set G)
    let D := (pPrimeCore 2 (centralizer (S : Set G))).map (centralizer (S : Set G)).subtype ⊓ C
    let OC := (pPrimeCore 2 C).map C.subtype
    (⁅((pCore 2 (C ⧸ pPrimeCore 2 C)).comap (QuotientGroup.mk' (pPrimeCore 2 C))).map
        C.subtype, D⁆ ≤ OC ∧ ⁅(pCore 2 C).map C.subtype, D⁆ = ⊥) ∧
    (∀ L : Subgroup G, L ≤ C → IsPComponent 2 (L.subgroupOf C) →
      D ≤ normalizer (L : Set G) ∧
      (¬ ⁅L, D⁆ ≤ (pPrimeCore 2 L).map L.subtype →
        S ⊓ normalizer (L : Set G) ≠ ⊥ ∧ (pPrimeCore 2 L).map L.subtype ⊔ ⁅L, D⁆ = L ∧
          (pPrimeCore 2 L).map L.subtype ⊔ ⁅L, S ⊓ normalizer (L : Set G)⁆ = L)) ∧
    (¬ D ≤ OC → ∃ M : Subgroup G, M ≤ C ∧ IsPComponent 2 (M.subgroupOf C) ∧
      ¬ ⁅M, D⁆ ≤ (pPrimeCore 2 M).map M.subtype)

@[expose] def AschbacherSeitzHeldInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Assembly.KProper Blueprint.Catalog G →
    IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ∀ L : Subgroup G, IsStandardSubgroup L → Nonempty (L ≃* Blueprint.NativeSporadic.He) →
      pRank 2 ↥(centralizer (L : Set G)) = 1

@[expose] def GorensteinWalterConnectedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GWTwoBalanced G →
    ∀ A : Subgroup G, (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) →
      16 ≤ Nat.card A →
      (∀ E E₁ : Subgroup G, AbelianConnected 3 E A → AbelianConnected 3 E₁ A →
        wGroup E = wGroup A ∧ wGroup E₁ = wGroup A ∧
          ∀ g : G, E₁ = conjugate E g → g ∈ normalizer (wGroup A : Set G)) ∧
      ∀ S : Subgroup G, S ≤ normalizer (wGroup A : Set G) →
        (∃ P : Sylow 2 ↥(normalizer (wGroup A : Set G)),
          (P : Subgroup _) = S.subgroupOf (normalizer (wGroup A : Set G))) →
        (∀ E F : Subgroup G, E ≤ S → F ≤ S → IsAbelianTwoOfRank 3 E → IsAbelianTwoOfRank 3 F →
          AbelianConnectedIn S 3 E F) →
        (∃ P : Sylow 2 G, (P : Subgroup G) = S) ∧
          ∀ a b : G, b ∈ S → IsExtremalIn S a → (∃ g : G, a = g⁻¹ * b * g) →
            3 ≤ pRank 2 ↥(S ⊓ centralizer ({b} : Set G)) →
            ∃ m ∈ normalizer (wGroup A : Set G), b = m⁻¹ * a * m

@[expose] def GorensteinHarrisInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G →
    ∀ (S : Sylow 2 G) (T : Sylow 2 Blueprint.NativeSporadic.HS),
      Nonempty ((S : Subgroup G) ≃* (T : Subgroup Blueprint.NativeSporadic.HS)) →
      Nonempty (G ≃* Blueprint.NativeSporadic.HS)

@[expose] def HoltTransitiveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ∀ (Ω : Type) [MulAction G Ω] [Finite Ω], MulAction.IsPretransitive G Ω → 2 ≤ Nat.card Ω →
      ∀ t : G, orderOf t = 2 → Odd (centralizer ({t} : Set G)).index →
        (∃ ω : Ω, ∀ ω' : Ω, t • ω' = ω' ↔ ω' = ω) →
        ∀ L : Subgroup G, L ≤ centralizer ({t} : Set G) →
          ¬ IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G)))

@[expose] def GoldschmidtStronglyClosedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ∀ (S : Sylow 2 G) (A : Subgroup G), A ≤ S → A ≠ ⊥ →
      (∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A) →
      Group.IsSolvable ↥(centralizer (A : Set G))

end CFSG.ComponentClassification.GrSLit
