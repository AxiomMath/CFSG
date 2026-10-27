module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

section Vocabulary

variable {G : Type*} [Group G]

@[expose] def oddIn (H : Subgroup G) : Subgroup G := (pPrimeCore 2 H).map H.subtype

@[expose] def zStarIn (H : Subgroup G) : Subgroup G := (Open.fusionZStar H).map H.subtype

@[expose] def layerIn (H : Subgroup G) : Subgroup G := (pLayer ↥H 2).map H.subtype

@[expose] def IsElemTwo (F : Subgroup G) : Prop :=
  (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ ∀ x ∈ F, x * x = 1

@[expose] def IsEightGroup (F : Subgroup G) : Prop := IsElemTwo F ∧ Nat.card F = 8

@[expose] def IsSylowTwoIn (S H : Subgroup G) : Prop :=
  S ≤ H ∧ ∃ P : Sylow 2 ↥H, (P : Subgroup ↥H) = S.subgroupOf H

@[expose] def omegaOne (H : Subgroup G) : Subgroup G := closure {h | h ∈ H ∧ h * h = 1}

@[expose] def IsThreeConnected [Finite G] (S : Subgroup G) : Prop :=
  ∀ E F : Subgroup G, E ≤ S → F ≤ S → IsAbelianTwoOfRank 3 E → IsAbelianTwoOfRank 3 F →
    AbelianConnectedIn S 3 E F

@[expose] def withKernel (J : Subgroup G) : Subgroup G := J ⊔ coreActionKernel J

@[expose] def pumpUp (J : Subgroup G) (t : G) : Subgroup G :=
  ⨆ (g : G) (_ : g ∈ layerIn (centralizer ({t} : Set G))), conjugate (gsFixedLayer J t) g

@[expose] noncomputable def twoExp [Finite G] (H : Subgroup G) : ℕ :=
  (Nat.card H).factorization 2

end Vocabulary

@[expose] def L34Sec4Setting (G : Type) [Group G] [Finite G] (a x : G) (J S : Subgroup G) :
    Prop :=
  L34BaseSetting G ∧ GSUnbalancingTriple a x J ∧ IsL34Type (J ⧸ Open.fusionZStar J) ∧
    GSWeakMaximalComponent J ∧ IsSylowTwoIn S (normalizer (J : Set G)) ∧ a ∈ S ∧ x ∈ S

@[expose] def L34Sec4Running {G : Type} [Group G] (J A : Subgroup G) : Prop :=
  A ≤ withKernel J ∧ IsEightGroup A ∧ wGroup A ≠ ⊥

@[expose] def L34Prop41 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) →
      ∀ A : Subgroup G, A ≤ withKernel J → IsEightGroup A → wGroup A = ⊥

@[expose] def L34Lemma43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    ¬ IsThreeConnected (S ⊓ withKernel J) ∧ Monoid.exponent ↥(S ⊓ zStarIn J) = 4

@[expose] def L34Lemma44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    L34Sec4Running J A → ¬ IsCyclic ↥(S ⊓ zStarIn J) →
    (IsElemTwo (S ⊓ J ⊓ centralizer ({x} : Set G) ⊔ zpowers x) ∧
        Nat.card ↥(S ⊓ J ⊓ centralizer ({x} : Set G) ⊔ zpowers x) = 16) ∧
      ∀ C : Subgroup G, C ≤ S ⊓ J → IsElemTwo C → Nat.card C = 16 →
        S ⊓ J ⊓ centralizer ({x} : Set G) ≤ C →
        (∀ y ∈ S ⊓ J, (∀ w ∈ S ⊓ J, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔
          y ∈ C ⊔ (S ⊓ zStarIn J)) →
        J = ⨆ (E : Subgroup G) (_ : E ≤ S ⊓ J ⊓ centralizer ({x} : Set G) ⊔ zpowers x ∨ E ≤ C)
          (_ : IsEightGroup E), J ⊓ normalizer (E : Set G)

@[expose] def L34Lemma45 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S : Subgroup G), L34Sec4Setting G a x J S →
    ∀ M₁ : Subgroup G, J ≤ M₁ → ((oddIn M₁ ⊔ J).subgroupOf M₁).Normal → IsSylowTwoIn S M₁ →
      (∀ s ∈ S, a * s = s * a) → normalizer ((S ⊓ J : Subgroup G) : Set G) ≤ M₁ →
      ∀ g : G, g⁻¹ * a * g ∈ M₁ →
        (∀ j ∈ oddIn M₁ ⊔ J, j⁻¹ * (g⁻¹ * a * g)⁻¹ * j * (g⁻¹ * a * g) ∈
          zStarIn (oddIn M₁ ⊔ J)) →
        ∃ m ∈ M₁, g⁻¹ * a * g = m⁻¹ * a * m

@[expose] def L34Lemma46 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
      IsCyclic ↥(S ⊓ zStarIn J) ∧ Nat.card ↥(S ⊓ zStarIn J) = 4

@[expose] def L34Lemma47 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
      IsCyclic ↥(S ⊓ coreActionKernel J) ∧
        ∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J

@[expose] def L34Prop41End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) → L34Sec4Running J A →
    IsCyclic ↥(S ⊓ zStarIn J) → Nat.card ↥(S ⊓ zStarIn J) = 4 →
    IsCyclic ↥(S ⊓ coreActionKernel J) →
    (∀ y ∈ S ⊓ J ⊔ S ⊓ coreActionKernel J, y * y = 1 → y ∈ S ⊓ J) → False

theorem prop41_of_steps (h46 : L34Lemma46) (h47 : L34Lemma47) (hEnd : L34Prop41End) :
    L34Prop41 := by
  intro G _ _ a x J S hset hcent hZ A hA hA8
  by_contra hW
  have hrun : L34Sec4Running J A := ⟨hA, hA8, hW⟩
  obtain ⟨hcyc, h4⟩ := h46 G a x J S A hset hcent hZ hrun
  obtain ⟨hcyc', hinv⟩ := h47 G a x J S A hset hcent hZ hrun
  exact hEnd G a x J S A hset hcent hZ hrun hcyc h4 hcyc' hinv

@[expose] def IsL34Family {G : Type} [Group G] [Finite G] (L : Subgroup G) (t : G) : Prop :=
  (∃ (a x : G) (J : Subgroup G), GSUnbalancingTriple a x J ∧
      IsL34Type (J ⧸ Open.fusionZStar J) ∧ orderOf t = 2 ∧
      (t ∈ coreActionKernel J ∧ a * t = t * a ∧ J ≤ centralizer ({t} : Set G)) ∧
      L = pumpUp J t) ∧
    IsL34Type (L ⧸ Open.fusionZStar L) ∧ GSWeakMaximalComponent L ∧
    ¬ oddIn L ≤ (center ↥L).map L.subtype ∧
    ∀ A : Subgroup G, IsEightGroup A → A ≤ L ⊔ zpowers t ∨ A ≤ coreActionKernel L →
      wGroup A = ⊥

@[expose] def L34Prop51Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G], L34BaseSetting G →
    (∃ (a x : G) (J S : Subgroup G), L34Sec4Setting G a x J S ∧ (∀ s ∈ S, s * a = a * s) ∧
      (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J)) →
    ∃ (L : Subgroup G) (t : G), IsL34Family L t

@[expose] def L34Sec5Setting (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G)
    (S T : Subgroup G) : Prop :=
  L34BaseSetting G ∧ IsL34Family L t ∧
    (∀ (L₁ : Subgroup G) (t₁ : G), IsL34Family L₁ t₁ →
      toLex (twoExp (zStarIn L₁), twoExp (coreActionKernel L₁)) ≤
        toLex (twoExp (zStarIn L), twoExp (coreActionKernel L))) ∧
    IsSylowTwoIn S (normalizer (L : Set G)) ∧ t ∈ S ∧ S ≤ T ∧ IsSylowTwoIn T ⊤

@[expose] def L34Lemma53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T →
    ∀ u ∈ S, orderOf u = 2 → u ∉ coreActionKernel L → u ∈ L ⊔ zpowers t →
      oddIn L ⊓ centralizer ({u} : Set G) ≠ ⊥ ∧
        ∃ u₁ ∈ ({u, u * t} : Set G), ¬ oddIn L ⊓ centralizer ({u₁} : Set G) ≤
          oddIn (centralizer ({u₁} : Set G))

@[expose] def L34UnbalancingSet {G : Type} [Group G] [Finite G] (L : Subgroup G) (t : G)
    (S : Subgroup G) : Set G :=
  {u | u ∈ S ⊓ L ⊔ zpowers t ∧ orderOf u = 2 ∧
    ¬ oddIn L ⊓ centralizer ({u} : Set G) ≤ oddIn (centralizer ({u} : Set G))}

@[expose] def l34K {G : Type} [Group G] [Finite G] (L : Subgroup G) (u : G) : Subgroup G :=
  ⨆ (K₁ : Subgroup G) (_ : K₁ ≤ centralizer ({u} : Set G))
    (_ : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (_ : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁), K₁

@[expose] def L34Lemma55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T →
    (∀ z ∈ S ⊓ coreActionKernel L, orderOf z = 2 →
      ∀ K : Subgroup G, K ≤ centralizer ({z} : Set G) →
        IsPComponent 2 (K.subgroupOf (centralizer ({z} : Set G))) →
        ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
            Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f) ∨
          IsL34Type (K ⧸ Open.fusionZStar K)) →
        K = (⨆ (g : G) (_ : g ∈ centralizer ({z} : Set G)), conjugate (gsFixedLayer L z) g) ∧
          IsL34Type (K ⧸ Open.fusionZStar K)) ∧
    (∀ z ∈ S ⊓ coreActionKernel L, orderOf z = 2 → z ≠ t →
      ∀ y ∈ oddIn L, z * y * z⁻¹ = y⁻¹) ∧
    (∀ u ∈ L34UnbalancingSet L t S, ∀ K₁ : Subgroup G, K₁ ≤ l34K L u →
      IsPComponent 2 (K₁.subgroupOf (l34K L u)) →
      omegaOne (S ⊓ coreActionKernel L) ≤ normalizer (K₁ : Set G) ∧
        S ⊓ coreActionKernel L ⊓ coreActionKernel K₁ = ⊥) ∧
    IsElemTwo (omegaOne (S ⊓ coreActionKernel L)) ∧
      Nat.card ↥(omegaOne (S ⊓ coreActionKernel L)) ≤ 4

@[expose] def L34Lemma56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ¬ IsSylowTwoIn S ⊤

@[expose] def L34Lemma58 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T →
    (omegaOne (S ⊓ coreActionKernel L) = zpowers t → S ⊓ coreActionKernel L = zpowers t) ∧
    (S ⊓ coreActionKernel L ⊓ L ≠ ⊥ →
      S ⊓ coreActionKernel L = omegaOne (S ⊓ coreActionKernel L) ∧
        ∀ y ∈ S ⊓ coreActionKernel L ⊓ L, y * y = 1)

@[expose] def L34Lemma59 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T →
    ∃ z : G, orderOf z = 2 ∧ z ≠ t ∧
      omegaOne (S ⊓ coreActionKernel L) = zpowers t ⊔ zpowers z ∧
      pRank 2 ↥(S ⊓ L ⊔ zpowers t ⊔ zpowers z) = 6 ∧ pRank 2 ↥S = 6

@[expose] def L34SmallProduct {G : Type} [Group G] [Finite G] (K : Subgroup G) : Prop :=
  ∃ (r : ℕ) (Ks : Fin r → Subgroup G), 1 ≤ r ∧ r ≤ 4 ∧
    (∀ i, Ks i ≤ K ∧ IsPComponent 2 ((Ks i).subgroupOf K) ∧
      (IsL2Type 5 (Ks i ⧸ Open.fusionZStar (Ks i)) ∨
        IsL2Type 7 (Ks i ⧸ Open.fusionZStar (Ks i)))) ∧
    (∀ K₁ : Subgroup G, K₁ ≤ K → IsPComponent 2 (K₁.subgroupOf K) → ∃ i, K₁ = Ks i) ∧
    K ≤ (⨆ i, Ks i) ⊔ oddIn K

@[expose] def L34Lemma510 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S,
      (∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
        Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) →
      L34SmallProduct (l34K L u)

@[expose] def L34Lemma511 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S,
      (∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
        Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) →
      ¬ L34SmallProduct (l34K L u)

@[expose] def L34UnbalancingSetNonempty : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
    L34Sec5Setting G L t S T → (L34UnbalancingSet L t S).Nonempty

theorem false_of_sec5_steps (h510 : L34Lemma510) (h511 : L34Lemma511)
    (hne : L34UnbalancingSetNonempty) {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) : False := by
  obtain ⟨u₀, hu₀⟩ := hne G L t S T hset
  have hfin : (L34UnbalancingSet L t S).Finite := Set.toFinite _
  obtain ⟨u, hu, hmax⟩ := Set.exists_max_image (L34UnbalancingSet L t S)
    (fun v => Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G))) hfin ⟨u₀, hu₀⟩
  exact h511 G L t S T hset u hu hmax (h510 G L t S T hset u hu hmax)

end CFSG.ComponentClassification.GrSLit
