module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def Asc81bEightFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S : Subgroup G), Open.IsKGroup ↥X → Asc81bHyp X S →
    CFSG.pPrimeCore 2 (↥X ⧸ CFSG.pCore 2 ↥X) ≤ Subgroup.centralizer (barM X S : Set _) ∨
    ∃ Y : Subgroup G, Y ≤ X ∧ IsSubnormal Y X ∧ Nonempty (↥Y ≃* alternatingGroup (Fin 4))

@[expose] def Asc81bEightFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Open.IsKGroup ↥X → Asc81bHyp X S →
    IsTwoPrimeComponent X L → IsSylowTwoOf (S ⊓ L) L → InClassXBlock L

@[expose] def Asc81bEightSix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S : Subgroup G), Open.IsKGroup ↥X → Asc81bHyp X S →
    ∀ Lbar : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X), IsComponentOf Lbar ⊤ →
      barM X S ≤ Subgroup.normalizer (Lbar : Set _)

@[expose] def Asc81bNineThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Open.IsKGroup ↥X → Asc81bHyp X S →
    IsWeakSBlock X S L → NineThreeConclusion X S L

@[expose] def AschbacherLocalCGTBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T : Subgroup G), Open.IsKGroup ↥X → CharTwo X →
    IsSylowTwoOf T X → cgsIn X T ≠ X →
      ∃ Y : Subgroup G, Y ≤ X ∧ IsSubnormal Y X ∧ InClassXBlock Y ∧ ¬ Y ≤ cgsIn X T

@[expose] def D1NoXBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.AGLEmbeddingD2.AGLGlobal G → ∀ M Y : Subgroup G,
    GLBIsMaxTwoLocal M → Y ≤ M → IsSubnormal Y M → InClassXBlock Y → False

@[expose] def IsSLSpG2Index : TauCeti.LieTypeIndex → Prop
  | .A _ q | .B _ q | .G2 q => q.p = 2
  | _ => False

@[expose] def IsSLSpG2Two (Y : Type) [Group Y] : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, IsSLSpG2Index d.1 ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group))

structure TimmesfeldHypA (X Z Q₁ : Subgroup G) : Prop where
  kGroup : Open.IsKGroup ↥X
  charTwo : CharTwo X
  center : ∃ T : Subgroup G, IsSylowTwoOf T X ∧ Z ≤ omegaOneCenterOf T
  ne_bot : Z ≠ ⊥
  le_normalizer : X ⊓ Subgroup.normalizer (Z : Set G) ≤ Subgroup.normalizer (Q₁ : Set G)
  le_core : pCoreOf 2 X ≤ Q₁
  core_le : Q₁ ≤ pCoreOf 2 (X ⊓ Subgroup.normalizer (Z : Set G))
  cgs : cgsIn X Q₁ = X ⊓ Subgroup.normalizer (Z : Set G)
  lt : X ⊓ Subgroup.normalizer (Z : Set G) < X

@[expose] def Timmesfeld34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Z Q₁ Kᵢ : Subgroup G), TimmesfeldHypA X Z Q₁ →
    IsTwoPrimeComponent X Kᵢ → ¬ Kᵢ ≤ Subgroup.normalizer (Z : Set G) →
      (Q₁ ≤ Subgroup.normalizer (Kᵢ : Set G) ∧ pCoreOf 2 (Kᵢ ⊔ Q₁) < Q₁) ∧
      IsSLSpG2Two (↥(barM X Kᵢ) ⧸ Subgroup.center ↥(barM X Kᵢ)) ∧
      Q₁ ≤ pCoreOf 2 ((Kᵢ ⊔ Q₁) ⊓ Subgroup.normalizer (Z : Set G)) ∧
      IsParabolicTwo (barM X Kᵢ) (barM X (Kᵢ ⊓ Subgroup.normalizer (Z : Set G)))

@[expose] def TimmesfeldE (M₀ M₁ : Subgroup G) : Prop :=
  ∃ Z T : Subgroup G, Z ≠ ⊥ ∧ IsSylowTwoOf T M₀ ∧ Z ≤ omegaOneCenterOf T ∧ Z ≤ M₁ ∧
    M₁ ≤ Subgroup.normalizer (Z : Set G)

@[expose] def TimmesfeldThreeMaxLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCharTwoType G → IsKProper G →
    ∀ M H : Subgroup G, GLBIsMaxTwoLocal M → GLBIsMaxTwoLocal H → M ≠ H →
      pCoreOf 2 M ≤ pCoreOf 2 H → pCoreOf 2 H ≤ M → TimmesfeldE M H →
      (∃ K₀ : Subgroup G, IsTwoPrimeComponent M K₀ ∧ ¬ K₀ ≤ H ∧
        ∀ M' : Subgroup G, GLBIsMaxTwoLocal M' → K₀ ≤ M' → M' = M) →
      (∀ p : ℕ, p.Prime → p ≠ 2 → Open.pRank p (M ⊓ H) ≤ 2) ∨ ((M ⊓ H).subgroupOf H).Normal

@[expose] def centralizerModTwoCore (J : Subgroup G) : Subgroup G :=
  Subgroup.closure {g : G | g ∈ Subgroup.normalizer (J : Set G) ∧
    ∀ x ∈ J, g * x * g⁻¹ * x⁻¹ ∈ pCoreOf 2 J}

@[expose] def InFooteB [Finite G] (J : Subgroup G) : Prop :=
  ∃ S : Subgroup G, IsSylowTwoOf S (centralizerModTwoCore J) ∧
    IsFooteBlock (Subgroup.normalizer (S : Set G)) J

@[expose] def barIn (J₂ J₁ : Subgroup G) : Subgroup (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) :=
  (J₁.subgroupOf J₂).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J₂))

theorem barIn_eq_barM (J₂ J₁ : Subgroup G) : barIn J₂ J₁ = barM J₂ J₁ := rfl

@[expose] def centralizerBarIn (J₂ T : Subgroup G) : Subgroup (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) :=
  barIn J₂ (Subgroup.closure {x : G | x ∈ J₂ ∧ ∀ t ∈ T, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 J₂})

@[expose] def FooteArrow (J₁ J₂ : Subgroup G) : Prop :=
  J₁ ≤ J₂ ∧ blockU J₁ = ⁅pCoreOf 2 J₂, J₁⁆ ∧
    ∃ T : Subgroup G, IsPGroup 2 T ∧ T ≤ Subgroup.normalizer (J₂ : Set G) ∧
      IsComponentOf (barIn J₂ J₁) (centralizerBarIn J₂ T)

@[expose] def InFooteBStar [Finite G] (J : Subgroup G) : Prop :=
  InFooteB J ∧ ∀ J' : Subgroup G, InFooteB J' → FooteArrow J J' → J' = J

@[expose] def FooteFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsCharTwoType G → ∀ J : Subgroup G, InFooteBStar J →
    (¬ ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m))) →
    ∃ M : Subgroup G, GLBIsMaxTwoLocal M ∧ IsFooteBlock M J ∧
      ∀ M' : Subgroup G, GLBIsMaxTwoLocal M' → J ≤ M' → M' = M

@[expose] def FooteSix : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsCharTwoType G → ∀ M J : Subgroup G,
    GLBIsMaxTwoLocal M → IsFooteBlock M J → InFooteB J

@[expose] def IsOrthogonalEven (Y : Type) [Group Y] : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, (∃ m : ℕ, ∃ q : TauCeti.PrimePower, q.p = 2 ∧
      (d.1 = .D m q ∨ d.1 = .twistedD m q ∨ d.1 = .twistedA 3 q ∨ d.1 = .A 3 q ∨
        d.1 = .A 1 q)) ∧ Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ n : ℕ, (n = 5 ∨ n = 8) ∧ Nonempty (Y ≃* alternatingGroup (Fin n)))

@[expose] def IsSymplecticEven (Y : Type) [Group Y] : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, (∃ m : ℕ, ∃ q : TauCeti.PrimePower, q.p = 2 ∧
      (d.1 = .B m q ∨ d.1 = .A 1 q)) ∧ Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ n : ℕ, (n = 5 ∨ n = 6) ∧ Nonempty (Y ≃* alternatingGroup (Fin n)))

@[expose] def FooteSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J₁ J₂ : Subgroup G), IsFooteBlock J₁ J₁ →
    IsFooteBlock J₂ J₂ → J₁ ≠ J₂ → FooteArrow J₁ J₂ →
      (∃ n k : ℕ, 1 ≤ k ∧
        Nonempty ((↥J₁ ⧸ CFSG.pCore 2 ↥J₁) ⧸ Subgroup.center (↥J₁ ⧸ CFSG.pCore 2 ↥J₁) ≃*
          alternatingGroup (Fin n)) ∧
        Nonempty ((↥J₂ ⧸ CFSG.pCore 2 ↥J₂) ⧸ Subgroup.center (↥J₂ ⧸ CFSG.pCore 2 ↥J₂) ≃*
          alternatingGroup (Fin (n + 2 * k))) ∧
        Nat.card (↥(blockU J₁) ⧸ (blockZ J₁).subgroupOf (blockU J₁)) =
          2 ^ (2 * ((n - 1) / 2))) ∨
      (IsSymplecticEven ((↥J₁ ⧸ CFSG.pCore 2 ↥J₁) ⧸ Subgroup.center (↥J₁ ⧸ CFSG.pCore 2 ↥J₁)) ∧
        IsOrthogonalEven ((↥J₂ ⧸ CFSG.pCore 2 ↥J₂) ⧸ Subgroup.center (↥J₂ ⧸ CFSG.pCore 2 ↥J₂))) ∨
      ((∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 2 ∧
          d.1 = .twistedA 3 q) ∧
          Nonempty ((↥J₁ ⧸ CFSG.pCore 2 ↥J₁) ⧸ Subgroup.center (↥J₁ ⧸ CFSG.pCore 2 ↥J₁) ≃*
            (TauCeti.CFSGIndex.lie d).Group)) ∧
        Nat.card (↥(blockU J₁) ⧸ (blockZ J₁).subgroupOf (blockU J₁)) = 2 ^ 8 ∧
        Nat.card (↥(blockU J₂) ⧸ (blockZ J₂).subgroupOf (blockU J₂)) = 2 ^ 12)

@[expose] def KFactSLGTwoNotArrow : Prop :=
  ∀ (Y : Type) [Group Y],
    ((∃ n m : ℕ, 3 ≤ n ∧ 1 ≤ m ∧ Nonempty (Y ≃*
        (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 m) ⧸
          Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 m))))) ∨
      (∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.p = 2 ∧
          2 ≤ q.exponent ∧ d.1 = .G2 q) ∧ Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group))) →
    ¬ IsSymplecticEven Y ∧ (∀ k : ℕ, Nonempty (Y ≃* alternatingGroup (Fin k)) → k = 8) ∧
    (¬ ∃ k : ℕ, Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∧
    ¬ ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 2 ∧
        d.1 = .twistedA 3 q) ∧ Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def KFactUPrime (p : ℕ) (K : Type) [Group K] [Finite K] : Prop :=
  ∀ T : Sylow p K, GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
    (∀ Y : Subgroup K, GLBCore p 1 (T : Subgroup K) ≤ Y →
      Y = GLBCore p 1 (T : Subgroup K) ∨ Y = ⊤) ∧
    (∀ N : Subgroup K, N ≤ GLBCore p 1 (T : Subgroup K) →
      (N.subgroupOf (GLBCore p 1 (T : Subgroup K))).Normal → p.Coprime (Nat.card N) →
        N = ⊥) ∧
    ∀ f : MulAut K, (∀ k ∈ GLBCore p 1 (T : Subgroup K), f k = k) → f = 1

end CFSG.AGLEmbedding
