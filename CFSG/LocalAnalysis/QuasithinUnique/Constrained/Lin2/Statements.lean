module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

@[expose] def Lemma2_4_8 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  (S.relIndex T = 2 ∧ T ≤ Subgroup.normalizer (S : Set G) ∧
      T ≤ Subgroup.normalizer (thompsonJ S : Set G)) ∧
  (pCoreOf 2 L = blockU L ∧ blockU L = pCoreOf 2 H) ∧
  (thompsonJ S = baum S ∧ IsSylowTwoOf (thompsonJ S) L ∧
    ∀ x ∈ T, x ∉ S →
      thompsonJ S = blockU L ⊔ conjR (blockU L) x ∧
      blockU L ⊓ conjR (blockU L) x = centerOf (thompsonJ S) ∧
      (∀ A : Subgroup G, IsMaxElemAbelian S A ↔ A = blockU L ∨ A = conjR (blockU L) x) ∧
      (∀ A : Subgroup G, IsMaxElemAbelian T A ↔ A = blockU L ∨ A = conjR (blockU L) x)) ∧
  (∀ x ∈ T, x ∉ S →
    conjR D x ≤ Subgroup.normalizer (L : Set G) ∧
      (centerOf L = ⊥ ∨ (IsElemAbelian 2 (centerOf L) ∧ Nat.card (centerOf L) = 2 ^ n ∧
        ActsRegularlyOn (conjR D x) (nonIdentity (centerOf L))))) ∧
  (∃ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B) ∧
  (∀ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B →
    (centerOf L ≠ ⊥ → ∀ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S →
        B = D ⊔ conjR D x ∧ D ⊓ conjR D x = ⊥) ∧
    (centerOf L = ⊥ →
      B ≤ D ⊔ Subgroup.centralizer (centerOf (thompsonJ S) : Set G) ∧
        ActsRegularlyOn D (nonIdentity (centerOf (thompsonJ S))))) ∧
  (∀ x ∈ T, x ∉ S →
    IsElemAbelian 2 (blockU L) ∧ IsElemAbelian 2 (conjR (blockU L) x) ∧
      ∀ E : Subgroup G, E ≤ thompsonJ S → IsElemAbelian 2 E →
        E ≤ blockU L ∨ E ≤ conjR (blockU L) x) ∧
  (IsCyclic ↥D ∧ Nat.card D = 2 ^ n - 1) ∧
  (∀ V : Subgroup G, centerOf (thompsonJ S) ≤ V → V ≤ blockU L →
    D ≤ Subgroup.normalizer (V : Set G) → V = centerOf (thompsonJ S) ∨ V = blockU L)

@[expose] def Lemma2_4_11 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  Subgroup.normalizer (pCoreOf 2 H : Set G) = Subgroup.normalizer (L : Set G) ∧
  (∀ X : Subgroup G, L ≤ X → pCoreOf 2 X ≠ ⊥ →
    X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
  (centerOf L ≠ ⊥ → fusionIsTI (centerOf L) ∧
    Subgroup.normalizer (pCoreOf 2 H : Set G) = Subgroup.normalizer (centerOf L : Set G))

@[expose] def Lemma2_4_12 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  ∀ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B →
    (IsCyclic ↥(S ⊓ Subgroup.normalizer (B : Set G)) ∧
      thompsonJ S ⊓ (S ⊓ Subgroup.normalizer (B : Set G)) = ⊥ ∧
      thompsonJ S ⊔ (S ⊓ Subgroup.normalizer (B : Set G)) = S ∧
      L ⊓ (S ⊓ Subgroup.normalizer (B : Set G)) = ⊥ ∧
      H = L ⊔ (S ⊓ Subgroup.normalizer (B : Set G))) ∧
    ∀ f ∈ S ⊓ Subgroup.normalizer (B : Set G), f ≠ 1 → f ^ 2 = 1 →
      Even n ∧
      (∀ r ∈ thompsonJ S, (f * r) ^ 2 = 1 → ∃ s ∈ thompsonJ S, s⁻¹ * f * s = f * r) ∧
      ((∃ m : ℕ, n = 2 * m ∧ 1 < m ∧ IsShort2 (L ⊓ Subgroup.centralizer ({f} : Set G)) ∧
          IsLin2Type (L ⊓ Subgroup.centralizer ({f} : Set G)) m ∧
          blockU L ⊓ Subgroup.centralizer ({f} : Set G) =
            blockU (L ⊓ Subgroup.centralizer ({f} : Set G)) ∧
          pCoreOf 2 (L ⊓ Subgroup.centralizer ({f} : Set G)) =
            blockU L ⊓ Subgroup.centralizer ({f} : Set G)) ∨
        (n = 2 ∧
          ((centerOf L = ⊥ ∧
              Nonempty ((L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) ≃*
                Equiv.Perm (Fin 4)) ∧
              pCoreOf 2 (L ⊓ Subgroup.centralizer ({f} : Set G)) =
                blockU L ⊓ Subgroup.centralizer ({f} : Set G)) ∨
            (centerOf L ≠ ⊥ ∧
              Nonempty ((L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) ≃*
                Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) ∧
              pCoreOf 2 (L ⊓ Subgroup.centralizer ({f} : Set G)) =
                blockU L ⊓ Subgroup.centralizer ({f} : Set G))))) ∧
      Nat.card ((lin2Z L (thompsonJ S) ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G)) = 2 ^ (n / 2) ∧
      (centerOf L = ⊥ →
        Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G)) =
          2 ^ (3 * n / 2)) ∧
      (centerOf L ≠ ⊥ →
        Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G)) = 2 ^ (2 * n))

@[expose] def Lemma2_4_14 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  ∀ t ∈ T, t ∉ S → t ^ 2 ∈ thompsonJ S →
    (∃ i : G, t⁻¹ * i ∈ thompsonJ S ∧ i ^ 2 = 1) ∧
    (∀ i j : G, t⁻¹ * i ∈ thompsonJ S → t⁻¹ * j ∈ thompsonJ S → i ^ 2 = 1 → j ^ 2 = 1 →
      ∃ s ∈ thompsonJ S, s⁻¹ * i * s = j) ∧
    (t ^ 2 = 1 →
      (centerOf L = ⊥ ∧
        centerOf (thompsonJ S) = thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) ∧
        ¬ ⁅thompsonJ S, Subgroup.zpowers t⁆ ≤ centerOf (thompsonJ S)) ∨
      (centerOf L = ⊥ ∧ Even n ∧
        Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)) =
          2 ^ (3 * n / 2) ∧
        Nat.card (omegaOneOf (thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)) =
          2 ^ (n / 2)) ∨
      (centerOf L ≠ ⊥ ∧
        Nat.card ((thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)) = 2 ^ (2 * n) ∧
        Nat.card (omegaOneOf (thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)) =
          2 ^ n))

@[expose] def Lemma2_4_16 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  ∀ Z : Subgroup G, Z = lin2Z L (thompsonJ S) →
    (IsElemAbelian 2 Z ∧ Nat.card Z = 2 ^ n ∧ S ≤ Subgroup.normalizer (Z : Set G)) ∧
    (∀ x ∈ T, x ∉ S →
      (centerOf L = ⊥ ∧ conjR Z x = Z ∧ Z = centerOf (thompsonJ S)) ∨
      (centerOf L ≠ ⊥ ∧ centerOf (thompsonJ S) = Z ⊔ conjR Z x ∧ Z ⊓ conjR Z x = ⊥)) ∧
    (∀ x ∈ T, x ∉ S →
      blockU L = ⨆ ℓ : L, conjR (conjR Z x) (ℓ : G) ∧ blockU L = weakClosure Z (blockU L))

@[expose] def Lemma2_4_17 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  ∀ Z : Subgroup G, Z = lin2Z L (thompsonJ S) →
    (T ⊓ Subgroup.centralizer (Z : Set G) = thompsonJ S ∨
      (centerOf L = ⊥ ∧ ∃ t ∈ T, t ∉ S ∧ t ^ 2 = 1 ∧
        T ⊓ Subgroup.centralizer (Z : Set G) = thompsonJ S ⊔ Subgroup.zpowers t ∧
        Z = centerOf (thompsonJ S) ∧
        Z = thompsonJ S ⊓ Subgroup.centralizer ({t} : Set G))) ∧
    (centerOf L = ⊥ → ∃ t ∈ T, T = (T ⊓ Subgroup.centralizer (Z : Set G)) ⊔ Subgroup.zpowers t)

@[expose] def Lemma2_4_18 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  ∀ Z : Subgroup G, Z = lin2Z L (thompsonJ S) →
    fusionIsTI Z ∧
    (centerOf L = ⊥ → Subgroup.normalizer (Z : Set G) = M) ∧
    (centerOf L ≠ ⊥ → Subgroup.normalizer (Z : Set G) = Subgroup.normalizer (pCoreOf 2 H : Set G))

@[expose] def Lemma2_4_19 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  ∀ Z : Subgroup G, Z = lin2Z L (thompsonJ S) → thompsonJ S = weakClosure Z T

@[expose] def Lemma2_4_20 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  ∀ Z : Subgroup G, Z = lin2Z L (thompsonJ S) → centerOf L ≠ ⊥ →
    (∀ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B →
      ∀ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S →
        ActsRegularlyOn B (lin2Delta (thompsonJ S) Z x)) ∧
    ∀ x ∈ T, x ∉ S →
      (∀ u ∈ lin2Delta (thompsonJ S) Z x,
        (∃ m ∈ M, m⁻¹ * u * m ∈ centerOf T) ∧
        Subgroup.centralizer ({u} : Set G) ≤ M ∧ ∀ g : G, g⁻¹ * u * g ∉ Z) ∧
      (∀ i ∈ thompsonJ S, i ^ 2 = 1 → i ≠ 1 →
        ∃ g : G, g⁻¹ * i * g ∈ lin2Delta (thompsonJ S) Z x ∨
          (g⁻¹ * i * g ∈ Z ∧ g⁻¹ * i * g ≠ 1)) ∧
      M ≤ Subgroup.normalizer (thompsonJ S : Set G) ∧
      (∀ u ∈ lin2Delta (thompsonJ S) Z x,
        Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (thompsonJ S : Set G)) ∧
      (∀ z ∈ Z, z ≠ 1 → ∀ P : Subgroup G,
        IsSylowTwoOf P (Subgroup.centralizer ({z} : Set G)) → ∃ g : G, P ≤ conjR S g) ∧
      (∀ u ∈ lin2Delta (thompsonJ S) Z x, ∀ X : Subgroup G,
        X ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 X → X = weakClosure Z X →
          X ≤ thompsonJ S)

@[expose] def Lemma2_4_21 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  thompsonJ S = strongClosure (pCoreOf 2 H) T ∧
  ∀ i ∈ thompsonJ S, i ^ 2 = 1 → ∀ g : G, g⁻¹ * i * g ∈ T → g⁻¹ * i * g ∈ thompsonJ S

@[expose] def Lemma2_4_22 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  (¬ ∃ t ∈ T, T = thompsonJ S ⊔ Subgroup.zpowers t) ∧ thompsonJ S < S

@[expose] def Lemma2_4_23 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  ∀ s ∈ S, s ∉ thompsonJ S → s ^ 2 = 1 →
    ((∃ m : ℕ, n = 2 * m ∧ 1 < m ∧ IsShort2 (L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
        IsLin2Type (L ⊓ Subgroup.centralizer ({s} : Set G)) m ∧
        blockU L ⊓ Subgroup.centralizer ({s} : Set G) =
          blockU (L ⊓ Subgroup.centralizer ({s} : Set G))) ∨
      (n = 2 ∧
        (Nonempty ((L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) ≃*
            Equiv.Perm (Fin 4)) ∨
          Nonempty ((L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) ≃*
            Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))))) ∧
    thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) =
      strongClosure (pCoreOf 2 H) (T ⊓ Subgroup.centralizer ({s} : Set G)) ∧
    (blockU L ⊓ Subgroup.centralizer ({s} : Set G) =
        pCoreOf 2 (L ⊓ Subgroup.centralizer ({s} : Set G)) ∧
      Subgroup.normalizer ((blockU L ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) :
          Set G) ≤ Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
    (T = thompsonJ S ⊔ (T ⊓ Subgroup.centralizer ({s} : Set G)) ∧
      (∃ x ∈ T ⊓ Subgroup.centralizer ({s} : Set G), x ∉ S) ∧
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ({s} : Set G)) (Subgroup.centralizer ({s} : Set G))) ∧
    (centerOf L ≠ ⊥ → 4 < 2 ^ n →
      ∀ x ∈ T ⊓ Subgroup.centralizer ({s} : Set G), x ∉ S →
        (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ (n / 2) ∧
          Nonempty ((L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
              conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G) ≃*
            Matrix.symplecticGroup (Fin 2) F)) ∧
        T ⊓ Subgroup.centralizer ({s} : Set G) ⊓
            Subgroup.centralizer ((L ⊓ Subgroup.centralizer ({s} : Set G) ⊔
              conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x : Subgroup G) : Set G) =
          Subgroup.zpowers s ∧
        (∃ t ∈ T ⊓ Subgroup.centralizer ({s} : Set G),
          T ⊓ Subgroup.centralizer ({s} : Set G) =
            (Subgroup.zpowers s ⊔ thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)) ⊔
              Subgroup.zpowers t) ∧
        (Subgroup.zpowers s ⊔ thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G)).relIndex
            (T ⊓ Subgroup.centralizer ({s} : Set G)) = 2 ^ (n.factorization 2))

@[expose] def Lemma2_4_24 : Prop := Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
  ∀ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B →
    ∀ Z : Subgroup G, Z = lin2Z L (thompsonJ S) →
      (thompsonJ S ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) = ⊥ ∧
        thompsonJ S ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) = T) ∧
      centerOf L = ⊥ ∧
      ∃ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S ∧ x ^ 2 = 1 ∧
        thompsonJ S ⊓ Subgroup.centralizer ({x} : Set G) = Z ∧
        thompsonJ S ⊔ Subgroup.zpowers x = T ⊓ Subgroup.centralizer (Z : Set G) ∧
        IsCyclic ↥(S ⊓ Subgroup.normalizer (B : Set G)) ∧
        T ⊓ Subgroup.normalizer (B : Set G) =
          Subgroup.zpowers x ⊔ (S ⊓ Subgroup.normalizer (B : Set G)) ∧
        Subgroup.zpowers x ⊓ (S ⊓ Subgroup.normalizer (B : Set G)) = ⊥ ∧
        S ⊓ Subgroup.normalizer (B : Set G) ≤ Subgroup.centralizer ({x} : Set G)

@[expose] def Lemma2_4_s1_fusion : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) =>
    ∀ s ∈ S, s ∉ thompsonJ S → s ^ 2 = 1 → ∀ g : G, g⁻¹ * s * g ∈ T → g⁻¹ * s * g ∈ S

@[expose] def Lin2HallExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), ConstrainedSetting G T M H S L →
    ∀ n : ℕ, 1 < n → IsLin2Type L n →
      ∃ D : Subgroup G, IsHallTwoPrimeOf D (conjJoin S L ⊓ M) ∧
        D ≤ Subgroup.normalizer ((conjJoin S L ⊓ S : Subgroup G) : Set G)

@[expose] def Lemma2_4_s2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L D : Subgroup G) (n : ℕ),
    Lin2Cfg2 G T M H S L n D → False

end CFSG.QuasithinUnique.Lin2
