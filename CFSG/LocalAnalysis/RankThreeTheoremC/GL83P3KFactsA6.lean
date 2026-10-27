module

public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.GH74.Exceptional Subgroup
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

noncomputable def conjLinesIn {X : Type} [Group X] (B : Subgroup X) (x : X) : ℕ :=
  Set.ncard {c : Subgroup X | ∃ g : X, c = (zpowers x).map (MulAut.conj g).toMonoidHom ∧ c ≤ B}

@[expose] def KFact1435 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (P : Sylow 3 X) (x : X),
    K.Normal → IsSimpleGroup ↥K → (∃ a b : ↥K, a * b ≠ b * a) →
    centralizer (K : Set X) = ⊥ →
    (IsChevTwo ↥K ∨ ∃ n : ℕ, Nonempty (↥K ≃* alternatingGroup (Fin n))) →
    Nonempty (↥(P : Subgroup X) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
    x ∈ thompsonSubgroup (P : Subgroup X) → x ≠ 1 →
    conjLinesIn (thompsonSubgroup (P : Subgroup X)) x = 3 →
    (∀ D : Subgroup X, D ≤ thompsonSubgroup (P : Subgroup X) →
      (∀ g ∈ normalizer (thompsonSubgroup (P : Subgroup X) : Set X), ∀ d ∈ D, g * d * g⁻¹ ∈ D) →
        D = ⊥ ∨ D = thompsonSubgroup (P : Subgroup X)) →
    (∀ S : Subgroup X,
      CFSG.ABGLocalTools.IsSylowOf 2 S (normalizer (thompsonSubgroup (P : Subgroup X) : Set X)) →
        ∃ a ∈ S, ∃ b ∈ S,
          a * b * a⁻¹ * b⁻¹ ∉ centralizer (thompsonSubgroup (P : Subgroup X) : Set X)) →
    CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({x} : Set X)) →
    x ∈ K ∧ Nonempty (↥K ≃* PSp43) ∧ Nat.card ↥(K ⊓ centralizer ({x} : Set X)) = 108

@[expose] def KFact2811 : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (L : Subgroup T), Nonempty (↥L ≃* PSp43) →
    ∀ z ∈ L, z ^ 2 = 1 → z ≠ 1 → Nat.card ↥(L ⊓ centralizer ({z} : Set T)) = 576 →
    ∀ x ∈ L, x ^ 3 = 1 → Nat.card ↥(L ⊓ centralizer ({x} : Set T)) = 108 →
    ∀ A : Subgroup T, A ≠ ⊥ → IsElemAbelian 2 A →
      A ≤ pCoreOf 2 (L ⊓ centralizer ({z} : Set T)) →
      (¬ A ≤ zpowers z → ∃ g₁ ∈ L, ∃ g₂ ∈ L,
        x ∈ A.map (MulAut.conj g₁).toMonoidHom ⊔ A.map (MulAut.conj g₂).toMonoidHom) ∧
      ∃ g : Fin 4 → T, (∀ i, g i ∈ L) ∧ x ∈ ⨆ i, A.map (MulAut.conj (g i)).toMonoidHom

@[expose] def KFactPSp43ElemLe8 : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (L : Subgroup T), Nonempty (↥L ≃* PSp43) →
    ∀ z ∈ L, z ^ 2 = 1 → z ≠ 1 → Nat.card ↥(L ⊓ centralizer ({z} : Set T)) = 576 →
    ∀ A : Subgroup T, IsElemAbelian 2 A → A ≤ pCoreOf 2 (L ⊓ centralizer ({z} : Set T)) →
      Nat.card A ≤ 8

@[expose] def KFactPSp43TwoSubgroups : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (L : Subgroup T), L.Normal → Nonempty (↥L ≃* PSp43) →
    centralizer (L : Set T) = ⊥ →
    ∀ (Q U : Subgroup T) (x : T), Q ≤ L → IsElemAbelian 3 Q → Nat.card Q = 27 → U ≤ Q →
      Nat.card U = 9 → x ∈ U → x ∈ L → Nat.card ↥(L ⊓ centralizer ({x} : Set T)) = 108 →
      (∀ g ∈ L, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ U →
        (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x) →
      ∀ Y : Subgroup T, IsPGroup 2 Y → U ≤ normalizer (Y : Set T) →
        Y ≤ normalizer (Q : Set T) ∨ ∃ z ∈ L, z ^ 2 = 1 ∧ z ≠ 1 ∧
          Nat.card ↥(L ⊓ centralizer ({z} : Set T)) = 576 ∧
          Y ≤ pCoreOf 2 (L ⊓ centralizer ({z} : Set T))

@[expose] def KFactA6TwoNormalized : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → centralizer (K : Set X) = ⊥ →
    IsRankThreeA6 ↥K → ∀ T : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 T K →
      ∀ S : Subgroup X, IsPGroup 2 S → T ≤ normalizer (S : Set X) → S = ⊥

end CFSG.LocalAnalysis.RankThreeTheoremC
