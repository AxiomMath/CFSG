module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def PerfectSectionsAltSq (p : ℕ) {X : Type*} [Group X] (J : Subgroup X) : Prop :=
  ∀ V : Subgroup X, V ≤ J → ⁅V, V⁆ = V → ∃ V₀ : Subgroup X, V₀ ≤ V ∧
    (V₀.subgroupOf V).Normal ∧ p.Coprime (Nat.card V₀) ∧
    ∃ f : ↥V →* alternatingGroup (Fin p) × alternatingGroup (Fin p), f.ker = V₀.subgroupOf V

@[expose] def KFactAltTwoPGamma : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → IsAltTwoP p K →
    ∀ T : Sylow p K, CFSG.pCore p (GLBCore p 1 (T : Subgroup K)) = ⊥ ∧
      ∀ V : Subgroup (GLBCore p 1 (T : Subgroup K)), ⁅V, V⁆ = V →
        ∃ f : ↥V →* alternatingGroup (Fin p) × alternatingGroup (Fin p), Function.Injective f

@[expose] def KFactBlockOutPrime : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    ∀ p : ℕ, p.Prime → 5 ≤ p →
    (IsOrthogonalTwo ↥L ∨ ∃ m : ℕ, Nonempty (↥L ≃* alternatingGroup (Fin m)) ∨
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin m))) →
    ∀ x ∈ Subgroup.normalizer (L : Set Y), x ^ p = 1 → x ∈ L ⊔ Subgroup.centralizer (L : Set Y)

@[expose] def KFactBlockAutAltInner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    ∀ p : ℕ, (p = 5 ∨ p = 7) → IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
    IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    PerfectSectionsAltSq p J → ∀ x ∈ Subgroup.normalizer (L : Set Y),
    x ∈ Subgroup.normalizer (J : Set Y) → x ^ p = 1 →
    (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) → x ∈ L ⊔ Subgroup.centralizer (L : Set Y)

@[expose] def KFactBlockOutRankAlt : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, (p = 5 ∨ p = 7) → PerfectSectionsAltSq p J →
    ∀ E : Subgroup Y, E ≤ Subgroup.normalizer (L : Set Y) → IsElemAbelian p E →
      Nat.card E = p ^ 2 → E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) = ⊥ → False

@[expose] def KFactBlockToralAlt : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    ∀ p : ℕ, (p = 5 ∨ p = 7) → PerfectSectionsAltSq p J →
    ∀ x ∈ L, x ^ p = 1 → x ∉ Subgroup.centralizer (L : Set Y) →
    (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    (∃ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 3) → False

@[expose] def CitedBlockThreeToralAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → (p = 5 ∨ p = 7) →
    PerfectSectionsAltSq p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →
    ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
      IsElemAbelian p E → Nat.card E = p ^ 3 → False

end CFSG.AGLEmbedding
