module

public import CFSG.Open.Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def KFactMSideAlmostSimpleE27 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K →
    Subgroup.centralizer (K : Set X) = ⊥ →
    ∀ (R T : Subgroup X) (z : X), IsElemAbelian 3 R → Nat.card R = 27 → T ≤ R → T ≤ K →
    Nat.card T = 9 → z ∈ R → z ∉ T →
    (∀ r ∈ R, r ∉ T → ∃ n ∈ Subgroup.normalizer (R : Set X), n * r * n⁻¹ ∈ Subgroup.zpowers z) →
    (∀ t ∈ T, t ≠ 1 → ∀ s ∈ T, s ≠ 1 → ∃ n ∈ Subgroup.normalizer (R : Set X), n * z * n⁻¹ = z ∧
      (∀ x ∈ T, n * x * n⁻¹ ∈ T) ∧ n * t * n⁻¹ = s) →
    (∃ S : Sylow 3 ↥(Subgroup.centralizer ({z} : Set X)),
      (S : Subgroup _).map (Subgroup.centralizer ({z} : Set X)).subtype = R) →
    (∀ D : Subgroup X, D ≤ Subgroup.centralizer ({z} : Set X) → ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D) →
    (∀ t ∈ T, t ≠ 1 → ∃ S : Sylow 3 X, (S : Subgroup X) ≤ Subgroup.centralizer ({t} : Set X)) →
    81 ∣ Nat.card X → False

@[expose] def KFactCompFixedThreeElt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), IsComponentOf L ⊤ →
    IsCatalogGroup (L ⧸ Subgroup.center L) → IsPGroup 3 (Subgroup.center L) →
    3 ∣ Nat.card (L ⧸ Subgroup.center L) →
    ∀ u : X, u ^ 3 = 1 → u ∈ Subgroup.normalizer (L : Set X) →
      u ∉ Subgroup.centralizer (L : Set X) →
      (∃ y ∈ L, IsPGroup 3 (Subgroup.zpowers y) ∧ y * u = u * y ∧ ∃ l ∈ L, y * l ≠ l * y) ∨
      (∃ h ∈ L, h ^ 3 = 1 ∧ ∃ c ∈ L, u * h * u⁻¹ = c * h ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧ c * u = u * c ∧
        ∀ x ∈ L, (∀ l ∈ L, x * l = l * x) ↔ x ∈ Subgroup.zpowers c)

@[expose] def KFactCompFixedThreeEltN : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), IsComponentOf L ⊤ →
    IsCatalogGroup (L ⧸ Subgroup.center L) → IsPGroup 3 (Subgroup.center L) →
    3 ∣ Nat.card (L ⧸ Subgroup.center L) →
    ∀ u : X, u ^ 3 = 1 → u ∈ Subgroup.normalizer (L : Set X) →
      u ∉ Subgroup.centralizer (L : Set X) →
      (∀ Q : Subgroup X, Q ≤ Subgroup.centralizer ({u} : Set X) → IsPGroup 3 Q →
        Nat.card Q ≤ 27) →
      (∃ y ∈ L, IsPGroup 3 (Subgroup.zpowers y) ∧ y * u = u * y ∧ ∃ l ∈ L, y * l ≠ l * y) ∨
      (∃ h ∈ L, h ^ 3 = 1 ∧ ∃ c ∈ L, u * h * u⁻¹ = c * h ∧ c ≠ 1 ∧ c ^ 3 = 1 ∧ c * u = u * c ∧
        ∀ x ∈ L, (∀ l ∈ L, x * l = l * x) ↔ x ∈ Subgroup.zpowers c)

theorem KFactCompFixedThreeElt.toN (h : KFactCompFixedThreeElt) : KFactCompFixedThreeEltN :=
  fun X _ _ L hL hcat hZ h3 u hu3 huN huC _ => h X L hL hcat hZ h3 u hu3 huN huC

@[expose] def KFactCompCenterNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), IsComponentOf L ⊤ → L.Normal →
    IsCatalogGroup (L ⧸ Subgroup.center L) →
    ∀ E : Subgroup X, E ≤ L → (∀ e ∈ E, ∀ l ∈ L, e * l = l * e) → IsElemAbelian 3 E →
      Nat.card E = 9 → ∃ e ∈ E, e ≠ 1 ∧ ∃ f ∈ E, f ≠ 1 ∧ ∀ n : X, n * e * n⁻¹ ≠ f

end CFSG.AGLEmbedding
