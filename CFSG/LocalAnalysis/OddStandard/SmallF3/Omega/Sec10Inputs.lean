module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Notation

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Fact1051 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P S : Subgroup G) (t z : G) (K1 K2 U : Subgroup G),
    IsPSp43 L → IsSylow2Of P L → P ≤ S → S ≤ normalizer (L : Set G) → IsPGroup 2 S →
    orderOf t = 2 → t ∈ centralizer (L : Set G) → S ≤ centralizer ({t} : Set G) →
    z ∈ centerIn P → orderOf z = 2 → (∀ s ∈ S, s * z = z * s) →
    Sl23PocketIn L z K1 → Sl23PocketIn L z K2 → K1 ≠ K2 →
    secW t K1 K2 ≤ U → U ≤ S → centralizer (L : Set G) ⊓ U = zpowers t →
    (∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ secW t K1 K2 ∧ u * u ∈ secW t K1 K2) →
    ∀ n : ℕ, 1 ≤ n → (secW t K1 K2).relIndex U = 2 ^ n →
      n ≤ 2 ∧ 2 ^ n * Nat.card {w : G // w ∈ secW t K1 K2 ∧
        ∀ u ∈ U, w * u * w⁻¹ * u⁻¹ ∈ zpowers z} < Nat.card (secW t K1 K2)

@[expose] def Asc82Fact107c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → IsPSp43 L → S ≤ normalizer (L : Set G) →
    centralizer (L : Set G) ⊓ S = zpowers t → IsSylow2Of (S ⊓ L) L →
      secA t S L = JElem S ∨
        ∃ r ∈ S, orderOf r = 2 ∧ InducesTypeSome L r 5 1 4 (-1) ∧
          secA2 t r K1 K2 ≠ secA t S L ∧
          ∀ X : Subgroup G, IsNormalE32In S X ↔ (X = secA t S L ∨ X = secA2 t r K1 K2)

@[expose] def Asc82Fact218c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ z u : G, IsI4PlusIn L z → IsI4PlusIn L u → z ≠ u → z * u = u * z →
      InducesTypeSome L (u * z) 5 1 2 (-1)

@[expose] def Asc82Fact218d : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ (z : G) (K1 K2 : Subgroup G), IsI4PlusIn L z → Sl23PocketIn L z K1 → Sl23PocketIn L z K2 →
      K1 ≠ K2 → ∀ u : G, u ∈ L → orderOf u = 2 → u * z = z * u →
        InducesTypeSome L u 5 1 2 (-1) →
          (CFSG.conjugate K1 u = K1 ∧ CFSG.conjugate K2 u = K2 ∧ ∃ k ∈ K1, k * u * k⁻¹ = u * z) ∨
            (CFSG.conjugate K1 u = K2 ∧ IsI4PlusIn L (u * z))

@[expose] def Asc82Fact218e : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ (z : G) (K1 K2 : Subgroup G), IsI4PlusIn L z → Sl23PocketIn L z K1 → Sl23PocketIn L z K2 →
      K1 ≠ K2 → ∀ u : G, InducesTypeSome L u 5 1 2 1 → CFSG.conjugate K1 u = K2 →
        InducesTypeSome L (u * z) 5 1 4 (-1)

@[expose] def Asc82Fact218f : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ s u : G, (InducesTypeSome L s 5 1 2 1 ∨ InducesTypeSome L s 5 1 2 (-1)) →
      u ∈ normalizer (L : Set G) → u * u ∈ centralizer (L : Set G) →
      u ∉ centralizer (L : Set G) → s⁻¹ * u ∉ centralizer (L : Set G) →
      (∀ g ∈ oTwoRes (L ⊓ centralizer ({s} : Set G)), u * g = g * u) →
        InducesTypeSome L u 5 1 4 1 ∨ InducesTypeSome L u 5 1 4 (-1)

@[expose] def Asc82Prince : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B V H : Subgroup G) (φ φ₀ : (Fin 5 → ZMod 2) → G),
    IsPermModuleMod (n := 5) IsEvenVec {0} φ V B H (alternatingGroup (Fin 5)) →
    IsPermModuleVia IsEvenVec φ₀ B H (alternatingGroup (Fin 5)) →
    (∀ h ∈ H, ∀ σ ∈ alternatingGroup (Fin 5),
      (∀ v, IsEvenVec v → (h * φ v * h⁻¹)⁻¹ * φ (permVec σ v) ∈ B) →
        ∀ v, IsEvenVec v → h * φ₀ v * h⁻¹ = φ₀ (permVec σ v)) →
      IsElemAb2 V 8 ∨ IsZ4Pow4 V

@[expose] def IsO4Plus4 (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* WrZ2 ↥(alternatingGroup (Fin 5)))

@[expose] def IsO4Minus4 (Q : Type) [Group Q] : Prop :=
  ∃ E : Subgroup Q, E.Normal ∧ E.index = 2 ∧ LieModel ↥E .PSL 2 2 4 ∧
    centralizer (E : Set Q) = ⊥

@[expose] def IsL34Two (Q : Type) [Group Q] : Prop :=
  ∃ E : Subgroup Q, E.Normal ∧ E.index = 2 ∧ LieModel ↥E .PSL 3 2 2 ∧
    centralizer (E : Set Q) = ⊥

end CFSG.OddStandard.SmallF3.Omega
