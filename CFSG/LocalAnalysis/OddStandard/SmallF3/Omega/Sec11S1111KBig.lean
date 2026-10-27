module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Step1111KBig : Prop :=
  Asc82Pre11 →
    ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G)
      (K1 K2 T R : Subgroup G), Sec11Ctx G t L S z K1 K2 T R →
      IsSylow2Of R (centralizer ({z} : Set G)) →
      (∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ R → h⁻¹ * t * h ∈ secD K1 K2 R) →
      IsDih2 (Subgroup.closure
        {s | s ∈ R ∧ ∃ h ∈ centralizer ({z} : Set G), s = h⁻¹ * t * h}) →
      8 ≤ Nat.card (Subgroup.closure
        {s | s ∈ R ∧ ∃ h ∈ centralizer ({z} : Set G), s = h⁻¹ * t * h}) →
      (∃ P : Subgroup G, IsSylow2Of P (secXH t z) ∧ IsDihSd P) →
        centralizer ({z} : Set G) ≤
          normalizer ((K1 ⊔ K2 ⊔ oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G)

@[expose] def Asc82Step1111KBigSD : Prop :=
  Asc82Pre11 →
    ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G)
      (K1 K2 T R : Subgroup G), Sec11Ctx G t L S z K1 K2 T R →
      IsSylow2Of R (centralizer ({z} : Set G)) →
      (∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ R → h⁻¹ * t * h ∈ secD K1 K2 R) →
      IsDih2 (Subgroup.closure
        {s | s ∈ R ∧ ∃ h ∈ centralizer ({z} : Set G), s = h⁻¹ * t * h}) →
      8 ≤ Nat.card (Subgroup.closure
        {s | s ∈ R ∧ ∃ h ∈ centralizer ({z} : Set G), s = h⁻¹ * t * h}) →
      (∃ P : Subgroup G, IsSylow2Of P (secXH t z) ∧
        (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥P ≃* CFSG.Open.SemidihedralGroup n)) ∧
        oddCoreIn (secXH t z) ⊔ P ≠ secXH t z) →
        centralizer ({z} : Set G) ≤
          normalizer ((K1 ⊔ K2 ⊔ oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G)

end CFSG.OddStandard.SmallF3.Omega
