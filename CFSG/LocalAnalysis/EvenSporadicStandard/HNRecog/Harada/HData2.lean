module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.EichlerDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

structure HData2 (G : Type) [Group G] (t z z₁ : G) (ι : Elem2 6 →* G) (zv : V6)
    (R0 F : Subgroup G) : Prop where
  coordElt_zv : coordElt ι zv = z
  lam_zv : lam zv = 0
  qm_zv : qm zv = 0
  card_R0 : Nat.card R0 = 2 ^ 8
  R0_le : R0 ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)
  R0_le_normalizer : R0 ≤ normalizer (ι.range : Set G)
  R0_normal : ∀ c ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G), ∀ x ∈ R0,
    c * x * c⁻¹ ∈ R0
  R0_max : ∀ P : Subgroup G, P ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) →
    IsPGroup 2 P → (∀ c ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G), ∀ x ∈ P,
      c * x * c⁻¹ ∈ P) → P ≤ R0
  R0_sq : ∀ x ∈ R0, x ^ 2 ∈ zpowers z
  R0_comm : ∀ x ∈ R0, ∀ y ∈ R0, x * y * x⁻¹ * y⁻¹ ∈ zpowers z
  R0_inter : ∀ v : V6, coordElt ι v ∈ R0 ↔ bil v zv = 0
  R0_eichler : ∀ r ∈ R0, ∃ u : V6, bil u zv = 0 ∧ lam u = 0 ∧
    ∀ x : V6, r * coordElt ι x * r⁻¹ = coordElt ι (eichF zv u x)
  R0_surj : ∀ u : V6, bil u zv = 0 → lam u = 0 → ∃ r ∈ R0,
    ∀ x : V6, r * coordElt ι x * r⁻¹ = coordElt ι (eichF zv u x)
  R0_faith : ∀ c ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G),
    (∀ x ∈ R0, c * x * c⁻¹ * x⁻¹ ∈ zpowers z) → c ∈ R0
  F_le : F ≤ centralizer ({t} : Set G) ⊓ centralizer ({z₁} : Set G)
  F_le_normalizer : F ≤ normalizer (ι.range : Set G)
  F_iso : Nonempty (F ≃* alternatingGroup (Fin 5))

end CFSG.EvenSporadicStandard.HNRecog.Harada
