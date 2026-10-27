module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.EichlerDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

structure HaradaFacts2 (H : Type) [Group H] (E : Subgroup H) (a z b z₁ : H)
    (S T T' W0 : Subgroup H) (ι : Elem2 6 →* H) (zv : V6) (R0 F : Subgroup H) : Prop
    extends HaradaFacts H E a z b z₁ S T T' W0 ι where
  ι_zv : ι (Multiplicative.ofAdd zv) = z
  lam_zv : lam zv = 0
  qm_zv : qm zv = 0
  card_R0 : Nat.card R0 = 2 ^ 8
  R0_le_centralizer : R0 ≤ centralizer ({z} : Set H)
  R0_le_normalizer : R0 ≤ normalizer (ι.range : Set H)
  R0_normal : ∀ c ∈ centralizer ({z} : Set H), ∀ x ∈ R0, c * x * c⁻¹ ∈ R0
  R0_max : ∀ P : Subgroup H, P ≤ centralizer ({z} : Set H) → IsPGroup 2 P →
    (∀ c ∈ centralizer ({z} : Set H), ∀ x ∈ P, c * x * c⁻¹ ∈ P) → P ≤ R0
  R0_sq : ∀ x ∈ R0, x ^ 2 ∈ zpowers z
  R0_comm : ∀ x ∈ R0, ∀ y ∈ R0, x * y * x⁻¹ * y⁻¹ ∈ zpowers z
  R0_inter : ∀ v : V6, ι (Multiplicative.ofAdd v) ∈ R0 ↔ bil v zv = 0
  R0_eichler : ∀ r ∈ R0, ∃ u : V6, bil u zv = 0 ∧ lam u = 0 ∧
    ∀ x : V6, r * ι (Multiplicative.ofAdd x) * r⁻¹ = ι (Multiplicative.ofAdd (eichF zv u x))
  R0_surj : ∀ u : V6, bil u zv = 0 → lam u = 0 → ∃ r ∈ R0,
    ∀ x : V6, r * ι (Multiplicative.ofAdd x) * r⁻¹ = ι (Multiplicative.ofAdd (eichF zv u x))
  R0_faith : ∀ c ∈ centralizer ({z} : Set H),
    (∀ x ∈ R0, c * x * c⁻¹ * x⁻¹ ∈ zpowers z) → c ∈ R0
  F_le_centralizer : F ≤ centralizer ({z₁} : Set H)
  F_le_normalizer : F ≤ normalizer (ι.range : Set H)
  F_iso : Nonempty (F ≃* alternatingGroup (Fin 5))

end CFSG.EvenSporadicStandard.HNRecog
