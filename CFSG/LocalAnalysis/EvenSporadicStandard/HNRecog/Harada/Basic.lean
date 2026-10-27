module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarHCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

@[expose] def coordElt {G : Type*} [Group G] (ι : Elem2 6 →* G) (v : V6) : G :=
  ι (Multiplicative.ofAdd v)

theorem coordElt_add {G : Type*} [Group G] (ι : Elem2 6 →* G) (v w : V6) :
    coordElt ι (v + w) = coordElt ι v * coordElt ι w := by
  simp only [coordElt, ofAdd_add, map_mul]

theorem coordElt_zero {G : Type*} [Group G] (ι : Elem2 6 →* G) : coordElt ι 0 = 1 := by
  simp [coordElt]

structure HData (G : Type) [Group G] (t z b z₁ : G) (S Eg T T' W0 : Subgroup G)
    (ι : Elem2 6 →* G) : Prop where
  core : HarCoreData t z S Eg T T' W0
  z_sq : z ^ 2 = 1
  isPGroup_S : IsPGroup 2 S
  card_S : Nat.card S = 2 ^ 11
  card_H : Nat.card (centralizer ({t} : Set G)) = 2 ^ 11 * 3 ^ 2 * 5 ^ 3 * 7 * 11
  inv_E : ∀ u ∈ Eg, u ^ 2 = 1 → u ≠ 1 → u ≠ t →
    ∃ h ∈ centralizer ({t} : Set G), h * u * h⁻¹ = z ∨ h * u * h⁻¹ = t * z
  inv_outer : ∀ p ∈ centralizer ({t} : Set G), p ^ 2 = 1 → p ∉ Eg →
    ∃ h ∈ centralizer ({t} : Set G), h * p * h⁻¹ = b ∨ h * p * h⁻¹ = z₁
  injective_ι : Function.Injective ι
  ι_tv : coordElt ι tv = t
  coords_z : ∃ v : V6, coordElt ι v = z ∧ lam v = 0 ∧ qm v = 0
  coords_b : ∃ v : V6, coordElt ι v = b ∧ lam v = 1 ∧ qm v = 1
  coords_z₁ : ∃ v : V6, coordElt ι v = z₁ ∧ lam v = 1 ∧ qm v = 0
  mem_E_iff : ∀ v : V6, coordElt ι v ∈ Eg ↔ lam v = 0
  conj_E64 : ∀ B : Subgroup G, B ≤ centralizer ({t} : Set G) → Nat.card B = 64 →
    CFSG.Open.IsElemAbelian 2 B → ∃ h ∈ centralizer ({t} : Set G),
      B = ι.range.map (MulAut.conj h).toMonoidHom
  centralizer_le : centralizer (ι.range : Set G) ≤ ι.range
  card_NH : Nat.card ↥(normalizer (ι.range : Set G) ⊓ centralizer ({t} : Set G)) = 46080
  fuse : ∀ v w : V6, v ≠ 0 → v ≠ tv → w ≠ 0 → w ≠ tv → lam v = lam w → qm v = qm w →
    ∃ n ∈ normalizer (ι.range : Set G) ⊓ centralizer ({t} : Set G),
      n * coordElt ι v * n⁻¹ = coordElt ι w

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}

theorem HData.t_sq (hD : HData G t z b z₁ S Eg T T' W0 ι) : t ^ 2 = 1 := hD.core.t_sq

theorem HData.S_le_centralizer (hD : HData G t z b z₁ S Eg T T' W0 ι) :
    S ≤ centralizer ({t} : Set G) := fun s hs =>
  mem_centralizer_singleton_iff.mpr (hD.core.S_comm_t s hs)

theorem HData.orderOf_t (hD : HData G t z b z₁ S Eg T T' W0 ι) : orderOf t = 2 :=
  orderOf_eq_prime hD.core.t_sq hD.core.t_ne_one

end CFSG.EvenSporadicStandard.HNRecog.Harada
