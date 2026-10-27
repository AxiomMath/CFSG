module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S2Odd

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Orbit

variable {T X : Type} [Group T] [Finite T] [Group X] [Finite X]

@[expose] def coverOrbit (κ : T →* X) (y : T) : Set T :=
  {w : T | ∃ g : T, κ g ∈ centralizer ({κ y} : Set X) ∧ w = g * y * g⁻¹}

theorem card_comap_centralizer_eq (κ : T →* X) (y : T) :
    Nat.card ↥((centralizer ({κ y} : Set X)).comap κ) =
      (coverOrbit κ y).ncard * Nat.card ↥(centralizer ({y} : Set T)) := by
  set Γ : Subgroup T := (centralizer ({κ y} : Set X)).comap κ with hΓ
  set D : Subgroup T := centralizer ({y} : Set T) with hD
  have hDΓ : D ≤ Γ := by
    intro g hg
    rw [hD, mem_centralizer_singleton_iff] at hg
    show κ g ∈ centralizer ({κ y} : Set X)
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg]
  set D' : Subgroup ↥Γ := D.subgroupOf Γ with hD'
  let f : ↥Γ → T := fun g => (g : T) * y * (g : T)⁻¹
  have hf : ∀ a b : ↥Γ, f a = f b ↔ a⁻¹ * b ∈ D' := by
    intro a b
    constructor
    · intro h
      show ((a⁻¹ * b : ↥Γ) : T) ∈ D
      rw [hD, mem_centralizer_singleton_iff]
      have h' : (a : T) * y * (a : T)⁻¹ = (b : T) * y * (b : T)⁻¹ := h
      show (a : T)⁻¹ * (b : T) * y = y * ((a : T)⁻¹ * (b : T))
      calc (a : T)⁻¹ * (b : T) * y = (a : T)⁻¹ * ((b : T) * y * (b : T)⁻¹) * (b : T) := by group
        _ = (a : T)⁻¹ * ((a : T) * y * (a : T)⁻¹) * (b : T) := by rw [h']
        _ = y * ((a : T)⁻¹ * (b : T)) := by group
    · intro h
      have h1 : ((a⁻¹ * b : ↥Γ) : T) ∈ D := h
      rw [hD, mem_centralizer_singleton_iff] at h1
      have h2 : (a : T)⁻¹ * (b : T) * y = y * ((a : T)⁻¹ * (b : T)) := h1
      show (a : T) * y * (a : T)⁻¹ = (b : T) * y * (b : T)⁻¹
      calc (a : T) * y * (a : T)⁻¹ = (b : T) * (((a : T)⁻¹ * (b : T))⁻¹ * y *
            ((a : T)⁻¹ * (b : T))) * (b : T)⁻¹ := by group
        _ = (b : T) * y * (b : T)⁻¹ := by
          have : ((a : T)⁻¹ * (b : T))⁻¹ * y * ((a : T)⁻¹ * (b : T)) = y := by
            calc ((a : T)⁻¹ * (b : T))⁻¹ * y * ((a : T)⁻¹ * (b : T))
                = ((a : T)⁻¹ * (b : T))⁻¹ * (y * ((a : T)⁻¹ * (b : T))) := by group
              _ = ((a : T)⁻¹ * (b : T))⁻¹ * ((a : T)⁻¹ * (b : T) * y) := by rw [h2]
              _ = y := by group
          rw [this]
  let ν : ↥Γ ⧸ D' → T := fun q => Quotient.liftOn' q f (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab
    exact (hf a b).2 hab)
  have hν : Function.Injective ν := by
    intro p q
    induction p using Quotient.inductionOn' with
    | h a =>
      induction q using Quotient.inductionOn' with
      | h b =>
        intro h
        have h' : f a = f b := h
        exact Quotient.sound' (by rw [QuotientGroup.leftRel_apply]; exact (hf a b).1 h')
  have hrange : Set.range ν = coverOrbit κ y := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Quotient.inductionOn' with
      | h a => exact ⟨(a : T), a.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨Quotient.mk'' ⟨g, hg⟩, rfl⟩
  have h1 : Nat.card (↥Γ ⧸ D') = (coverOrbit κ y).ncard := by
    rw [← hrange, ← Nat.card_coe_set_eq]
    exact (Nat.card_range_of_injective hν).symm
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup D'
  have h3 : Nat.card ↥D' = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDΓ).toEquiv
  rw [h2, h1, h3]

theorem card_centralizer_le_orbit_mul (κ : T →* X) (hκ : Function.Surjective κ) (y : T) :
    Nat.card ↥(centralizer ({κ y} : Set X)) ≤
      (coverOrbit κ y).ncard * Nat.card ↥((centralizer ({y} : Set T)).map κ) := by
  have h1 := natCard_comap_of_surjective' κ hκ (centralizer ({κ y} : Set X))
  have h2 := card_comap_centralizer_eq κ y
  let r : ↥(centralizer ({y} : Set T)) →* X := κ.comp (centralizer ({y} : Set T)).subtype
  have hr : r.range = (centralizer ({y} : Set T)).map κ := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup r.ker
  have h4 : Nat.card (↥(centralizer ({y} : Set T)) ⧸ r.ker) = Nat.card ↥((centralizer ({y} : Set T)).map κ) := by
    rw [← hr]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv
  have h5 : Nat.card ↥r.ker ≤ Nat.card ↥κ.ker := by
    refine Nat.card_le_card_of_injective (fun g => ⟨(g.1 : T), g.2⟩) ?_
    intro a b hab
    have h2 : (a.1.1 : T) = b.1.1 := congrArg (fun z : ↥κ.ker => (z : T)) hab
    exact Subtype.ext (Subtype.ext h2)
  have hkpos : 0 < Nat.card ↥κ.ker := Nat.card_pos
  have key : Nat.card ↥κ.ker * Nat.card ↥(centralizer ({κ y} : Set X)) ≤
      Nat.card ↥κ.ker * ((coverOrbit κ y).ncard * Nat.card ↥((centralizer ({y} : Set T)).map κ)) := by
    rw [← h1, h2, h3, h4]
    calc (coverOrbit κ y).ncard * (Nat.card ↥((centralizer ({y} : Set T)).map κ) * Nat.card ↥r.ker)
        = (coverOrbit κ y).ncard * Nat.card ↥((centralizer ({y} : Set T)).map κ) * Nat.card ↥r.ker := by ring
      _ ≤ (coverOrbit κ y).ncard * Nat.card ↥((centralizer ({y} : Set T)).map κ) * Nat.card ↥κ.ker :=
          Nat.mul_le_mul_left _ h5
      _ = Nat.card ↥κ.ker * ((coverOrbit κ y).ncard * Nat.card ↥((centralizer ({y} : Set T)).map κ)) := by ring
  exact Nat.le_of_mul_le_mul_left key hkpos

end Orbit

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
