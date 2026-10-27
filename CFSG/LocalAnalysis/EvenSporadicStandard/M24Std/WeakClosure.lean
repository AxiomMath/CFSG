module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

theorem weaklyClosed_of_relIndex_lt {G : Type*} [Group G] [Finite G] {R C : Subgroup G}
    (hCab : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c) (hC2 : ∀ c ∈ C, c * c = 1)
    (hbig : ∀ D : Subgroup G, D ≤ R → (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
      (∀ x ∈ D, x * x = 1) → ¬ D ≤ C → Nat.card D = Nat.card C →
      ∃ d ∈ D, d ∉ C ∧ C.relIndex D < (centralizer ({d} : Set G)).relIndex C) :
    ∀ g : G, C.map (MulAut.conj g).toMonoidHom ≤ R → C.map (MulAut.conj g).toMonoidHom = C := by
  intro g hg
  by_contra hne
  set D := C.map (MulAut.conj g).toMonoidHom with hD
  have hcard : Nat.card D = Nat.card C :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hCab a ha b hb]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  have hD2 : ∀ x ∈ D, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    show g * a * g⁻¹ * (g * a * g⁻¹) = 1
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hC2 a ha]; group
  have hDC : ¬ D ≤ C := fun h => hne (Subgroup.eq_of_le_of_card_ge h (le_of_eq hcard.symm))
  obtain ⟨d, hdD, hdC, hlt⟩ := hbig D hg hDab hD2 hDC hcard
  have hle : D ⊓ C ≤ centralizer ({d} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (hDab d hdD x hx.1).symm
  have hne0 : (D ⊓ C).relIndex C ≠ 0 := by
    show ((D ⊓ C).subgroupOf C).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have h1 : (centralizer ({d} : Set G)).relIndex C ≤ D.relIndex C := by
    rw [← Subgroup.inf_relIndex_right D C]
    exact Subgroup.relIndex_le_of_le_left hle hne0
  have h3 : C.relIndex D = D.relIndex C := by
    have e1 := Subgroup.relIndex_mul_card (H := D) (K := C)
    have e2 := Subgroup.relIndex_mul_card (H := C) (K := D)
    rw [inf_comm] at e2
    rw [← hcard] at e1
    have hpos : 0 < Nat.card (D ⊓ C : Subgroup G) := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)).symm
  omega

theorem exists_sylow_eq_of_weaklyClosed {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {C R : Subgroup G} (hR : IsPGroup p R) (hRN : R ≤ normalizer (C : Set G))
    (hmax : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ normalizer (C : Set G) → R ≤ Q → Q ≤ R)
    (hwc : ∀ g : G, C.map (MulAut.conj g).toMonoidHom ≤ R →
      C.map (MulAut.conj g).toMonoidHom = C) (hCR : C ≤ R) :
    ∃ P : Sylow p G, (P : Subgroup G) = R := by
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hRP⟩
  by_contra hPR
  have hlt : R.subgroupOf (P : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact hPR
  have : Group.IsNilpotent (P : Subgroup G) := P.isPGroup'.isNilpotent
  have hnc : NormalizerCondition (P : Subgroup G) := Group.normalizerCondition_of_isNilpotent
  obtain ⟨-, hnle⟩ := lt_iff_le_not_ge.1 (hnc _ hlt)
  obtain ⟨x, hx, hxR⟩ := Set.not_subset.1 hnle
  have hnR : (x : G) ∉ R := fun h => hxR (mem_subgroupOf.2 h)
  have hnorm : ∀ y ∈ R, (x : G) * y * (x : G)⁻¹ ∈ R := fun y hy => by
    have h1 := (mem_normalizer_iff.1 hx ⟨y, hRP hy⟩).1 (mem_subgroupOf.2 hy)
    exact mem_subgroupOf.1 h1
  have hCn : C.map (MulAut.conj (x : G)).toMonoidHom ≤ R := by
    rintro _ ⟨c, hc, rfl⟩
    exact hnorm c (hCR hc)
  have hCeq := hwc _ hCn
  have hnN : (x : G) ∈ normalizer (C : Set G) :=
    mem_normalizer_iff_map_conj_eq.2 hCeq
  have hQP : R ⊔ zpowers (x : G) ≤ (P : Subgroup G) :=
    sup_le hRP (zpowers_le.2 x.2)
  have hQ := hmax (R ⊔ zpowers (x : G)) (P.isPGroup'.to_le hQP)
    (sup_le hRN (zpowers_le.2 hnN)) le_sup_left
  exact hnR (hQ (mem_sup_right (mem_zpowers _)))

end CFSG.EvenSporadicStandard.M24Std
