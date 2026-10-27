module

public import CFSG.LocalAnalysis.Asc75.Basic

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

@[expose] def FixedOnly (H X : Subgroup G) : Prop :=
  X ≤ H ∧ ∀ g : G, conjugate X g ≤ H → g ∈ H

theorem fixedOnly_iff {H X : Subgroup G} :
    FixedOnly H X ↔ X ≤ H ∧ Subgroup.normalizer (X : Set G) ≤ H ∧
      ∀ g : G, conjugate X g ≤ H → ∃ h ∈ H, conjugate X g = conjugate X h := by
  constructor
  · rintro ⟨hXH, hfix⟩
    refine ⟨hXH, fun n hn => hfix n ?_, fun g hg => ⟨g, hfix g hg, rfl⟩⟩
    rw [conjugate_of_mem_normalizer hn]
    exact hXH
  · rintro ⟨hXH, hN, hfus⟩
    refine ⟨hXH, fun g hg => ?_⟩
    obtain ⟨h, hh, hgh⟩ := hfus g hg
    have hn : g * h⁻¹ ∈ Subgroup.normalizer (X : Set G) := by
      refine mem_normalizer_of_conjugate_eq ?_
      rw [conjugate_mul, hgh, conjugate_inv_conjugate]
    have := hN hn
    have e : g = (g * h⁻¹) * h := by group
    rw [e]
    exact H.mul_mem this hh

theorem FixedOnly.le {H X : Subgroup G} (h : FixedOnly H X) : X ≤ H := h.1

theorem FixedOnly.mono {H X X' : Subgroup G} (h : FixedOnly H X') (hX' : X' ≤ X) (hXH : X ≤ H) :
    FixedOnly H X :=
  ⟨hXH, fun g hg => h.2 g ((conjugate_mono hX' g).trans hg)⟩

@[expose] def FixedOnlyElt (H : Subgroup G) (a : G) : Prop :=
  a ∈ H ∧ ∀ g : G, g⁻¹ * a * g ∈ H → g ∈ H

theorem fixedOnlyElt_iff_zpowers {H : Subgroup G} {a : G} :
    FixedOnlyElt H a ↔ FixedOnly H (Subgroup.zpowers a) := by
  have key : ∀ g : G, conjugate (Subgroup.zpowers a) g ≤ H ↔ g⁻¹ * a * g ∈ H := by
    intro g
    constructor
    · intro h
      have : g⁻¹ * a * g ∈ conjugate (Subgroup.zpowers a) g := conj_mem_conjugate (Subgroup.mem_zpowers a) g
      exact h this
    · intro h x hx
      rw [mem_conjugate_iff] at hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      have : x = (g⁻¹ * a * g) ^ k := by
        have e : (g⁻¹ * a * g) ^ k = g⁻¹ * a ^ k * g := by
          simpa using (conj_zpow (a := g⁻¹) (b := a) (i := k))
        rw [e, hk]; group
      rw [this]
      exact H.zpow_mem h k
  constructor
  · rintro ⟨ha, hfix⟩
    exact ⟨(Subgroup.zpowers_le).2 ha, fun g hg => hfix g ((key g).1 hg)⟩
  · rintro ⟨hle, hfix⟩
    exact ⟨hle (Subgroup.mem_zpowers a), fun g hg => hfix g ((key g).2 hg)⟩

end CFSG.Asc75
