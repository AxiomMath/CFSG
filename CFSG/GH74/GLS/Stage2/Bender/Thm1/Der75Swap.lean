module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.ConjV7
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Abstract

variable {Y : Type*} [Group Y] {L₁ L₂ : Subgroup Y}

theorem conj_mul_eq_iff (hne : L₁ ≠ L₂)
    (hd : ∀ g : Y, (conjugate L₁ g = L₁ ∧ conjugate L₂ g = L₂) ∨
      (conjugate L₁ g = L₂ ∧ conjugate L₂ g = L₁)) (g h : Y) :
    conjugate L₁ (g * h) = L₂ ↔ (conjugate L₁ g = L₂ ↔ ¬ conjugate L₁ h = L₂) := by
  rw [← CFSG.ComponentClassification.UnbalancedLayer.conjugate_conjugate]
  rcases hd g with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · rw [a1]
    simp [hne]
  · rw [a1]
    rcases hd h with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · simp [b1, b2, hne]
    · simp [b1, b2, hne]

theorem conj_inv_eq_iff (hne : L₁ ≠ L₂)
    (hd : ∀ g : Y, (conjugate L₁ g = L₁ ∧ conjugate L₂ g = L₂) ∨
      (conjugate L₁ g = L₂ ∧ conjugate L₂ g = L₁)) (g : Y) :
    conjugate L₁ g⁻¹ = L₂ ↔ conjugate L₁ g = L₂ := by
  have h := conj_mul_eq_iff hne hd g g⁻¹
  rw [mul_inv_cancel, CFSG.ComponentClassification.UnbalancedLayer.conjugate_one] at h
  have h' : ¬ (L₁ = L₂) := hne
  tauto

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem comps_dichotomy (hpair : Stage1Pair G z S q L₁ L₂) (g : CentralizerBar z) :
    (conjugate L₁ g = L₁ ∧ conjugate L₂ g = L₂) ∨ (conjugate L₁ g = L₂ ∧ conjugate L₂ g = L₁) := by
  have hc₁ : IsComponent L₁ := by
    have : L₁ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
      rw [hpair.comps]
      exact Set.mem_insert _ _
    exact this
  have hc₂ : IsComponent L₂ := by
    have : L₂ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
      rw [hpair.comps]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    exact this
  have e1 : conjugate L₁ g ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
    rw [← hpair.comps]
    exact CFSG.ComponentClassification.UnbalancedLayer.isComponent_conjugate hc₁ g
  have e2 : conjugate L₂ g ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
    rw [← hpair.comps]
    exact CFSG.ComponentClassification.UnbalancedLayer.isComponent_conjugate hc₂ g
  have hinj : conjugate L₁ g = conjugate L₂ g → L₁ = L₂ := fun h => by
    have := congrArg (fun K => conjugate K g⁻¹) h
    simpa [CFSG.ComponentClassification.UnbalancedLayer.conjugate_conjugate_inv] using this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at e1 e2
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · exact absurd (hinj (e1.trans e2.symm)) hpair.ne
  · exact Or.inl ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩
  · exact absurd (hinj (e1.trans e2.symm)) hpair.ne

theorem swaps_iff_conj (hpair : Stage1Pair G z S q L₁ L₂) {t : G} (ht : t ∈ Cen z) :
    Swaps z t L₁ L₂ ↔ conjugate L₁ (toBar z ⟨t, ht⟩) = L₂ := by
  constructor
  · rintro ⟨_, h1, _⟩
    exact h1
  · intro h
    refine ⟨ht, h, ?_⟩
    rcases comps_dichotomy hpair (toBar z ⟨t, ht⟩) with ⟨a1, -⟩ | ⟨-, a2⟩
    · exact absurd (a1.symm.trans h) hpair.ne
    · exact a2

theorem swaps_conj (hpair : Stage1Pair G z S q L₁ L₂) {t c : G} (hc : c ∈ Cen z)
    (hsw : Swaps z t L₁ L₂) : Swaps z (c * t * c⁻¹) L₁ L₂ := by
  obtain ⟨ht, h1, -⟩ := hsw
  have hct : c * t * c⁻¹ ∈ Cen z :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hc ht) (Subgroup.inv_mem _ hc)
  have hd := comps_dichotomy hpair
  rw [swaps_iff_conj hpair hct]
  have e : toBar z ⟨c * t * c⁻¹, hct⟩ =
      toBar z ⟨c, hc⟩ * toBar z ⟨t, ht⟩ * (toBar z ⟨c, hc⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e, conj_mul_eq_iff hpair.ne hd, conj_mul_eq_iff hpair.ne hd, conj_inv_eq_iff hpair.ne hd]
  tauto

theorem conjugate_L₁_of_mem_LBar (hpair : Stage1Pair G z S q L₁ L₂) {y : CentralizerBar z}
    (hy : y ∈ LBar z) : conjugate L₁ y = L₁ := by
  obtain ⟨hsup, hcomm, -⟩ := hpair.prod
  rw [← hsup] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hy
  rw [← CFSG.ComponentClassification.UnbalancedLayer.conjugate_conjugate, conjugate_self ha]
  ext x
  rw [mem_conjugate_iff]
  constructor
  · intro hx
    have h := hcomm (b * x * b⁻¹) hx b hb
    have h' : b * x = b * (b * x * b⁻¹) := by
      calc b * x = (b * x * b⁻¹) * b := by group
        _ = b * (b * x * b⁻¹) := h
    have h'' : x = b * x * b⁻¹ := mul_left_cancel h'
    rw [h'']
    exact hx
  · intro hx
    have h := hcomm x hx b hb
    have : b * x * b⁻¹ = x := by
      calc b * x * b⁻¹ = x * b * b⁻¹ := by rw [h]
        _ = x := by group
    rw [this]
    exact hx

theorem swaps_mul_LC (hpair : Stage1Pair G z S q L₁ L₂) {s l : G} (hs : Swaps z s L₁ L₂)
    (hl : l ∈ LC z) : Swaps z (s * l) L₁ L₂ := by
  obtain ⟨hsC, h1, -⟩ := hs
  have hlC : l ∈ Cen z := LC_le_Cen z hl
  have hslC : s * l ∈ Cen z := Subgroup.mul_mem _ hsC hlC
  have hlB : toBar z ⟨l, hlC⟩ ∈ LBar z := ⟨⟨l, hlC⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hfix := conjugate_L₁_of_mem_LBar hpair hlB
  rw [swaps_iff_conj hpair hslC]
  have e : toBar z ⟨s * l, hslC⟩ = toBar z ⟨s, hsC⟩ * toBar z ⟨l, hlC⟩ := by
    rw [← map_mul]
    rfl
  rw [e, conj_mul_eq_iff hpair.ne (comps_dichotomy hpair)]
  have hnl : ¬ conjugate L₁ (toBar z ⟨l, hlC⟩) = L₂ := by
    rw [hfix]
    exact hpair.ne
  tauto

theorem swaps_mul_of_not_swaps (hpair : Stage1Pair G z S q L₁ L₂) {a s : G} (ha : a ∈ Cen z)
    (hna : ¬ Swaps z a L₁ L₂) (hs : Swaps z s L₁ L₂) : Swaps z (a * s) L₁ L₂ := by
  obtain ⟨hsC, h1, -⟩ := hs
  have hasC : a * s ∈ Cen z := Subgroup.mul_mem _ ha hsC
  rw [swaps_iff_conj hpair ha] at hna
  rw [swaps_iff_conj hpair hasC]
  have e : toBar z ⟨a * s, hasC⟩ = toBar z ⟨a, ha⟩ * toBar z ⟨s, hsC⟩ := by
    rw [← map_mul]
    rfl
  rw [e, conj_mul_eq_iff hpair.ne (comps_dichotomy hpair)]
  tauto

theorem exists_swapper_not_mem (hpair : Stage1Pair G z S q L₁ L₂) (hSC : S ≤ Cen z) {K : Subgroup G}
    {a t₀ : G} (haS : a ∈ S) (haK : a ∉ K) (ht₀S : t₀ ∈ S) (ht₀ : Swaps z t₀ L₁ L₂) :
    ∃ s ∈ S, s ∉ K ∧ Swaps z s L₁ L₂ := by
  by_cases haw : Swaps z a L₁ L₂
  · exact ⟨a, haS, haK, haw⟩
  · by_cases ht₀K : t₀ ∈ K
    · refine ⟨a * t₀, S.mul_mem haS ht₀S, fun h => haK ?_,
        swaps_mul_of_not_swaps hpair (hSC haS) haw ht₀⟩
      have := K.mul_mem h (K.inv_mem ht₀K)
      simpa using this
    · exact ⟨t₀, ht₀S, ht₀K, ht₀⟩

end Concrete

end CFSG.GH74.GLS.Stage2.Bender.Thm1
