module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma39

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {Y Z : Type} [Group Y] [Group Z] (f : Y ≃* Z) {KY : Subgroup Y} {KZ : Subgroup Z}
  {uY : Y}

theorem fi24in_mem_iff_of_map_eq (hK : KY.map f.toMonoidHom = KZ) {y : Y} :
    f y ∈ KZ ↔ y ∈ KY := by
  rw [← hK, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem fi24in_mem_vCandidates_equiv (hK : KY.map f.toMonoidHom = KZ) {v : Y} :
    f v ∈ vCandidates KZ (f uY) ↔ v ∈ vCandidates KY uY := by
  have hsup : (KY ⊔ zpowers uY).map f.toMonoidHom = KZ ⊔ zpowers (f uY) := by
    rw [Subgroup.map_sup, hK, MonoidHom.map_zpowers]
    rfl
  have h1 : f v ∈ KZ ⊔ zpowers (f uY) ↔ v ∈ KY ⊔ zpowers uY := by
    rw [← hsup, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have h2 : f v ∈ (center KZ).map KZ.subtype ↔ v ∈ (center KY).map KY.subtype := by
    rw [mem_center_map_iff, mem_center_map_iff, fi24in_mem_iff_of_map_eq f hK]
    refine and_congr Iff.rfl ⟨fun h k hk => ?_, fun h k hk => ?_⟩
    · have := h (f k) ((fi24in_mem_iff_of_map_eq f hK).2 hk)
      rw [← map_mul, ← map_mul] at this
      exact f.injective this
    · obtain ⟨k', rfl⟩ := f.surjective k
      rw [← map_mul, ← map_mul, h k' ((fi24in_mem_iff_of_map_eq f hK).1 hk)]
  have h3 : orderOf (f v) = orderOf v := orderOf_injective f.toMonoidHom f.injective v
  exact and_congr h1 (and_congr (not_congr h2) (by rw [h3]))

theorem fi24in_twoAdic_inf_centralizer_equiv (hK : KY.map f.toMonoidHom = KZ) (v : Y) :
    twoAdic (KZ ⊓ centralizer ({f v} : Set Z)) = twoAdic (KY ⊓ centralizer ({v} : Set Y)) := by
  have hmap : (KY ⊓ centralizer ({v} : Set Y)).map f.toMonoidHom =
      KZ ⊓ centralizer ({f v} : Set Z) := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [← hK]
        exact ⟨_, h1, by simp⟩
      · have := congrArg f h2
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
        exact this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · exact (fi24in_mem_iff_of_map_eq f hK).1 (by simpa using h1)
      · apply f.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact h2
  unfold twoAdic
  rw [← hmap, Subgroup.card_map_of_injective f.injective]

theorem fi24in_mem_vMaximal_equiv (hK : KY.map f.toMonoidHom = KZ) {v : Y} :
    f v ∈ vMaximal KZ (f uY) ↔ v ∈ vMaximal KY uY := by
  constructor
  · rintro ⟨hv, hmax⟩
    refine ⟨(fi24in_mem_vCandidates_equiv f hK).1 hv, fun v' hv' => ?_⟩
    have := hmax (f v') ((fi24in_mem_vCandidates_equiv f hK).2 hv')
    rwa [fi24in_twoAdic_inf_centralizer_equiv f hK, fi24in_twoAdic_inf_centralizer_equiv f hK]
      at this
  · rintro ⟨hv, hmax⟩
    refine ⟨(fi24in_mem_vCandidates_equiv f hK).2 hv, fun v'' hv'' => ?_⟩
    obtain ⟨v', rfl⟩ := f.surjective v''
    have := hmax v' ((fi24in_mem_vCandidates_equiv f hK).1 hv'')
    rwa [fi24in_twoAdic_inf_centralizer_equiv f hK, fi24in_twoAdic_inf_centralizer_equiv f hK]

theorem fi24in_mem_vPairs_equiv (hK : KY.map f.toMonoidHom = KZ) {w : Y} :
    f w ∈ vPairs (⊤ : Subgroup Z) KZ (f uY) ↔ w ∈ vPairs (⊤ : Subgroup Y) KY uY := by
  constructor
  · rintro ⟨v'', hv'', hw, l, -, hl⟩
    obtain ⟨v, rfl⟩ := f.surjective v''
    refine ⟨v, (fi24in_mem_vMaximal_equiv f hK).1 hv'', f.injective (by rw [hw, map_mul]),
      f.symm l, Subgroup.mem_top _, f.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hl]
  · rintro ⟨v, hv, hw, l, -, hl⟩
    refine ⟨f v, (fi24in_mem_vMaximal_equiv f hK).2 hv, by rw [hw, map_mul], f l,
      Subgroup.mem_top _, ?_⟩
    rw [← hl, map_mul, map_mul, map_inv]

theorem fi24in_vPairs_nonempty_of_equiv (hK : KY.map f.toMonoidHom = KZ)
    (h : (vPairs (⊤ : Subgroup Z) KZ (f uY)).Nonempty) :
    (vPairs (⊤ : Subgroup Y) KY uY).Nonempty := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', rfl⟩ := f.surjective w
  exact ⟨w', (fi24in_mem_vPairs_equiv f hK).1 hw⟩

theorem fi24in_sol78Generate_of_equiv (hK : KY.map f.toMonoidHom = KZ)
    (h : Sol78Generate (⊤ : Subgroup Z) KZ (f uY)) : Sol78Generate (⊤ : Subgroup Y) KY uY := by
  intro l _ hl
  have hl' : f (l * uY * l⁻¹) ∈ vPairs (⊤ : Subgroup Z) KZ (f uY) :=
    (fi24in_mem_vPairs_equiv f hK).2 hl
  rw [map_mul, map_mul, map_inv] at hl'
  have hgen := h (f l) (Subgroup.mem_top _) hl'
  have hcomm : f.toMonoidHom.comp (conjHom l) = (conjHom (f l)).comp f.toMonoidHom := by
    ext x
    simp
  have himg : (KY ⊔ KY.map (conjHom l)).map f.toMonoidHom = KZ ⊔ KZ.map (conjHom (f l)) := by
    rw [Subgroup.map_sup, hK, Subgroup.map_map, hcomm, ← Subgroup.map_map, hK]
  rw [eq_top_iff]
  intro y _
  have : f y ∈ (KY ⊔ KY.map (conjHom l)).map f.toMonoidHom := by
    rw [himg, hgen]
    exact Subgroup.mem_top _
  rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this

end CFSG.EvenSporadicStandard.Induction
