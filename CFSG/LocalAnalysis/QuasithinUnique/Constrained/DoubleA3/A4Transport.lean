module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Block

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G H : Type} [Group G] [Group H]

theorem IsA4Block.map_of_injective {L U : Subgroup G} (h : IsA4Block L U) (f : G →* H)
    (hf : Function.Injective f) : IsA4Block (L.map f) (U.map f) := by
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := h.exists_c
  refine ⟨?_, ?_, ?_, ?_, ?_, f c, ⟨c, hcL, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf]; exact h.card_U
  · rintro _ ⟨u, hu, rfl⟩
    show (f u) ^ 2 = 1
    rw [← map_pow, h.sq_U u hu, map_one]
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    show f u * f v = f v * f u
    rw [← map_mul, ← map_mul, h.comm_U u hu v hv]
  · rw [Subgroup.card_map_of_injective hf]; exact h.card_L
  · rintro _ ⟨g, hg, rfl⟩ hcomm
    have hg1 : g = 1 := h.center_L g hg (fun l hl => hf (by
      have := hcomm (f l) ⟨l, hl, rfl⟩
      simpa [map_mul] using this))
    simp [hg1]
  · rw [← hc3]
    exact orderOf_injective f hf c
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨c * u * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN u).mp hu, ?_⟩
      simp [map_mul, map_inv]
    · rintro ⟨u, hu, hu'⟩
      refine ⟨c⁻¹ * u * c, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp ((normalizer (U : Set G)).inv_mem hcN) u).mp hu
        simpa using this
      · calc f (c⁻¹ * u * c) = (f c)⁻¹ * f u * f c := by simp [map_mul, map_inv]
          _ = y := by rw [hu']; group
  · rintro _ ⟨u, hu, rfl⟩ hu1 heq
    refine hcfp u hu (fun h1 => hu1 (by simp [h1])) (hf ?_)
    simpa [map_mul, map_inv] using heq
  · conv_lhs => rw [hLc]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]

theorem IsA4Block.of_map_injective {L U : Subgroup G} (f : G →* H) (hf : Function.Injective f)
    (h : IsA4Block (L.map f) (U.map f)) : IsA4Block L U := by
  obtain ⟨c', hc'L, hc3, hc'N, hc'fp, hLc⟩ := h.exists_c
  obtain ⟨c, hcL, rfl⟩ := hc'L
  refine ⟨?_, ?_, ?_, ?_, ?_, c, hcL, ?_, ?_, ?_, ?_⟩
  · have := h.card_U
    rwa [Subgroup.card_map_of_injective hf] at this
  · intro u hu
    apply hf
    rw [map_pow, map_one]
    exact h.sq_U (f u) ⟨u, hu, rfl⟩
  · intro u hu v hv
    apply hf
    rw [map_mul, map_mul]
    exact h.comm_U (f u) ⟨u, hu, rfl⟩ (f v) ⟨v, hv, rfl⟩
  · have := h.card_L
    rwa [Subgroup.card_map_of_injective hf] at this
  · intro g hg hcomm
    apply hf
    rw [map_one]
    refine h.center_L (f g) ⟨g, hg, rfl⟩ ?_
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, hcomm l hl]
  · rw [← hc3]
    exact (orderOf_injective f hf c).symm
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp hc'N (f y)
    have e : f c * f y * (f c)⁻¹ = f (c * y * c⁻¹) := by simp [map_mul, map_inv]
    rw [e, Subgroup.mem_map_iff_mem hf, Subgroup.mem_map_iff_mem hf] at h1
    exact h1
  · intro u hu hu1 heq
    refine hc'fp (f u) ⟨u, hu, rfl⟩ (fun h1 => hu1 (hf (by rw [h1, map_one]))) ?_
    have : f (c * u * c⁻¹) = f u := congrArg f heq
    simpa [map_mul, map_inv] using this
  · apply Subgroup.map_injective hf
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    exact hLc

end CFSG.QuasithinUnique.DoubleA3
