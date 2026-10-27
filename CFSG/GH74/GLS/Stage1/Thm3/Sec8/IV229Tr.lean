module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229Fin
public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.KGroups

theorem exists_ringEquiv : Nonempty (F16 ≃+* GF16) := by
  classical
  let _ : Fintype F16 := Fintype.ofFinite F16
  have h1 : Fintype.card F16 = 16 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 4 (by norm_num)
  have h2 : Fintype.card GF16 = 16 := by decide +kernel
  exact ⟨FiniteField.ringEquivOfCardEq (h1.trans h2.symm)⟩


section Transport

variable (e : F16 ≃+* GF16)

include e in
theorem F16_trace_surj_of (a : F16) : ∃ b : F16, b + bar b + a * bar a = 0 := by
  obtain ⟨b', hb'⟩ := gf16_trace_surj (e a)
  refine ⟨e.symm b', e.injective ?_⟩
  simp only [map_add, map_mul, bar_apply, map_pow, RingEquiv.apply_symm_apply, map_zero]
  exact hb'

include e in
theorem F16_norm_surj_of (b : F16) (hb : b + bar b = 0) : ∃ a : F16, a * bar a = b := by
  have hb' : e b + e b ^ 4 = 0 := by
    have := congrArg e hb
    simpa only [map_add, bar_apply, map_pow, map_zero] using this
  obtain ⟨a', ha'⟩ := gf16_norm_surj (e b) hb'
  refine ⟨e.symm a', e.injective ?_⟩
  simp only [map_mul, bar_apply, map_pow, RingEquiv.apply_symm_apply]
  exact ha'

include e in
theorem F16_no_pair_of (L₁ L₂ : F16 → F16) (hf₁ : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hf₂ : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hg₁ : ∀ a b, a * bar a = b * bar b → L₁ a * bar (L₁ a) = L₁ b * bar (L₁ b))
    (hg₂ : ∀ a b, a * bar a = b * bar b → L₂ a * bar (L₂ a) = L₂ b * bar (L₂ b))
    (hne : ∃ a, L₁ a ≠ a) (ho₁ : ∀ a, L₁ (L₁ (L₁ a)) = a) (ho₂ : ∀ a, L₂ (L₂ a) = a)
    (hrel : ∀ a, L₁ (L₂ (L₁ a)) = L₂ a) : False := by
  have hn : ∀ x : F16, e (x * bar x) = e x * e x ^ 4 := fun x => by
    simp only [map_mul, bar_apply, map_pow]
  refine gf16_no_pair (fun x => e (L₁ (e.symm x))) (fun x => e (L₂ (e.symm x)))
    (fun a b => by simp only [map_add, hf₁])
    (fun a b => by simp only [map_add, hf₂])
    (fun a b h => ?_) (fun a b h => ?_) ?_ (fun a => by simp [ho₁]) (fun a => by simp [ho₂])
    (fun a => by simp [hrel])
  · have h' : e.symm a * bar (e.symm a) = e.symm b * bar (e.symm b) := by
      apply e.injective
      rw [hn, hn]
      simpa using h
    have := congrArg e (hg₁ _ _ h')
    rw [hn, hn] at this
    exact this
  · have h' : e.symm a * bar (e.symm a) = e.symm b * bar (e.symm b) := by
      apply e.injective
      rw [hn, hn]
      simpa using h
    have := congrArg e (hg₂ _ _ h')
    rw [hn, hn] at this
    exact this
  · obtain ⟨a, ha⟩ := hne
    refine ⟨e a, fun h => ha ?_⟩
    simpa using e.injective (by simpa using h)

end Transport

theorem F16_trace_surj (a : F16) : ∃ b : F16, b + bar b + a * bar a = 0 := by
  obtain ⟨e⟩ := exists_ringEquiv
  exact F16_trace_surj_of e a

theorem F16_norm_surj (b : F16) (hb : b + bar b = 0) : ∃ a : F16, a * bar a = b := by
  obtain ⟨e⟩ := exists_ringEquiv
  exact F16_norm_surj_of e b hb

theorem F16_no_pair (L₁ L₂ : F16 → F16) (hf₁ : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hf₂ : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hg₁ : ∀ a b, a * bar a = b * bar b → L₁ a * bar (L₁ a) = L₁ b * bar (L₁ b))
    (hg₂ : ∀ a b, a * bar a = b * bar b → L₂ a * bar (L₂ a) = L₂ b * bar (L₂ b))
    (hne : ∃ a, L₁ a ≠ a) (ho₁ : ∀ a, L₁ (L₁ (L₁ a)) = a) (ho₂ : ∀ a, L₂ (L₂ a) = a)
    (hrel : ∀ a, L₁ (L₂ (L₁ a)) = L₂ a) : False := by
  obtain ⟨e⟩ := exists_ringEquiv
  exact F16_no_pair_of e L₁ L₂ hf₁ hf₂ hg₁ hg₂ hne ho₁ ho₂ hrel

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.IV229
