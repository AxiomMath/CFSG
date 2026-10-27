module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG.LocalAnalysis.ComponentInitial

variable {q : ℕ} {F : Type} [Field F] [Finite F]

theorem uniDesc_exists_fieldData (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) :
    ∃ (p f : ℕ) (_ : UnitaryFieldData p f F), p ^ f = q ∧ (2 : F) ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hpn⟩ := FiniteField.card F (ringChar F)
  have hqdvd : q ∣ ringChar F ^ (n : ℕ) := by
    rw [← hpn, ← Nat.card_eq_fintype_card, hF]
    exact Dvd.intro_left q (by ring)
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hqdvd
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : Nat.card F = 1 := by rw [hF, hf]; simp
    exact absurd this (Nat.ne_of_gt Finite.one_lt_card)
  have hcard : Nat.card F = ringChar F ^ (2 * f) := by
    rw [hF, hf, pow_mul']
  refine ⟨ringChar F, f, ⟨hp, Nat.one_le_iff_ne_zero.2 hf0, hcard⟩, hf.symm, ?_⟩
  intro h2
  have hp2 : ringChar F ∣ 2 := by
    have : ((2 : ℕ) : F) = 0 := by simpa using h2
    exact (CharP.cast_eq_zero_iff F (ringChar F) 2).1 this
  have hpe : ringChar F = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2
  rw [hpe] at hf
  have heven : Even q := by
    rw [hf]
    exact (Nat.even_pow.2 ⟨even_two, hf0⟩)
  have : q % 2 = 0 := Nat.even_iff.1 heven
  omega

theorem uniDesc_field_facts (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (bar : F →+* F)
    (hbar : ∀ x, bar x = x ^ q) :
    (∀ x, bar (bar x) = x) ∧ (2 : F) ≠ 0 ∧ (∃ δ : F, δ ≠ 0 ∧ bar δ = -δ) ∧
      Nat.card (bar.eqLocusField (RingHom.id F)) = q := by
  obtain ⟨p, f, h, hpf, h2⟩ := uniDesc_exists_fieldData hF hq
  have hb : h.bar = bar := RingHom.ext fun x => by rw [h.bar_apply, hpf, hbar]
  refine ⟨fun x => ?_, h2, ?_, ?_⟩
  · rw [← hb]; exact h.bar_bar x
  · obtain ⟨c, hc⟩ := h.exists_bar_ne
    rw [hb] at hc
    refine ⟨bar c - c, sub_ne_zero.2 hc, ?_⟩
    have : bar (bar c) = c := by rw [← hb]; exact h.bar_bar c
    rw [map_sub, this]; ring
  · have h1 : h.fixedField = bar.eqLocusField (RingHom.id F) := by
      unfold UnitaryFieldData.fixedField
      rw [hb]
    rw [← h1, h.card_fixedField, hpf]

end CFSG.GH74.Generic.S1.Exo
