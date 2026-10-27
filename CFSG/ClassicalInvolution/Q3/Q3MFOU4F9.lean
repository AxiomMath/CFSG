module

public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSU3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOU4

open CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Q3.Q3PP

abbrev F3 : Type := GaloisField 3 1

noncomputable abbrev σ9 : F9 ≃+* F9 := unitaryInvolution F9 3 1

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem three_eq_zero_F9 : (3 : F9) = 0 := by
  have : CharP F9 3 := inferInstance
  exact_mod_cast CharP.cast_eq_zero F9 3

theorem σ9_apply (c : F9) : σ9 c = c ^ 3 := by
  rw [unitaryInvolution_apply]
  simp

theorem eq_of_σ9_fixed {c : F9} (h : σ9 c = c) : c = 0 ∨ c = 1 ∨ c = -1 := by
  rw [σ9_apply] at h
  have h3 : c * (c - 1) * (c + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact Or.inl h5
    · exact Or.inr (Or.inl (sub_eq_zero.mp h5))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h4))

theorem σ9_σ9 (c : F9) : σ9 (σ9 c) = c := unitaryInvolution_involutive card_F9 c

theorem isUnitaryInvolution_σ9 : IsUnitaryInvolution σ9 :=
  isUnitaryInvolution_unitaryInvolution card_F9

theorem exists_iota : ∃ ι : F9, ι * ι = -1 ∧ σ9 ι = -ι := by
  obtain ⟨c, hc0, hc⟩ := exists_unitaryInvolution_eq_neg (K := F9) (p := 3) (f := 1) card_F9
  have hc' : σ9 c = -c := hc
  have hcc : σ9 (c * c) = c * c := by
    rw [map_mul, hc']
    ring
  refine ⟨c, ?_, hc'⟩
  rcases eq_of_σ9_fixed hcc with h | h | h
  · exact absurd (mul_self_eq_zero.mp h) hc0
  · exfalso
    have h' : (c - 1) * (c + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · have h2 : c = 1 := sub_eq_zero.mp h1
      rw [h2, map_one] at hc'
      exact two_ne_zero_F9 (by linear_combination hc')
    · have h2 : c = -1 := eq_neg_of_add_eq_zero_left h1
      rw [h2, map_neg, map_one] at hc'
      exact two_ne_zero_F9 (by linear_combination -hc')
  · exact h

theorem exists_zeta : ∃ ζ : F9, σ9 ζ * ζ = -1 :=
  isUnitaryInvolution_σ9.exists_norm_neg_one

noncomputable def castF9 : ZMod 3 →+* F9 := ZMod.castHom (dvd_refl 3) F9

noncomputable def castF3 : ZMod 3 →+* F3 := ZMod.castHom (dvd_refl 3) F3

theorem castF3_bijective : Function.Bijective castF3 := by
  refine castF3.injective.bijective_of_nat_card_le ?_
  rw [natCard_gf3]
  simp

noncomputable def embF : F3 →+* F9 :=
  castF9.comp (RingEquiv.ofBijective castF3 castF3_bijective).symm.toRingHom

theorem embF_injective : Function.Injective embF := embF.injective

theorem σ9_embF (c : F3) : σ9 (embF c) = embF c := by
  rw [σ9_apply, ← map_pow]
  congr 1
  have : Fintype F3 := Fintype.ofFinite F3
  have hc : Fintype.card F3 = 3 := by rw [← Nat.card_eq_fintype_card]; exact natCard_gf3
  have := FiniteField.pow_card c
  rwa [hc] at this

theorem exists_embF {c : F9} (h : σ9 c = c) : ∃ c' : F3, embF c' = c := by
  rcases eq_of_σ9_fixed h with rfl | rfl | rfl
  · exact ⟨0, map_zero _⟩
  · exact ⟨1, map_one _⟩
  · exact ⟨-1, map_neg _ _ |>.trans (by rw [map_one])⟩

end CFSG.ClassicalInvolution.Q3.Q3MFOU4
