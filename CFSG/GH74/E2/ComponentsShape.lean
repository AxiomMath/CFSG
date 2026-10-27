module

public import CFSG.GH74.E2.ComponentsFacts
public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.E2.CompCerts
public import CFSG.GH74.Generic.ClassicalCerts
public import CFSG.GH74.Generic.Context
public import CFSG.GH74.Filter.Small.Wrappers
public import CFSG.GH74.Filter.Sporadic.All
public import CFSG.GH74.Filter.Monster.Main
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases

public section

namespace CFSG.GH74.E2

open Subgroup Blueprint CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def EvenLieRankFour : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    EvenLieType S → SectionalTwoRankLE S 4 →
      ShapeA5 S ∨ ShapeL27 S ∨ ShapeL28 S ∨ ShapeSz8 S ∨ LieModel S .PSL 2 2 4 ∨
        LieModel S .PSL 3 2 2 ∨ LieModel S .PSL 4 2 1 ∨ LieModel S .PSU 3 2 2 ∨
          LieModel S .PSU 4 2 1

theorem isFM9_ne_two {p f : ℕ} (hf : 1 ≤ f) (h : IsFM9 (p ^ f)) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  rcases h with h | ⟨-, ⟨k, hk⟩ | ⟨n, hn⟩⟩
  · rw [h] at h2
    omega
  · have h3 : 2 ∣ 2 ^ 2 ^ k := dvd_pow_self 2 (by positivity)
    omega
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have : 0 < 2 ^ f := by positivity
      omega
    · have h3 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega

theorem eq_of_pow_eq_nine {p f : ℕ} (hp : p.Prime) (h : p ^ f = 9) : p = 3 ∧ f = 2 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h
  have hdvd : p ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h]
    exact dvd_pow_self p hf
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 3))
    (by simpa using h : 3 ^ f = 3 ^ 2)⟩

theorem isFM9_five : IsFM9 (5 ^ 1) := Or.inr ⟨by norm_num, Or.inl ⟨1, by norm_num⟩⟩

theorem isFM9_seven : IsFM9 (7 ^ 1) := Or.inr ⟨by norm_num, Or.inr ⟨3, by norm_num⟩⟩

theorem isFM9_nine : IsFM9 (3 ^ 2) := Or.inl (by norm_num)

section Presentations

variable {X : Type} [Group X]

theorem lieModel_psl_two_five_of_alt
    (h : Nonempty (X ≃* alternatingGroup (Fin 5))) :
    LieModel X .PSL 2 5 1 :=
  Or.inl ⟨by decide, statedClassicalModel_psl_two_five_of_alternating_five X h⟩

theorem lieModel_psl_two_five_of_shapeA5
    (h : ShapeA5 X) : LieModel X .PSL 2 5 1 := by
  rcases h with h | h | h
  · exact lieModel_psl_two_five_of_alt h
  · exact lieModel_psl_two_five_of_alt (PSL2_four_alternating_five_model X h)
  · exact h

theorem lieModel_psl_two_seven_of_shapeL27 (h : ShapeL27 X) : LieModel X .PSL 2 7 1 := by
  rcases h with h | h
  · exact h
  · exact PSL3_two_PSL2_seven_paired_isomorphism X h

theorem lieModel_psl_two_nine_of_alt_six (h : Nonempty (X ≃* alternatingGroup (Fin 6))) :
    LieModel X .PSL 2 3 2 :=
  Or.inl ⟨by decide, statedClassicalModel_psl_two_nine_of_alternating_six X h⟩

end Presentations

section Intro

variable {K : Type} [Group K]

theorem K0Shape.of_A5 (h : ShapeA5 K) : K0Shape K := Or.inl h
theorem K0Shape.of_L27 (h : ShapeL27 K) : K0Shape K := Or.inr (Or.inl h)
theorem K0Shape.of_A6 (h : ShapeA6 K) : K0Shape K := Or.inr (Or.inr (Or.inl h))
theorem K0Shape.of_L217 (h : ShapeL217 K) : K0Shape K := Or.inr (Or.inr (Or.inr (Or.inl h)))
theorem K0Shape.of_L28 (h : ShapeL28 K) : K0Shape K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem K0Shape.of_L33 (h : ShapeL33 K) : K0Shape K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
theorem K0Shape.of_U33 (h : ShapeU33 K) : K0Shape K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
theorem K0Shape.of_Sz8 (h : ShapeSz8 K) : K0Shape K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
theorem K0Shape.of_M11 (h : ShapeM11 K) : K0Shape K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
theorem K0Shape.of_2M12 (h : Shape2M12 K) : K0Shape K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
theorem K0Shape.of_2Sz8 (h : Shape2Sz8 K) : K0Shape K :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))

end Intro

section CenterBot

variable {K : Type} [Group K]

theorem lieModel_of_center_bot {t : StatedLieTag} {n p f : ℕ} (hbot : center K = ⊥)
    (h : LieModel (K ⧸ center K) t n p f) : LieModel K t n p f :=
  lieModel_of_mulEquiv (mulEquivOfCenterBot hbot).symm h

theorem isSporadic_of_center_bot {s : TauCeti.SporadicName} (hbot : center K = ⊥)
    (h : NativeSporadic.IsSporadic (K ⧸ center K) s) : NativeSporadic.IsSporadic K s :=
  isSporadic_of_mulEquiv (mulEquivOfCenterBot hbot).symm h

theorem card_center_eq_two_of_le [Finite K] (hZ : center K ≠ ⊥) (hle : Nat.card (center K) ≤ 2) :
    Nat.card (center K) = 2 := by
  have h1 := (Subgroup.one_lt_card_iff_ne_bot (center K)).2 hZ
  omega

end CenterBot

structure CompData (K : Type) [Group K] [Finite K] : Prop where
  quasi : IsQuasisimple K
  pgroup : IsPGroup 2 ↥(center K)
  not_excluded : ¬ ExcludedFromC2 K
  gen4 : Gen4 K
  rank : SectionalTwoRankLE K 3 ∨ center K ≠ ⊥
  restricted : ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel K .PSL 2 p f →
    p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 ∨ p ^ f = 17

namespace CompData

variable {K : Type} [Group K] [Finite K] (D : CompData K)

include D

theorem center_bot_of_noTwoCover {S : Type} [Group S] (hN : NoTwoCover S)
    (e : K ⧸ center K ≃* S) : center K = ⊥ :=
  hN K D.quasi D.pgroup ⟨e⟩

theorem false_of_cert (hbot : center K = ⊥) (hc : RankCertified K 3) : False := by
  rcases D.rank with h | h
  · exact hc.not_sectionalTwoRankLE h
  · exact h hbot

theorem gen4_quotient : Gen4 (K ⧸ center K) := Gen4.quotient _ D.gen4

theorem isSimple_quotient : IsSimpleGroup (K ⧸ center K) := D.quasi.2.1

theorem nonabelian_quotient : ∃ a b : K ⧸ center K, a * b ≠ b * a := D.quasi.2.2

theorem shape_of_psl2 (hG : GenericKnownFacts) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hfm : IsFM9 (p ^ f)) (hL : LieModel (K ⧸ center K) .PSL 2 p f) : K0Shape K := by
  rcases hG.psl2_cover p f hp hp2 K D.quasi D.pgroup hL with hbot | ⟨F, _, _, hF, ⟨e⟩⟩
  · have hLK : LieModel K .PSL 2 p f := lieModel_of_center_bot hbot hL
    rcases D.restricted p f hp hp2 hLK with h | h | h | h
    · obtain ⟨rfl, rfl⟩ := (Nat.prime_five.pow_eq_iff).1 h
      exact K0Shape.of_A5 (Or.inr (Or.inr hLK))
    · obtain ⟨rfl, rfl⟩ := (Nat.prime_seven.pow_eq_iff).1 h
      exact K0Shape.of_L27 (Or.inl hLK)
    · obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_nine hp h
      exact K0Shape.of_A6 (Or.inr hLK)
    · obtain ⟨rfl, rfl⟩ := ((show Nat.Prime 17 by norm_num).pow_eq_iff).1 h
      exact K0Shape.of_L217 hLK
  · exact absurd (Or.inl ⟨F, inferInstance, inferInstance, hF ▸ hfm, ⟨e⟩⟩) D.not_excluded


theorem shape_of_even
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) (hEL : EvenLieRankFour)
    (hE : EvenLieType (K ⧸ center K)) : K0Shape K := by
  rcases hEL _ D.isSimple_quotient D.nonabelian_quotient hE D.gen4_quotient with
    hA5 | hL27 | hL28 | hSz | h216 | h34 | h42 | hU34 | hU42
  · exact D.shape_of_psl2 hG Nat.prime_five (by norm_num) isFM9_five
      (lieModel_psl_two_five_of_shapeA5 hA5)
  · exact D.shape_of_psl2 hG Nat.prime_seven (by norm_num) isFM9_seven
      (lieModel_psl_two_seven_of_shapeL27 hL27)
  · have hbot := D.center_bot_of_noTwoCover (hF.noTwoCover_even _ (Or.inl hL28)) (MulEquiv.refl _)
    exact K0Shape.of_L28 (lieModel_of_center_bot hbot hL28)
  · rcases hF.sz8_cover K D.quasi D.pgroup hSz with hle | hng
    · by_cases hbot : center K = ⊥
      · exact K0Shape.of_Sz8 (lieModel_of_center_bot hbot hSz)
      · exact K0Shape.of_2Sz8 ⟨D.quasi, card_center_eq_two_of_le hbot hle, hSz⟩
    · exact absurd D.gen4 hng
  · have hbot := D.center_bot_of_noTwoCover
      (hF.noTwoCover_even _ (Or.inr (Or.inl h216))) (MulEquiv.refl _)
    exact (D.false_of_cert hbot (rank3_L2_16 (lieModel_of_center_bot hbot h216))).elim
  · by_cases hbot : center K = ⊥
    · exact (D.false_of_cert hbot (rank3_L3_4 (lieModel_of_center_bot hbot h34))).elim
    · by_cases hexp : Monoid.exponent ↥(center K) = 4
      · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h34, hexp⟩))))) D.not_excluded
      · exact absurd D.gen4 (hF.l34_cover K D.quasi D.pgroup h34 hbot hexp)
  · obtain ⟨eA8⟩ := Filter.t_iso_L4_two _ (stated_of_lieModel_PSL h42)
    by_cases hbot : center K = ⊥
    · exact (D.false_of_cert hbot (rank3_L4_2 (lieModel_of_center_bot hbot h42))).elim
    · have hle := hG.alt_cover 8 (by norm_num) (by norm_num) K D.quasi D.pgroup ⟨eA8⟩
      exact absurd (Or.inr (Or.inl ⟨D.quasi, card_center_eq_two_of_le hbot hle, ⟨eA8⟩⟩))
        D.not_excluded
  · have hbot := D.center_bot_of_noTwoCover
      (hF.noTwoCover_even _ (Or.inr (Or.inr hU34))) (MulEquiv.refl _)
    exact (D.false_of_cert hbot (rank3_U3_4 (lieModel_of_center_bot hbot hU34))).elim
  · have hP : LieModel (K ⧸ center K) .PSp 2 3 1 :=
      Or.inl ⟨by decide, Filter.t_iso_U4_two _ (stated_of_lieModel_PSU hU42)⟩
    rcases hG.psp4_cover 3 1 Nat.prime_three (by norm_num) K D.quasi D.pgroup hP with
      hbot | ⟨F, _, _, hF3, ⟨e⟩⟩
    · exact (D.false_of_cert hbot (rank3_U4_2 (lieModel_of_center_bot hbot hU42))).elim
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨F, inferInstance, inferInstance, by simpa using hF3, ⟨e⟩⟩))))) D.not_excluded

theorem false_of_psl4_three (hG : GenericKnownFacts) (hL : LieModel (K ⧸ center K) .PSL 4 3 1) :
    False := by
  by_cases hbot : center K = ⊥
  · exact D.false_of_cert hbot (rank3_L4_3 (lieModel_of_center_bot hbot hL))
  · obtain ⟨-, -, F, _, _, hF, ⟨eS⟩⟩ := lieModel_psl_data hL
    have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_card_eq Nat.prime_three (by norm_num) hF
    have hodd : Odd (Nat.card F) := by rw [hF]; decide
    obtain ⟨π, hπ, hcompat⟩ := hG.psl4_cover K D.quasi D.pgroup F hodd eS
    rcases cover_branch_SL4 hF2 eS π hπ hcompat hbot with ⟨-, ⟨e⟩⟩ | ⟨h1, -⟩
    · exact D.not_excluded (Or.inr (Or.inr (Or.inl ⟨F, inferInstance, inferInstance,
        by simpa using hF, ⟨e⟩⟩)))
    · rw [hF] at h1
      norm_num at h1

theorem false_of_psu4_three (hG : GenericKnownFacts) (hL : LieModel (K ⧸ center K) .PSU 4 3 1) :
    False := by
  by_cases hbot : center K = ⊥
  · exact D.false_of_cert hbot (rank3_U4_3 (lieModel_of_center_bot hbot hL))
  · obtain ⟨-, -, F, _, _, hF, ⟨eS⟩⟩ := lieModel_psu_data hL
    obtain ⟨π, hπ, hcompat⟩ := hG.psu4_cover K D.quasi D.pgroup F (3 ^ 1) hF (by decide) eS
    rcases cover_branch_SU4 hF (by norm_num) eS π hπ hcompat hbot with ⟨h1, -⟩ | ⟨-, hc⟩
    · norm_num at h1
    · exact hc.not_gen4 (le_refl 4) D.gen4

theorem false_of_g2_three
    (hG : GenericKnownFacts) (hL : LieModel (K ⧸ center K) .G2 0 3 1) :
    False := by
  have hbot := D.center_bot_of_noTwoCover
    (hG.noTwoCover_g2 3 1 Nat.prime_three (by norm_num) _ hL) (MulEquiv.refl _)
  exact D.false_of_cert hbot (rank3_G2_3 (lieModel_of_center_bot hbot hL))

theorem shape_of_M12 (hF : E2ComponentFacts)
    (hM : NativeSporadic.IsSporadic (K ⧸ center K) .M12) : K0Shape K := by
  by_cases hbot : center K = ⊥
  · exact (D.false_of_cert hbot (rank3_M12 (isSporadic_of_center_bot hbot hM))).elim
  · exact K0Shape.of_2M12
      ⟨D.quasi, card_center_eq_two_of_le hbot (hF.m12_cover K D.quasi D.pgroup hM), hM⟩

theorem false_of_M22_J2 (hF : E2ComponentFacts)
    (h : NativeSporadic.IsSporadic (K ⧸ center K) .M22 ∨
      NativeSporadic.IsSporadic (K ⧸ center K) .J2) : False := by
  by_cases hbot : center K = ⊥
  · rcases h with h | h
    · exact D.false_of_cert hbot (rank3_M22 (isSporadic_of_center_bot hbot h))
    · exact D.false_of_cert hbot (rank3_J2 (isSporadic_of_center_bot hbot h))
  · exact hF.cover_not_gen4 K D.quasi D.pgroup h hbot D.gen4

theorem false_of_large_sporadic
    {s : TauCeti.SporadicName} (hs : s ∈ Filter.sporadicOut)
    (h : NativeSporadic.IsSporadic (K ⧸ center K) s) : False :=
  Filter.t_sporadic_all Filter.t_sporadic_M s hs _ D.nonabelian_quotient h D.gen4_quotient

end CompData

theorem k0Shape_of_component
    (hG : GenericKnownFacts) (hF : E2ComponentFacts)
    (hEL : EvenLieRankFour) {K : Type} [Group K] [Finite K] (D : CompData K)
    (hC : SimpleInC2 (K ⧸ center K)) : K0Shape K := by
  obtain ⟨-, hc⟩ := hC
  rcases hc with hChev | hL2 | hL33 | hL43 | hU43 | hG23 | hM11 | hM12 | hM22 | hM23 | hM24 |
    hJ2 | hJ3 | hJ4 | hHS | hSuz | hRu | hCo1 | hCo2 | hFi22 | hFi23 | hFi24 | hTh | hB | hM
  · rcases hChev with hE | hA6 | hU33
    · exact D.shape_of_even hG hF hEL hE
    · exact D.shape_of_psl2 hG Nat.prime_three (by norm_num) isFM9_nine
        (lieModel_psl_two_nine_of_alt_six hA6)
    · have hbot := D.center_bot_of_noTwoCover
        (hG.noTwoCover_psu3 3 1 Nat.prime_three (by norm_num) _ hU33) (MulEquiv.refl _)
      exact K0Shape.of_U33 (lieModel_of_center_bot hbot hU33)
  · obtain ⟨p, f, hp, hf, hfm, hL⟩ := hL2
    exact D.shape_of_psl2 hG hp (isFM9_ne_two hf hfm) hfm hL
  · have hbot := D.center_bot_of_noTwoCover
      (hG.noTwoCover_psl3 3 1 Nat.prime_three (by norm_num) _ hL33) (MulEquiv.refl _)
    exact K0Shape.of_L33 (lieModel_of_center_bot hbot hL33)
  · exact (D.false_of_psl4_three hG hL43).elim
  · exact (D.false_of_psu4_three hG hU43).elim
  · exact (D.false_of_g2_three hG hG23).elim
  · have hbot := D.center_bot_of_noTwoCover
      (hF.noTwoCover_sporadic _ hM11) (MulEquiv.refl _)
    exact K0Shape.of_M11 (isSporadic_of_center_bot hbot hM11)
  · exact D.shape_of_M12 hF hM12
  · exact (D.false_of_M22_J2 hF (Or.inl hM22)).elim
  · by_cases hbot : center K = ⊥
    · exact (D.false_of_cert hbot (rank3_M23 (isSporadic_of_center_bot hbot hM23))).elim
    · exact (hF.cover_not_gen4_M23_J3 K D.quasi D.pgroup (Or.inl hM23) hbot D.gen4).elim
  · exact (D.false_of_large_sporadic (by decide) hM24).elim
  · exact (D.false_of_M22_J2 hF (Or.inr hJ2)).elim
  · by_cases hbot : center K = ⊥
    · exact (D.false_of_cert hbot (rank3_J3 (isSporadic_of_center_bot hbot hJ3))).elim
    · exact (hF.cover_not_gen4_M23_J3 K D.quasi D.pgroup (Or.inr hJ3) hbot D.gen4).elim
  · exact (D.false_of_large_sporadic (by decide) hJ4).elim
  · exact (D.false_of_large_sporadic (by decide) hHS).elim
  · exact (D.false_of_large_sporadic (by decide) hSuz).elim
  · exact (D.false_of_large_sporadic (by decide) hRu).elim
  · exact (D.false_of_large_sporadic (by decide) hCo1).elim
  · exact (D.false_of_large_sporadic (by decide) hCo2).elim
  · exact (D.false_of_large_sporadic (by decide) hFi22).elim
  · exact (D.false_of_large_sporadic (by decide) hFi23).elim
  · exact (D.false_of_large_sporadic (by decide) hFi24).elim
  · exact (D.false_of_large_sporadic (by decide) hTh).elim
  · exact (D.false_of_large_sporadic (by decide) hB).elim
  · exact (D.false_of_large_sporadic (by decide) hM).elim

end CFSG.GH74.E2
