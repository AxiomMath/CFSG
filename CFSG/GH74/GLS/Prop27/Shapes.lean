module

public import CFSG.GH74.GLS.Prop27.Defs
public import CFSG.GH74.E2.Components

public section

namespace CFSG.GH74.GLS.Prop27

open Subgroup CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.GH74.E2 CFSG.Blueprint
  Assembly.LowTwoRank

structure CompData7 (K : Type) [Group K] [Finite K] : Prop where
  quasi : IsQuasisimple K
  pgroup : IsPGroup 2 ↥(center K)
  not_excluded : ¬ ExcludedFromC2 K
  gen4 : Gen4 K
  rank : SectionalTwoRankLE K 3 ∨ center K ≠ ⊥
  no_fm9 : ¬ HasL2Model K IsFM9

namespace CompData7

variable {K : Type} [Group K] [Finite K] (D : CompData7 K)

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

theorem false_of_psl2 (hG : GenericKnownFacts) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hfm : IsFM9 (p ^ f)) (hL : LieModel (K ⧸ center K) .PSL 2 p f) : False := by
  rcases hG.psl2_cover p f hp hp2 K D.quasi D.pgroup hL with hbot | ⟨F, _, _, hF, ⟨e⟩⟩
  · exact D.no_fm9 ⟨p, f, hp, hf, hfm, lieModel_of_center_bot hbot hL⟩
  · exact D.not_excluded (Or.inl ⟨F, inferInstance, inferInstance, hF ▸ hfm, ⟨e⟩⟩)

theorem shapes_of_even
    (hG : GenericKnownFacts) (hF : E2ComponentFacts)
    (hE : EvenLieType (K ⧸ center K)) : Shapes7 K := by
  rcases evenLieRankFour _ D.isSimple_quotient D.nonabelian_quotient hE D.gen4_quotient with
    hA5 | hL27 | hL28 | hSz | h216 | h34 | h42 | hU34 | hU42
  · exact (D.false_of_psl2 hG Nat.prime_five (by norm_num) le_rfl isFM9_five
      (lieModel_psl_two_five_of_shapeA5 hA5)).elim
  · exact (D.false_of_psl2 hG Nat.prime_seven (by norm_num) le_rfl isFM9_seven
      (lieModel_psl_two_seven_of_shapeL27 hL27)).elim
  · have hbot := D.center_bot_of_noTwoCover (hF.noTwoCover_even _ (Or.inl hL28)) (MulEquiv.refl _)
    exact Or.inl ⟨hbot, Or.inl (lieModel_of_center_bot hbot hL28)⟩
  · rcases hF.sz8_cover K D.quasi D.pgroup hSz with hle | hng
    · by_cases hbot : center K = ⊥
      · exact Or.inl ⟨hbot, Or.inr (Or.inr (Or.inr (Or.inl (lieModel_of_center_bot hbot hSz))))⟩
      · exact Or.inr (Or.inr ⟨D.quasi, card_center_eq_two_of_le hbot hle, hSz⟩)
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

theorem shapes_of_M12 (hF : E2ComponentFacts)
    (hM : NativeSporadic.IsSporadic (K ⧸ center K) .M12) : Shapes7 K := by
  by_cases hbot : center K = ⊥
  · exact (D.false_of_cert hbot (rank3_M12 (isSporadic_of_center_bot hbot hM))).elim
  · exact Or.inr (Or.inl
      ⟨D.quasi, card_center_eq_two_of_le hbot (hF.m12_cover K D.quasi D.pgroup hM), hM⟩)

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

end CompData7

theorem shapes7_of_component
    (hG : GenericKnownFacts) (hF : E2ComponentFacts)
    {K : Type} [Group K] [Finite K] (D : CompData7 K) (hC : SimpleInC2 (K ⧸ center K)) :
    Shapes7 K := by
  obtain ⟨-, hc⟩ := hC
  rcases hc with hChev | hL2 | hL33 | hL43 | hU43 | hG23 | hM11 | hM12 | hM22 | hM23 | hM24 |
    hJ2 | hJ3 | hJ4 | hHS | hSuz | hRu | hCo1 | hCo2 | hFi22 | hFi23 | hFi24 | hTh | hB | hM
  · rcases hChev with hE | hA6 | hU33
    · exact D.shapes_of_even hG hF hE
    · exact (D.false_of_psl2 hG Nat.prime_three (by norm_num) (by norm_num) isFM9_nine
        (lieModel_psl_two_nine_of_alt_six hA6)).elim
    · have hbot := D.center_bot_of_noTwoCover
        (hG.noTwoCover_psu3 3 1 Nat.prime_three (by norm_num) _ hU33) (MulEquiv.refl _)
      exact Or.inl ⟨hbot, Or.inr (Or.inr (Or.inl (lieModel_of_center_bot hbot hU33)))⟩
  · obtain ⟨p, f, hp, hf, hfm, hL⟩ := hL2
    exact (D.false_of_psl2 hG hp (isFM9_ne_two hf hfm) hf hfm hL).elim
  · have hbot := D.center_bot_of_noTwoCover
      (hG.noTwoCover_psl3 3 1 Nat.prime_three (by norm_num) _ hL33) (MulEquiv.refl _)
    exact Or.inl ⟨hbot, Or.inr (Or.inl (lieModel_of_center_bot hbot hL33))⟩
  · exact (D.false_of_psl4_three hG hL43).elim
  · exact (D.false_of_psu4_three hG hU43).elim
  · exact (D.false_of_g2_three hG hG23).elim
  · have hbot := D.center_bot_of_noTwoCover
      (hF.noTwoCover_sporadic _ hM11) (MulEquiv.refl _)
    exact Or.inl ⟨hbot, Or.inr (Or.inr (Or.inr (Or.inr (isSporadic_of_center_bot hbot hM11))))⟩
  · exact D.shapes_of_M12 hF hM12
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

end CFSG.GH74.GLS.Prop27
