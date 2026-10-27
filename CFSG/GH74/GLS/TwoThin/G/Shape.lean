module

public import CFSG.GH74.GLS.TwoThin.G.Pred
public import CFSG.GH74.E2.Components

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.E2

@[expose] def C2SimpleShape (K : Type) [Group K] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ IsFM9 (p ^ f) ∧ LieModel K .PSL 2 p f) ∨
    ShapeL28 K ∨ ShapeL33 K ∨ ShapeU33 K ∨ ShapeSz8 K ∨ ShapeM11 K

@[expose] def C2Shape (K : Type) [Group K] : Prop :=
  (center K = ⊥ ∧ C2SimpleShape K) ∨ Shape2M12 K ∨ Shape2Sz8 K

section Intro

variable {K : Type} [Group K]

theorem C2Shape.of_L2 (hz : center K = ⊥)
    (h : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ IsFM9 (p ^ f) ∧ LieModel K .PSL 2 p f) : C2Shape K :=
  Or.inl ⟨hz, Or.inl h⟩
theorem C2Shape.of_L28 (h : ShapeL28 K) (hz : center K = ⊥) : C2Shape K :=
  Or.inl ⟨hz, Or.inr (Or.inl h)⟩
theorem C2Shape.of_L33 (h : ShapeL33 K) (hz : center K = ⊥) : C2Shape K :=
  Or.inl ⟨hz, Or.inr (Or.inr (Or.inl h))⟩
theorem C2Shape.of_U33 (h : ShapeU33 K) (hz : center K = ⊥) : C2Shape K :=
  Or.inl ⟨hz, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
theorem C2Shape.of_Sz8 (h : ShapeSz8 K) (hz : center K = ⊥) : C2Shape K :=
  Or.inl ⟨hz, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
theorem C2Shape.of_M11 (h : ShapeM11 K) (hz : center K = ⊥) : C2Shape K :=
  Or.inl ⟨hz, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
theorem C2Shape.of_2M12 (h : Shape2M12 K) : C2Shape K := Or.inr (Or.inl h)
theorem C2Shape.of_2Sz8 (h : Shape2Sz8 K) : C2Shape K := Or.inr (Or.inr h)

end Intro

structure CompDataG (K : Type) [Group K] [Finite K] : Prop where
  quasi : IsQuasisimple K
  pgroup : IsPGroup 2 ↥(center K)
  not_excluded : ¬ ExcludedFromC2 K
  gen4 : Gen4 K
  rank : SectionalTwoRankLE K 3 ∨ center K ≠ ⊥

namespace CompDataG

variable {K : Type} [Group K] [Finite K] (D : CompDataG K)

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
    (hfm : IsFM9 (p ^ f)) (hL : LieModel (K ⧸ center K) .PSL 2 p f) : C2Shape K := by
  rcases hG.psl2_cover p f hp hp2 K D.quasi D.pgroup hL with hbot | ⟨F, _, _, hF, ⟨e⟩⟩
  · exact C2Shape.of_L2 hbot ⟨p, f, hp, hp2, hfm, lieModel_of_center_bot hbot hL⟩
  · exact absurd (Or.inl ⟨F, inferInstance, inferInstance, hF ▸ hfm, ⟨e⟩⟩) D.not_excluded

theorem shape_of_even
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) (hEL : EvenLieRankFour)
    (hE : EvenLieType (K ⧸ center K)) : C2Shape K := by
  rcases hEL _ D.isSimple_quotient D.nonabelian_quotient hE D.gen4_quotient with
    hA5 | hL27 | hL28 | hSz | h216 | h34 | h42 | hU34 | hU42
  · exact D.shape_of_psl2 hG Nat.prime_five (by norm_num) isFM9_five
      (lieModel_psl_two_five_of_shapeA5 hA5)
  · exact D.shape_of_psl2 hG Nat.prime_seven (by norm_num) isFM9_seven
      (lieModel_psl_two_seven_of_shapeL27 hL27)
  · have hbot := D.center_bot_of_noTwoCover (hF.noTwoCover_even _ (Or.inl hL28)) (MulEquiv.refl _)
    exact C2Shape.of_L28 (lieModel_of_center_bot hbot hL28) hbot
  · rcases hF.sz8_cover K D.quasi D.pgroup hSz with hle | hng
    · by_cases hbot : center K = ⊥
      · exact C2Shape.of_Sz8 (lieModel_of_center_bot hbot hSz) hbot
      · exact C2Shape.of_2Sz8 ⟨D.quasi, card_center_eq_two_of_le hbot hle, hSz⟩
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
    (hM : NativeSporadic.IsSporadic (K ⧸ center K) .M12) : C2Shape K := by
  by_cases hbot : center K = ⊥
  · exact (D.false_of_cert hbot (rank3_M12 (isSporadic_of_center_bot hbot hM))).elim
  · exact C2Shape.of_2M12
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

end CompDataG

theorem c2Shape_of_component
    (hG : GenericKnownFacts) (hF : E2ComponentFacts)
    (hEL : EvenLieRankFour) {K : Type} [Group K] [Finite K] (D : CompDataG K)
    (hC : SimpleInC2 (K ⧸ center K)) : C2Shape K := by
  obtain ⟨-, hc⟩ := hC
  rcases hc with hChev | hL2 | hL33 | hL43 | hU43 | hG23 | hM11 | hM12 | hM22 | hM23 | hM24 |
    hJ2 | hJ3 | hJ4 | hHS | hSuz | hRu | hCo1 | hCo2 | hFi22 | hFi23 | hFi24 | hTh | hB | hM
  · rcases hChev with hE | hA6 | hU33
    · exact D.shape_of_even hG hF hEL hE
    · exact D.shape_of_psl2 hG Nat.prime_three (by norm_num) isFM9_nine
        (lieModel_psl_two_nine_of_alt_six hA6)
    · have hbot := D.center_bot_of_noTwoCover
        (hG.noTwoCover_psu3 3 1 Nat.prime_three (by norm_num) _ hU33) (MulEquiv.refl _)
      exact C2Shape.of_U33 (lieModel_of_center_bot hbot hU33) hbot
  · obtain ⟨p, f, hp, hf, hfm, hL⟩ := hL2
    exact D.shape_of_psl2 hG hp (isFM9_ne_two hf hfm) hfm hL
  · have hbot := D.center_bot_of_noTwoCover
      (hG.noTwoCover_psl3 3 1 Nat.prime_three (by norm_num) _ hL33) (MulEquiv.refl _)
    exact C2Shape.of_L33 (lieModel_of_center_bot hbot hL33) hbot
  · exact (D.false_of_psl4_three hG hL43).elim
  · exact (D.false_of_psu4_three hG hU43).elim
  · exact (D.false_of_g2_three hG hG23).elim
  · have hbot := D.center_bot_of_noTwoCover
      (hF.noTwoCover_sporadic _ hM11) (MulEquiv.refl _)
    exact C2Shape.of_M11 (isSporadic_of_center_bot hbot hM11) hbot
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

theorem c2Shape_of_inC2
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) {L : Type} [Group L]
    [Finite L] (hL : InC2 L) (hP : Gen4Comp L) : C2Shape L := by
  obtain ⟨hq, hZ, hS, hne⟩ := hL
  have hZ2 : IsPGroup 2 ↥(center L) := by
    rw [hZ]
    exact CFSG.pCore_isPGroup
  exact c2Shape_of_component hG hF evenLieRankFour
    ⟨hq, hZ2, hne, hP.1, hP.2⟩ hS

theorem c2ShapeG_of_inC2
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) {L : Type} [Group L]
    [Finite L] (hL : InC2 L) (hgen : Gen4 L) :
    center L = ⊥ ∨ Shape2M12 L ∨ Shape2Sz8 L := by
  by_cases hz : center L = ⊥
  · exact Or.inl hz
  · rcases c2Shape_of_inC2 hG hF hL ⟨hgen, Or.inr hz⟩ with ⟨hz', -⟩ | h | h
    · exact absurd hz' hz
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end CFSG.GH74.GLS.TwoThin
