module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverLarge
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigher
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
public import CFSG.LieType.Chevalley.G2LargeEvenCover
public import CFSG.LieType.Chevalley.TrialityFieldTwoCover
public import CFSG.LieType.Ree.LargeReeEightCentralTwoCover

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

theorem sylowCentralizerCentral_of_psl_two_even {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : 2 ≤ f) (h : StatedClassicalModel X .PSL 2 2 f) : SylowCentralizerCentral X :=
  sylowCentralizerCentral_of_bender (K1.fusionIsBenderGroup_of_stated_psl_two hf h)

theorem sylowCentralizerCentral_of_psu_three_even {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : 2 ≤ f) (h : StatedClassicalModel X .PSU 3 2 f) : SylowCentralizerCentral X :=
  sylowCentralizerCentral_of_bender (K1.fusionIsBenderGroup_of_stated_psu_three hf h)

theorem sylowCentralizerCentral_of_suzuki {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : SuzukiModel X 2 f) : SylowCentralizerCentral X :=
  sylowCentralizerCentral_of_bender (K1.fusionIsBenderGroup_of_suzukiModel h)

theorem sylowCentralizerCentral_of_psl_three_large {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : 3 ≤ f) (h : StatedClassicalModel X .PSL 3 2 f) : SylowCentralizerCentral X := by
  refine sylowCentralizerCentral_of_cover_trivial ?_
  intro E _ _ _ η hη hC h2
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearCover.even_linear_three_large_field_catalog_central_two_cover_trivial
    η hη hC h2 hf (Or.inl ⟨by decide, h⟩)).1

theorem sylowCentralizerCentral_of_psp_four {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : 2 ≤ f) (h : StatedClassicalModel X .PSp 2 2 f) : SylowCentralizerCentral X := by
  refine sylowCentralizerCentral_of_cover_trivial ?_
  intro E _ _ _ η hη hC h2
  exact (CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour.even_symplectic_four_catalog_perfect_central_two_cover_trivial
    η hη hC h2 hf (Or.inl ⟨by decide, h⟩)).1

theorem sylowCentralizerCentral_of_g2_large
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : 3 ≤ f) (h : ChevalleyExceptionalModel X .G2 2 f) : SylowCentralizerCentral X := by
  refine sylowCentralizerCentral_of_cover_trivial ?_
  intro E _ _ _ η hη hC h2
  exact (CFSG.LieType.Chevalley.G2_large_even_field_central_two_cover_trivial η hη hC h2 hf
    (Or.inr (Or.inl ⟨rfl, by decide, h⟩))).1

theorem sylowCentralizerCentral_of_triality
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : 1 ≤ f) (h : ChevalleyExceptionalModel X .trialityD4 2 f) :
    SylowCentralizerCentral X := by
  refine sylowCentralizerCentral_of_cover_trivial ?_
  intro E _ _ _ η hη hC h2
  have hJ : LieModel X .trialityD4 0 2 f := Or.inr (Or.inl ⟨rfl, by decide, h⟩)
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    exact (CFSG.LieType.Chevalley.triality_field_two_central_two_cover_trivial η hη hC h2 hJ).1
  · exact (CFSG.LieType.Chevalley.triality_nonprime_even_field_central_two_cover_trivial η hη hC
      h2 hf2 hJ).1

theorem sylowCentralizerCentral_of_ree
    {X : Type} [Group X] [Finite X] {f : ℕ} (hodd : Odd f)
    (hf : 3 ≤ f) (h : ReeTitsModel X .twistedF4 2 f) : SylowCentralizerCentral X := by
  refine sylowCentralizerCentral_of_cover_trivial ?_
  intro E _ _ _ η hη hC h2
  have hJ : LieModel X .twistedF4 0 2 f := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, h⟩))
  by_cases hf3 : f = 3
  · subst hf3
    exact (CFSG.LieType.Ree.large_Ree_field_eight_central_two_cover_trivial η hη hC h2 hJ).1
  · obtain ⟨k, hk⟩ := hodd
    exact (CFSG.LieType.Ree.large_Ree_large_even_field_central_two_cover_trivial η hη hC h2
      (by omega) hJ).1

theorem sylowCentralizerCentral_of_psl_five_two {X : Type} [Group X] [Finite X]
    (h : StatedClassicalModel X .PSL 5 2 1) : SylowCentralizerCentral X := by
  refine sylowCentralizerCentral_of_cover_trivial ?_
  intro E _ _ _ η hη hC h2
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearCover.even_higher_linear_prime_field_central_two_cover_trivial
    η hη hC h2 le_rfl (Or.inl ⟨by decide, h⟩)).1

@[expose] def TitsTwoCoverTrivial : Prop :=
  ∀ (X : Type) [Group X] [Finite X], ReeTitsModel X .Tits 2 1 →
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (η : E →* X), Function.Surjective η →
      η.ker ≤ Subgroup.center E → IsPGroup 2 η.ker → η.ker = ⊥

theorem sylowCentralizerCentral_of_tits (hT : TitsTwoCoverTrivial) {X : Type} [Group X] [Finite X]
    (h : ReeTitsModel X .Tits 2 1) : SylowCentralizerCentral X := by
  refine sylowCentralizerCentral_of_cover_trivial ?_
  intro E _ _ _ η hη hC h2
  exact hT X h E η hη hC h2

end CFSG.QuasithinUnique.Ch1
