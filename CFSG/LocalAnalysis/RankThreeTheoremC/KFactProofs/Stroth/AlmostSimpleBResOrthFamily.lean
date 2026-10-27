module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResOrthMinus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResLeaves

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)
open CFSG.LieType.SeitzGeneration (not_rankLE2_three_plus not_rankLE2_three_minus)

theorem five_le_of_prime_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  by_contra h
  have h2 := hp.two_le
  have h4 : p = 4 := by omega
  subst h4
  exact absurd hp (by norm_num)

theorem chevTwoOuterFixesPair_omegaPlus : ChevTwoOuterFixesPair LieIndexOmegaPlus := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | D r q =>
    have hq2 : q.p = 2 := hchar
    have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hcl : StatedClassicalModel L .POmegaPlus r 2 q.exponent := by
      have := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq2 e
      rwa [hq2] at this
    have hcl' := hcl
    obtain ⟨-, F, _, _, hFc, ⟨eL⟩⟩ := hcl
    obtain ⟨hrk2, -⟩ := rank_data_of_pRank hp hrk eL
    by_cases hp3 : p = 3
    · subst hp3
      exact absurd hrk2 (not_rankLE2_three_plus hr4)
    · obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_of_pRank_eq_two hp hrk
      exact plus_outer_fixesPair hcl' hp (five_le_of_prime_ne hp hp2 hp3) ⟨E, hE, hEc⟩ hα hαp
  | A _ _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | B _ _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | C _ _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | E6 _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | E7 _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | E8 _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | F4 _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | G2 _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | suzuki _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | reeG2 _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | reeF4 _ => exact absurd hF (by simp [LieIndexOmegaPlus])
  | tits => exact absurd hF (by simp [LieIndexOmegaPlus])

theorem chevTwoOuterFixesPair_omegaMinus : ChevTwoOuterFixesPair LieIndexOmegaMinus := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedD r q =>
    have hq2 : q.p = 2 := hchar
    have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hcl : StatedClassicalModel L .POmegaMinus r 2 q.exponent := by
      have := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq2 e
      rwa [hq2] at this
    have hcl' := hcl
    obtain ⟨-, F, _, _, hFc, b, c, hirr, ⟨eL⟩⟩ := hcl
    obtain ⟨hrk2, -⟩ := rank_data_of_pRank hp hrk eL
    by_cases hp3 : p = 3
    · subst hp3
      exact absurd hrk2 (not_rankLE2_three_minus hr4 hirr)
    · obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_of_pRank_eq_two hp hrk
      exact minus_outer_fixesPair hcl' hp (five_le_of_prime_ne hp hp2 hp3) ⟨E, hE, hEc⟩ hα hαp
  | A _ _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | B _ _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | C _ _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | D _ _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | E6 _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | E7 _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | E8 _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | F4 _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | G2 _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | suzuki _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | reeG2 _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | reeF4 _ => exact absurd hF (by simp [LieIndexOmegaMinus])
  | tits => exact absurd hF (by simp [LieIndexOmegaMinus])

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
