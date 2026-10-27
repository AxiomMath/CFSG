module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinL2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinL3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAlt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinClsOdd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinClsEven

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

theorem hinFor_linear_unitary :
    HinFor fun Y _ => ∃ n ℓ f : ℕ, Assembly.LowTwoRank.StatedClassicalModel Y .PSL n ℓ f ∨
      Assembly.LowTwoRank.StatedClassicalModel Y .PSU n ℓ f := by
  intro Y _ _ _ ⟨n, ℓ, f, hY⟩ hnab p m hp hp2 hm h16 h44 τ hτ hL
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    rcases hY with hY | hY
    · obtain ⟨⟨-, -, hn, -⟩, -⟩ := id hY
      rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
      · exact hinFor_psl2 Y ⟨2, f, hY⟩ hnab p m hp hp2 hm h16 h44 τ hτ hL
      · by_cases hA : ∃ k : ℕ, 5 ≤ k ∧ Nonempty (Y ≃* alternatingGroup (Fin k))
        · exact hinFor_alt Y hA hnab p m hp hp2 hm h16 h44 τ hτ hL
        · refine hinConcl_psl_even hnab hn3 hY (fun k hk => ?_) hp hp2 hm h16 hτ hL
          exact not_nonempty_iff.mp fun h => hA ⟨k, hk, h⟩
    · exact hinConcl_psu_even hnab hY hp hp2 hm h16 hτ hL
  · rcases hY with hY | hY
    · obtain ⟨⟨hℓ, hf, hn, -⟩, -⟩ := id hY
      rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | hn5
      · exact hinFor_psl2 Y ⟨ℓ, f, hY⟩ hnab p m hp hp2 hm h16 h44 τ hτ hL
      · exact hinFor_l3u3_odd Y ⟨ℓ, f, hℓ2, Or.inl hY⟩ hnab p m hp hp2 hm h16 h44 τ hτ hL
      · exfalso
        have hpl := eq_of_psl4 hnab hℓ hℓ2 hY hp hp2 hm h16 hτ hL
        subst hpl
        exact (h44 f hf).1 (Or.inl ⟨by simp [Blueprint.classicalTags], hY⟩)
      · exact (false_of_psl_ge_five hnab hn5 hℓ hℓ2 hY hp2 hτ hL).elim
    · obtain ⟨⟨hℓ, hf, hn, -⟩, -⟩ := id hY
      rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | hn5
      · exact hinFor_l3u3_odd Y ⟨ℓ, f, hℓ2, Or.inr hY⟩ hnab p m hp hp2 hm h16 h44 τ hτ hL
      · exfalso
        have hpl := eq_of_psu4 hnab hℓ hℓ2 hY hp hp2 hm h16 hτ hL
        subst hpl
        exact (h44 f hf).2 (Or.inl ⟨by simp [Blueprint.classicalTags], hY⟩)
      · exact (false_of_psu_ge_five hnab hn5 hℓ hℓ2 hf hY hp hp2 hm h16 hτ hL).elim

theorem hinFor_symplectic_even :
    HinFor fun Y _ => ∃ n f : ℕ, Assembly.LowTwoRank.StatedClassicalModel Y .PSp n 2 f := by
  intro Y _ _ _ ⟨n, f, hY⟩ hnab p m hp hp2 hm _ _ τ hτ hL
  exact hinConcl_psp_even hnab hY hp hp2 hm hτ hL

theorem hinFor_classicalRep_of_rows
    (hSp : HinFor fun Y _ => ∃ n ℓ f : ℕ, ℓ ≠ 2 ∧
      Assembly.LowTwoRank.StatedClassicalModel Y .PSp n ℓ f)
    (hO : HinFor fun Y _ => ∃ (t : Assembly.LowTwoRank.StatedLieTag) (n ℓ f : ℕ),
      (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
        Assembly.LowTwoRank.StatedClassicalModel Y t n ℓ f) :
    HinFor fun Y _ => Milestones.ClassicalRep Y := by
  intro Y _ _ _ ⟨t, n, ℓ, f, hY⟩
  cases t with
  | PSL => exact hinFor_linear_unitary Y ⟨n, ℓ, f, Or.inl hY⟩
  | PSU => exact hinFor_linear_unitary Y ⟨n, ℓ, f, Or.inr hY⟩
  | PSp =>
    by_cases hℓ : ℓ = 2
    · subst hℓ
      exact hinFor_symplectic_even Y ⟨n, f, hY⟩
    · exact hSp Y ⟨n, ℓ, f, hℓ, hY⟩
  | POmegaOdd => exact hO Y ⟨_, n, ℓ, f, Or.inl rfl, hY⟩
  | POmegaPlus => exact hO Y ⟨_, n, ℓ, f, Or.inr (Or.inl rfl), hY⟩
  | POmegaMinus => exact hO Y ⟨_, n, ℓ, f, Or.inr (Or.inr rfl), hY⟩
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact hY.2.elim

end CFSG.ComponentClassification.HarrisLit.Hin
