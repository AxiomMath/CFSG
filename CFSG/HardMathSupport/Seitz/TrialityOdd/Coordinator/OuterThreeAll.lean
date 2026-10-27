module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.OuterThree
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.LieType.SeitzGeneration.ExcOuterTriality

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator



theorem seitzExcOuterNarrowTrialityThree_proved : SeitzExcOuterNarrowTrialityThree := by
  rintro ⟨d, hv⟩ p - - hpc - E hE - ⟨hout, hs, ⟨q, rfl⟩, hp3⟩
  change p = 3 at hp3
  subst hp3
  exfalso
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hE' := isElemAbelian_map_congr e hE
  have hout' := not_le_range_conj_map_congr e hout
  have hs' := NarrowScope.map_congr e hs
  by_cases h2 : q.p = 2
  · have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, h2]
    have hσ' : ∀ c, σ c = c ^ (2 ^ q.exponent) := fun c => by rw [hσ, h2]
    obtain ⟨-, hNF, ⟨Θ, hΘ, -, -, -⟩, hcyc, hcardAut, -, hZ, -⟩ :=
      even_triality_exact_automorphism_normal_form q.exponent_pos K hK' σ hσ'
    exact false_of_outer_three_of_normalForm Nat.prime_two q.exponent_pos hK' σ hσ' hNF Θ hΘ hcyc
      hcardAut hZ _ hE' hout' hs'
  · obtain ⟨-, hNF, ⟨Θ, hΘ, -, -, -⟩, hcyc, hcardAut, -, hZ, -⟩ :=
      odd_triality_exact_automorphism_normal_form q.prime_p h2 q.exponent_pos K hK σ hσ
    exact false_of_outer_three_of_normalForm q.prime_p q.exponent_pos hK σ hσ hNF Θ hΘ hcyc
      hcardAut hZ _ hE' hout' hs'

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
