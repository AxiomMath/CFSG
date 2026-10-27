module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdEvenB
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.GSThmB
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem almostSimpleRestricted_catalog_of_inputs
    (hOL : AlmostSimpleRestricted OddLinearUnrestricted)
    (hOC : AlmostSimpleRestricted OddClassicalUnrestricted)
    (hEO : AlmostSimpleRestricted EvenOrthogonal)
    (hEx : AlmostSimpleRestricted ExceptionalChevalley)
    (hSp : AlmostSimpleRestricted SporadicUnrestricted) :
    AlmostSimpleRestricted fun Y _ => Catalog Y := by
  intro A _ _ W _ hWs hWnab hCW hcat _ a ha L hLW hne hL hstd hs
  by_cases halt : ∃ m : ℕ, 5 ≤ m ∧ Nonempty (W ≃* alternatingGroup (Fin m))
  · obtain ⟨m, hm, h⟩ := halt
    exact gsRestricted_of_alternating hm h
  have hWalt : ∀ m : ℕ, 5 ≤ m → IsEmpty (W ≃* alternatingGroup (Fin m)) :=
    fun m hm => not_nonempty_iff.mp fun h => halt ⟨m, hm, h⟩
  rcases (Milestones.ct_catalog_nonabelian_type_partition W hWnab).mp hcat with
    hA | hodd | heven | hspor
  · exact absurd hA halt
  · rcases gsRestricted_or_of_oddLieType hodd with h | h | h | h
    · exact h
    · exact hOL A W hWs hWnab hCW hcat h a ha L hLW hne hL hstd hs
    · exact hOC A W hWs hWnab hCW hcat h a ha L hLW hne hL hstd hs
    · exact hEx A W hWs hWnab hCW hcat h a ha L hLW hne hL hstd hs
  · obtain ⟨t, n, f, hadm, hm⟩ := heven
    have hf : 1 ≤ f := hadm.2.1
    cases t with
    | PSL =>
      have hn : 2 ≤ n := hadm.2.2.1
      rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
      · exact gsRestricted_even_psl_two hWs hWnab hCW ha hLW hL hs hm
      · exact gsRestricted_even_psl hWs hWnab hCW ha hLW hL hs h3 hf hm hWalt
    | PSU => exact gsRestricted_even_psu hWs hWnab hCW ha hLW hL hs hm
    | PSp => exact gsRestricted_even_psp hWs hWnab hCW ha hLW hL hs hm
    | POmegaOdd => exact absurd rfl hadm.2.2.2
    | POmegaPlus =>
      exact hEO A W hWs hWnab hCW hcat ⟨n, f, hadm.2.2, hf, Or.inl hm⟩ a ha L hLW hne hL hstd hs
    | POmegaMinus =>
      exact hEO A W hWs hWnab hCW hcat ⟨n, f, hadm.2.2, hf, Or.inr hm⟩ a ha L hLW hne hL hstd hs
    | G2 => exact hEx A W hWs hWnab hCW hcat ⟨.G2, 2, f, by decide, Nat.prime_two, hf,
        lieModel_exceptional_zero (by decide) hm⟩ a ha L hLW hne hL hstd hs
    | F4 => exact hEx A W hWs hWnab hCW hcat ⟨.F4, 2, f, by decide, Nat.prime_two, hf,
        lieModel_exceptional_zero (by decide) hm⟩ a ha L hLW hne hL hstd hs
    | E6 => exact hEx A W hWs hWnab hCW hcat ⟨.E6, 2, f, by decide, Nat.prime_two, hf,
        lieModel_exceptional_zero (by decide) hm⟩ a ha L hLW hne hL hstd hs
    | E7 => exact hEx A W hWs hWnab hCW hcat ⟨.E7, 2, f, by decide, Nat.prime_two, hf,
        lieModel_exceptional_zero (by decide) hm⟩ a ha L hLW hne hL hstd hs
    | E8 => exact hEx A W hWs hWnab hCW hcat ⟨.E8, 2, f, by decide, Nat.prime_two, hf,
        lieModel_exceptional_zero (by decide) hm⟩ a ha L hLW hne hL hstd hs
    | twistedE6 => exact hEx A W hWs hWnab hCW hcat ⟨.twistedE6, 2, f, by decide, Nat.prime_two,
        hf, lieModel_exceptional_zero (by decide) hm⟩ a ha L hLW hne hL hstd hs
    | trialityD4 => exact hEx A W hWs hWnab hCW hcat ⟨.trialityD4, 2, f, by decide,
        Nat.prime_two, hf, lieModel_exceptional_zero (by decide) hm⟩ a ha L hLW hne hL hstd hs
    | twistedB2 => exact (not_lieModel_twistedB2 hWs hWnab hCW ha hLW hL hm).elim
    | twistedG2 => exact absurd hadm.2.2.2.1 (by decide)
    | twistedF4 => exact (not_lieModel_large_ree_tits hWs hWnab hCW ha hLW hL (Or.inl rfl) hm).elim
    | Tits => exact (not_lieModel_large_ree_tits hWs hWnab hCW ha hLW hL (Or.inr rfl) hm).elim
  · obtain ⟨s, ⟨e⟩⟩ := hspor
    by_cases hsr : s ∈ restrictedSporadicNames
    · exact gsRestricted_of_isSporadic hsr ⟨e⟩
    · exact hSp A W hWs hWnab hCW hcat ⟨s, hsr, ⟨e⟩⟩ a ha L hLW hne hL hstd hs

theorem restrictedStandard_of_inputs (hS : SchreierFor Catalog)
    (hOL : AlmostSimpleRestricted OddLinearUnrestricted)
    (hOC : AlmostSimpleRestricted OddClassicalUnrestricted)
    (hEO : AlmostSimpleRestricted EvenOrthogonal)
    (hEx : AlmostSimpleRestricted ExceptionalChevalley)
    (hSp : AlmostSimpleRestricted SporadicUnrestricted) : RestrictedStandardInput :=
  restrictedStandard_of_almostSimple hS
    (almostSimpleRestricted_catalog_of_inputs hOL hOC hEO hEx hSp)

end CFSG.ComponentClassification.RestrictedStd
