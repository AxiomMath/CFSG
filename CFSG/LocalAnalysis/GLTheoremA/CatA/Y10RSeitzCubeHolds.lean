module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzRest
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeBender
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeU33
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeTri
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeRee
public import CFSG.LieType.ChevTwo.Reductions
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrDispatch

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint CFSG.LieType.ChevTwo
open CFSG.AGLEmbedding.ParabAutIrr
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenScope)


section Certs


private theorem seitzSimpleStmt_of_isSmallTwo {S : Type} [Group S] [Finite S]
    (h : IsSmallTwo S) : SeitzSimpleStmt S := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    ·
      have hm : StatedClassicalModel S .PSL 2 2 2 :=
        (CFSG.StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five e).statedClassicalModel
          (by simp [classicalTags])
      exact seitzSimpleStmt_of_twoGen (seitzTwoGen_of_statedPSL_two hm)
    ·
      exact seitzSimpleStmt_of_mulEquiv e.symm seitzSimpleStmt_alternatingGroup_six
    ·
      have hm : StatedClassicalModel S .PSL 4 2 1 :=
        (CFSG.StandardType.ChevTwo.lieModel_psl_four_two_of_alternating_eight e).statedClassicalModel
          (by simp [classicalTags])
      exact seitzSimpleStmt_of_twoGen
        (seitzTwoGen_of_statedClassicalModel (Or.inl rfl) (by simp) (by simp) hm)
  · obtain ⟨i, hv⟩ := d
    rcases hd with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    ·
      subst hdq
      have hm : StatedClassicalModel S .PSL 3 2 1 :=
        (CFSG.StandardType.ChevTwo.lieModel_psl_three_two_of_A_one q hv hq e).statedClassicalModel
          (by simp [classicalTags])
      exact seitzSimpleStmt_of_twoGen
        (seitzTwoGen_of_statedClassicalModel (Or.inl rfl) (by simp) (by simp) hm)
    ·
      subst hdq
      exact seitzSimpleStmt_of_psu_three_three
        (CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two q hv hq e)

theorem seitzCubeRest_of_ree
    (hRee : ∀ (S : Type) [Group S] [Finite S] (a : ℕ), 1 ≤ a →
      ReeTitsModel S .twistedF4 2 (2 * a + 1) → SeitzTwoGen S) : SeitzCubeRest := by
  intro S _ _ hS hnot
  rw [isChevTwo_iff] at hS
  rcases hS with hcl | hexc
  ·
    rcases isClassicalTwoOrG2_cases hcl with ⟨t, n, f, ht, hm⟩ | hG2 | hSmall
    ·
      by_cases hpsl : t = .PSL ∧ n = 2
      · obtain ⟨rfl, rfl⟩ := hpsl
        exact seitzSimpleStmt_of_twoGen (seitzTwoGen_of_statedPSL_two hm)
      · by_cases hpsu : t = .PSU ∧ n = 3
        · obtain ⟨rfl, rfl⟩ := hpsu
          exact seitzSimpleStmt_of_twoGen (seitzTwoGen_of_statedPSU_three hm)
        · exact seitzSimpleStmt_of_twoGen
            (seitzTwoGen_of_statedClassicalModel ht hpsl hpsu hm)
    ·
      obtain ⟨q, hv, hq, ⟨e⟩⟩ := hG2
      have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      have h3 : 3 ≤ 2 ^ q.exponent := by
        have h3 : 3 ≤ q.card := hr
        rwa [TauCeti.PrimePower.card_def, hq] at h3
      have hmodel : ChevalleyExceptionalModel S .G2 2 q.exponent :=
        ⟨⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩,
          CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge
            CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv hq e⟩
      exact seitzSimpleStmt_of_twoGen (seitzTwoGen_of_G2 hmodel)
    · exact seitzSimpleStmt_of_isSmallTwo hSmall
  ·
    obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hexc
    cases d with
    | A r q => exact hd.elim
    | twistedA r q => exact hd.elim
    | B r q => exact hd.elim
    | C r q => exact hd.elim
    | D r q => exact hd.elim
    | twistedD r q => exact hd.elim
    | G2 q => exact hd.elim
    | reeG2 m => exact hd.elim
    | E6 q => exact (hnot ⟨⟨.E6 q, hv⟩, hd, ⟨e⟩⟩).elim
    | E7 q => exact (hnot ⟨⟨.E7 q, hv⟩, hd, ⟨e⟩⟩).elim
    | E8 q => exact (hnot ⟨⟨.E8 q, hv⟩, hd, ⟨e⟩⟩).elim
    | F4 q => exact (hnot ⟨⟨.F4 q, hv⟩, hd, ⟨e⟩⟩).elim
    | twistedE6 q => exact (hnot ⟨⟨.twistedE6 q, hv⟩, hd, ⟨e⟩⟩).elim
    | trialityD4 q =>
        have hp : q.p = 2 := hd
        have hf : 1 ≤ q.exponent := q.exponent_pos
        have hmodel : TwistedChevalleyModel S .D4 (2 ^ q.exponent) :=
          CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge
            CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv hp e
        exact seitzSimpleStmt_of_twoGen (seitzTwoGen_of_twistedChevalleyModel_D4 hf hmodel)
    | suzuki m => exact seitzSimpleStmt_of_twoGen (seitzTwoGen_of_valid_suzuki m hv e)
    | reeF4 a =>
        have ha : 1 ≤ a :=
          (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
            ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
        exact seitzSimpleStmt_of_twoGen
          (hRee S a ha (CFSG.StandardType.ChevTwo.reeTitsModel_of_reeF4 a hv e))
    | tits =>
        exact seitzSimpleStmt_of_titsModel (CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e)

theorem seitzCubeRest_holds : SeitzCubeRest :=
  seitzCubeRest_of_ree fun _ _ _ _ ha h => seitzTwoGen_of_reeTitsModel_twistedF4 ha h

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
