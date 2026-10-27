module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInner
import CFSG.Quasithin.EmptyFaithful.Insp9Cases11
import CFSG.Quasithin.H13.KGFactLieOutAbL
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankLin3
import CFSG.GH74.KGroups.L3EpsLin
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Lin
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Uni
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Two

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.QuasithinUnique.Id2519 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

@[expose] def InputL3U3Section : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLThreeEps Y →
    ∀ P : Subgroup (MulAut Y), IsPGroup 3 ↥P → ¬ HasElemSection3 P 4

theorem simple_of_commutator_eq_top_of_isLThreeEps {Y : Type} [Group Y] [Finite Y]
    (h : IsLThreeEps Y) (hc : commutator Y = ⊤) : IsSimpleGroup Y := by
  have hperf : Group.IsPerfect Y := ⟨hc⟩
  rcases h with ⟨K, _, _, -, ⟨e⟩⟩ | ⟨K, _, _, q, hcard, -, ⟨e⟩⟩
  · exact e.isSimpleGroup_congr.2 (CFSG.Quasithin.Insp9.isSimpleGroup_statedProj_statedSL_three K)
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    by_cases hq : 2 < p ^ f
    · have : Fact p.Prime := ⟨hF.prime⟩
      have hnq : (3, p ^ f) ≠ (3, 2) := fun h => by
        simp only [Prod.mk.injEq, true_and] at h
        omega
      exact e.isSimpleGroup_congr.2
        (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hcard 3 le_rfl hnq)
    · exfalso
      have h2 := pow_eq_two_of_not_two_lt hF hq
      have hsol : Group.IsSolvable Y := by
        have := isSolvable_statedProj_of_pow_eq_two hF h2
        exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have c2 : Nat.card Y = 72 := by
        rw [Nat.card_congr e.toEquiv]
        exact card_statedProj_of_pow_eq_two hF h2
      have : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.1 (by omega)
      exact Group.IsPerfect.not_isSolvable Y hsol

theorem hasElemAb_nine_of_isLThreeEps {Y : Type} [Group Y] (h : IsLThreeEps Y) :
    ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  rcases h with ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, q, hcard, hq, ⟨e⟩⟩
  · have := CFSG.QuasithinUnique.Lin2.OddRank.hasElemAb_nine_psl_three_of_dvd (F := K)
      (by omega)
    exact HasElemAb.of_mulEquiv e.symm this
  · have := CFSG.Quasithin.H13.KGLieOut.hasElemAb_nine_psu3 (K := K) (q := q)
      (by omega) hcard (by omega)
    exact HasElemAb.of_mulEquiv e.symm this

theorem field_inner_trivial_of_isLThreeEps {Y : Type} [Group Y] [Finite Y] (hY : IsLThreeEps Y)
    (y : Y) (hα : IsFieldAutThree (MulAut.conj y)) : MulAut.conj y = 1 := by
  obtain ⟨hcd, hcase⟩ := centerDescend_eq_one_of_field_inner hα
  have key : Subgroup.center Y = ⊥ → MulAut.conj y = 1 := fun hZ =>
    eq_one_of_centerDescend_eq_one_of_center_bot hZ hcd
  rcases hY with ⟨F, _, _, -, ⟨e⟩⟩ | ⟨F, _, _, q, hcard, -, ⟨e⟩⟩
  · exact key (center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans (psiO F))
      (CFSG.GH74.KGroups.L3Eps.center_projectiveSL_three_eq_bot))
  · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
    by_cases hq : 2 < p ^ f
    · exact key (center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans (psuO hF).symm)
        (center_unitaryPSU_three_eq_bot hF hq))
    · have h2 := pow_eq_two_of_not_two_lt hF hq
      have hsolY : Group.IsSolvable Y := by
        have := isSolvable_statedProj_of_pow_eq_two hF h2
        exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      rcases hcase with h1 | ⟨F', _, _, ⟨e'⟩⟩ | ⟨p', f', F', _, hF', ⟨e'⟩⟩
      · exact h1
      · exfalso
        obtain ⟨hperf, hnt⟩ := isPerfect_nontrivial_projectiveSL F'
        have : Group.IsSolvable (projectiveSL 3 F') :=
          Group.isSolvable_of_isSolvable_injective (f := e'.symm.toMonoidHom) e'.symm.injective
        exact Group.IsPerfect.not_isSolvable _ this
      · by_cases hq' : 2 < p' ^ f'
        · exfalso
          obtain ⟨hperf, hnt⟩ := isPerfect_nontrivial_unitaryPSU hF' hq'
          have : Group.IsSolvable (unitaryPSU hF' 3) :=
            Group.isSolvable_of_isSolvable_injective (f := e'.symm.toMonoidHom) e'.symm.injective
          exact Group.IsPerfect.not_isSolvable _ this
        · refine key (center_eq_bot_of_card_eq e' ?_)
          have := hF'.finite
          have c1 : Nat.card (unitaryPSU hF' 3) = 72 := by
            rw [Nat.card_congr (psuO hF').toEquiv]
            exact card_statedProj_of_pow_eq_two hF' (pow_eq_two_of_not_two_lt hF' hq')
          have c2 : Nat.card Y = 72 := by
            rw [Nat.card_congr e.toEquiv]
            exact card_statedProj_of_pow_eq_two hF h2
          rw [c1, c2]

theorem inputL3U3Facts_of_section (h : InputL3U3Section) : InputL3U3Facts := by
  intro Y _ _ hY
  exact ⟨simple_of_commutator_eq_top_of_isLThreeEps hY, hasElemAb_nine_of_isLThreeEps hY,
    fun α ⟨g, hg⟩ hα => by
      subst hg
      exact field_inner_trivial_of_isLThreeEps hY g hα,
    h Y hY⟩

theorem inputL3U3Section_holds : InputL3U3Section := by
  intro Y _ _ hY P hP
  rcases hY with ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, q, hcard, hq, ⟨e⟩⟩
  · exact not_hasElemSection3_of_equiv (e.trans (psiO K))
      (fun P hP => not_hasElemSection3_four_projectiveSL hK P hP) P hP
  · by_cases hq2 : q = 2
    · subst hq2
      exact not_hasElemSection3_four_statedProj_two (by rw [hcard]; norm_num) e P hP
    · obtain ⟨p, f, rfl, ⟨hF⟩⟩ := exists_unitaryFieldData hcard
      have hq' : ¬ (3 = 3 ∧ p ^ f = 2) := fun h' => hq2 h'.2
      obtain ⟨⟨eP⟩, -⟩ := unitary_prime_form_full_semilinear_realization hF
        (isPrimeFormGram_one (n := 3) (K := K)) (by norm_num) hq'
      have := hF.finite
      exact not_hasElemSection3_of_equiv ((e.trans (psuO hF).symm).trans eP.symm)
        (fun P hP => not_hasElemSection3_four_primeFormP hF hq2 hq P hP) P hP

theorem inputL3U3Facts_holds : InputL3U3Facts := inputL3U3Facts_of_section inputL3U3Section_holds

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
