
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOnePrelude

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours
public import CFSG.Sporadic.Schreier.RuOddCore

public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.Sporadic.RuSchreier
open CFSG.ComponentClassification.M12Cover CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th (Rep)

theorem fourClassesLarge_centralizerIn :
    ∀ v ∈ ruP, orderOf v = 2 → FourClassesLarge (centralizerIn ruP v) := by
  refine fourClassesLarge_centralizerIn_of_reps ruP [ruZ, ruA0] ?_ ?_
  · intro v hv h2
    have hmem : v ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨hv, h2⟩
    rw [ruInvolutions_eq] at hmem
    rcases hmem with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
    · exact ⟨ruZ, by simp, g, hg, rfl⟩
    · exact ⟨ruA0, by simp, g, hg, rfl⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [show centralizerIn ruP ruZ = ruC from ruC_eq_centralizer.symm]
      exact fourClassesLarge_ruC
    · rw [show centralizerIn ruP ruA0 = ruL from ruCentralizer_a]
      exact fourClassesLarge_ruL

theorem hypothesisOne_P :
    HypothesisOne ruP := by
  refine hypothesisOne_of_inner (conj_injective_of_center_eq_bot center_ruP) (fun α => ?_)
    fun y hy => ?_
  · obtain ⟨g, hg⟩ := conj_bijective.2 α
    exact ⟨g, hg.symm⟩
  · have hy' : orderOf (y : Equiv.Perm (Fin 4060)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hy
    refine SmallNormalFree.centralizer_of_centralizerIn ruP y ?_
      (fourClassesLarge_centralizerIn y y.2 hy')
    exact (NoOddNormal.of_mulEquiv (centralizerSubgroupEquiv ruP y).symm
      (noOddNormal_centralizer y.2 hy')).cores.2.2

theorem hypothesisOne_native :
    HypothesisOne CFSG.Blueprint.NativeSporadic.Ru :=
  CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv ruEquivP.symm hypothesisOne_P

theorem allInner_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .Ru) : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g := by
  obtain ⟨e⟩ := h
  refine forall_eq_conj_of_mulEquiv (e.trans ruEquivP).symm fun α => ?_
  obtain ⟨g, hg⟩ := conj_bijective.2 α
  exact ⟨g, hg.symm⟩

end CFSG.EvenSporadicStandard.TwoRu.HypOne
