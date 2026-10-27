module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuTwoBChecks
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuTwoBRep
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsA
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB1Group
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Assemble

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.RuStd
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

theorem ruTwoBFacts_ruP :
    RuTwoBFacts ruP := by
  obtain ⟨⟨g, hg, h, hh, hord⟩, u, hu, hu2, hune, hcentral⟩ := ruTwoB_exists
  have hcomm : ∀ x ∈ ruL, x * ruA0 = ruA0 * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (ruL_le_centralizer hx).2
  refine RuTwoBFacts.of_rep ruA0' (fun v hv hc => FactsA.isConj_ruA0'_of_card hv hc) ?_ ?_
  · have hgc : (⟨g, ruL_le hg⟩ : ruP) ∈ centralizer ({ruA0'} : Set ruP) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (hcomm g hg))
    have hhc : (⟨h, ruL_le hh⟩ : ruP) ∈ centralizer ({ruA0'} : Set ruP) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (hcomm h hh))
    refine ⟨⁅(⟨g, ruL_le hg⟩ : ruP), ⟨h, ruL_le hh⟩⁆,
      commutatorElement_mem_derivedCentralizer hgc hhc, ?_⟩
    rw [← Subgroup.orderOf_coe]
    simpa [commutatorElement_def] using hord
  · refine ⟨⟨u, ruL_le hu⟩, ?_, fun h' => hune (congrArg Subtype.val h'), ?_⟩
    · rw [← Subgroup.orderOf_coe]
      exact hu2
    · intro x hx
      have hxL : (x : Equiv.Perm (Fin 4060)) ∈ ruL := by
        rw [← ruCentralizer_a]
        exact Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx))⟩
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hcentral hxL))

theorem ruTwoBFacts_of_isSporadic
    {Y : Type} [Group Y]
    (hY : IsSporadic Y .Ru) : RuTwoBFacts Y := by
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.TwoRu.nonempty_mulEquiv_ruP_of_isSporadic hY
  exact ruTwoBFacts_ruP.of_mulEquiv e.symm

end CFSG.EvenSporadicStandard.RuStd.S2
