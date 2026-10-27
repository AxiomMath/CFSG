module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieInn
import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Lin
import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Symp
import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Orth
import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4ExcHolds
import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4OtherHolds
import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Ord
import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup lieOrderBridge_holds)


theorem eq_twistedE6_of_triD4 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (hSd : Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))
    {α β : MulAut S} (hα : α ∈ innAutDerived S) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hβ : β ∈ innAutDerived S) (hβ3 : β ^ 3 = 1) (hαβ : Commute α β) {J : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup α) J) (hT : catalogIs (PSimple 3 J) S9.isD4two)
    (hβJ : ∀ y ∈ J, β y ∈ J) (hni : ¬ ∃ j ∈ J, ∀ y ∈ J, β y = j * y * j⁻¹) :
    ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card = 2 := by
  obtain ⟨e⟩ := hSd
  have hC : H1431c.CompOfType S α S9.isD4two := ⟨J, hJ, hT⟩
  obtain ⟨i, J', hrel, ⟨φ⟩, hT'⟩ := H1431c.lieSInn_component_index
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent hS hnc d hd e
    (I1431C2.compIdxAt_three_of_families KD264Lie.lieCompIdx_linear KD264Lie.lieCompIdx_unitary
      KD264Lie.lieCompIdx_classicalBCD KD264Lie.lieCompIdx_triality
      KD264Lie.lieCompIdx_excUntwisted KD264Lie.lieCompIdx_excTwisted d hd)
    hα hα3 hα1 hC
  have hcard : Nat.card (↥J' ⧸ Subgroup.center ↥J') = 174182400 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two
      (D4XF.statedModel_of_d4two hT')).2.2.2.1 rfl]
    decide +kernel
  have hf : KD264Lie.fieldSize d.1 = 2 :=
    (fieldSize_eq_two_of_d4two lieOrderBridge_holds d hd i hrel φ hcard).1
  by_cases hE : ∃ q, d.1 = .twistedE6 q
  · obtain ⟨q, hq⟩ := hE
    exact ⟨q, hq, by rwa [hq] at hf⟩
  · exact absurd (triD4No_notTwE6 triD4NoA_holds triD4NoTwistedA_holds triD4NoB_holds
      triD4NoD_holds triD4NoTwistedD_holds triD4NoE6_holds triD4NoE78_holds triD4NoF4_holds
      triD4NoOther_holds S hS hnc d hE hd hf ⟨e⟩ α β hα hα3 hα1 hβ hβ3 hαβ J hJ hT hβJ) hni

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
