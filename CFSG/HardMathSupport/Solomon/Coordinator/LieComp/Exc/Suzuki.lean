module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem noThreeComponents_suzuki (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) {S : Type} [Group S] [Finite S]
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group)) (β : MulAut S) :
    NoThreeComponents β := by
  obtain ⟨e⟩ := he
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  refine noThreeComponents_of_not_dvd (fun h3 => ?_) β
  rw [Nat.card_congr (e.trans θ).toEquiv] at h3
  exact CFSG.RankThree.PartTwo.KFacts.not_three_dvd_card_suzukiGroup hK h3

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
