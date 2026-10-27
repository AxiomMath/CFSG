module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

theorem nonempty_mulEquiv_of_isCaseTwoGroup {p : ℕ} {A B : Type} [Group A] [Group B]
    (hA : IsCaseTwoGroup p A) (hB : IsCaseTwoGroup p B) : Nonempty (A ≃* B) := by
  obtain ⟨⟨i, hi⟩, hd, ⟨e⟩⟩ := hA
  obtain ⟨⟨j, hj⟩, hd', ⟨e'⟩⟩ := hB
  have hij : i = j := by
    rcases hd with ⟨hp, ⟨q, f, hq, hf⟩, hqp, hqe, hi1⟩ | ⟨hp, hi1⟩ <;>
      rcases hd' with ⟨hp', ⟨q', f', hq', hf'⟩, hqp', hqe', hj1⟩ | ⟨hp', hj1⟩
    · simp only at hi1 hj1 hqp hqe hqp' hqe'
      subst hqp hqe hqp' hqe'
      rw [hi1, hj1]
    · omega
    · omega
    · simp only at hi1 hj1
      rw [hi1, hj1]
  subst hij
  exact ⟨e.trans e'.symm⟩

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H : Subgroup G}

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
