module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CoverNotCaseTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 Subgroup

variable {G : Type} [Group G] [Finite G]

theorem odd_orderOf_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup G}
    (hB : IsPGroup p B) {b : G} (hb : b ∈ B) : Odd (orderOf b) := by
  obtain ⟨k, hk⟩ := hB ⟨b, hb⟩
  have hdvd : orderOf b ∣ p ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rw [hi]
  exact (hp.odd_of_ne_two hp2).pow

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
