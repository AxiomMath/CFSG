module

import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.CGT.PushingUpLit.Transport
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.AGLEmbedding.CoverNotCaseTwo
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime CFSG.RankThreeCoreUniqueness.Helpers
  Subgroup

namespace InnerQ.ResidueJZero

theorem dvd_card_quotient_center_of_perfect {Y : Type*} [Group Y] [Finite Y]
    (hY : commutator Y = ⊤) {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card Y) :
    p ∣ Nat.card (Y ⧸ center Y) := by
  by_contra h
  obtain ⟨P⟩ : Nonempty (Sylow p Y) := inferInstance
  have hPZ : (P : Subgroup Y) ≤ center Y := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf (QuotientGroup.mk' (center Y) x) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxk, map_one])
    have h2 : orderOf (QuotientGroup.mk' (center Y) x) ∣ Nat.card (Y ⧸ center Y) :=
      orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ k) (Nat.card (Y ⧸ center Y)) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h)
    have h3 : orderOf (QuotientGroup.mk' (center Y) x) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)
  have hP : normalizer ((P : Subgroup Y) : Set Y) ≤ centralizer ((P : Subgroup Y) : Set Y) :=
    fun g _ => mem_centralizer_iff.mpr fun x hx => (mem_center_iff.mp (hPZ hx) g).symm
  set f := MonoidHom.transferSylow P hP
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← hY, commutator_def, commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (mem_center_iff.mp (hPZ (f b).2) (f a))
  have hc := MonoidHom.ker_transferSylow_isComplement' P hP
  rw [← show f.ker = (MonoidHom.transferSylow P hP).ker from rfl, hker] at hc
  have hcard := hc.card_mul
  rw [card_top] at hcard
  have hP1 : Nat.card (P : Subgroup Y) = 1 := by
    have hpos : 0 < Nat.card Y := Nat.card_pos
    nlinarith
  exact P.ne_bot_of_dvd_card hp (card_eq_one.mp hP1)

variable {G : Type} [Group G] [Finite G]

end InnerQ.ResidueJZero

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.RankThreeTheoremC
