module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOrd
public import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Ree CFSG.StandardType CFSG.Open
open CFSG.RankThree.PartOne.KE
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)


theorem nonempty_szQuot_equiv {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (LargeEvenCenterQuot (LargeEvenSzGroup a K) ≃* suzukiGroup a K) := by
  suffices h : ∀ S : Subgroup (GL (Fin 4) K), S = suzukiGroup a K →
      Nonempty (LargeEvenCenterQuot S ≃* suzukiGroup a K) from
    h _ (largeEvenSzGroup_eq a K)
  intro S hS
  subst hS
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (suzuki_center_eq_bot ha hK)).trans
    QuotientGroup.quotientBot⟩

theorem stOrderBody_suzuki {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (I F : Set (MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K)))) (hF : InnFree p F) :
    StOrderBody p (LargeEvenCenterQuot (LargeEvenSzGroup a K)) I F := by
  intro f hf hord
  obtain ⟨e⟩ := nonempty_szQuot_equiv ha hK
  have hαord : orderOf (MulAut.congr e f) = p := by
    rw [MulEquiv.orderOf_eq (MulAut.congr e) f, hord]
  have hαinn : MulAut.congr e f ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) :=
    fun h => hF f hf hord ((congr_mem_range_conj e f).1 h)
  obtain ⟨σ, h, b, k, _, _, hσp, hbp, hkcard, hconj, ⟨eH⟩⟩ :=
    suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 (MulAut.congr e f) hαord hαinn
  have h1 : fixNum f = Nat.card (suzukiGroup b k) := by
    rw [← fixNum_congr e f, ← fixNum_conj (MulAut.conj h) (MulAut.congr e f), hconj,
      fixNum_eq_card_fixSub]
    exact Nat.card_congr eH.toEquiv
  have hc1 : Nat.card (suzukiGroup b k) = ordSuzuki (2 ^ (2 * b + 1)) := by
    rw [suzuki_order hkcard]
    unfold ordSuzuki
    ring
  have hc2 : Nat.card (LargeEvenCenterQuot (LargeEvenSzGroup a K)) =
      ordSuzuki (2 ^ (2 * a + 1)) := by
    rw [Nat.card_congr e.toEquiv, suzuki_order hK]
    unfold ordSuzuki
    ring
  rw [h1, hc2, hc1, twoPart_of_profile
    (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordSuzuki' (e := 2 * b + 1) (by omega)),
    twoPart_of_profile
      (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordSuzuki' (e := 2 * a + 1) (by omega)),
    ← pow_mul, ← hbp]
  congr 1
  ring

end FQ

end CFSG.LocalAnalysis.GLTheoremA
