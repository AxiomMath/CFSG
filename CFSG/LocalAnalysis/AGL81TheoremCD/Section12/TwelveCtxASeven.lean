module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenOneSixCenterOf

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem card_barM_inf_dvd_seventyTwo_of_twelveCtx
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) {M : Subgroup G} {p : ℕ}
    {Q H : Subgroup G} (h : TwelveCtx G M p Q H) {L : Subgroup G}
    (hL : L ∈ weakBlockSet M H) (h5 : NineThreeFive M L) :
    Nat.card ↥(barM M (H ⊓ L)) ∣ 72 := by
  haveI : IsSimpleGroup G := h.cstar.simple
  have hphase : TwoLocalPhaseThree M H := h.twoLocalPhaseThree
  have hMtop : M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab M h.maxLocal.1
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper hMtop
  have h85 : CFSG.AGLEmbedding.Asc81bEightFive :=
    CFSG.AGLEmbedding.asc81bEightFive_of_factorization
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G :=
    noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
  have hLw : IsWeakSBlock M (pCoreOf 2 H) L := hL
  have hX : ¬ InClassXBlock L := (hphase.nineThree_not_one hK h85 hD2 hLw).1
  have hS : ¬ CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 H ⊓ L) L :=
    hphase.not_isSylowTwoOf_inf hK h85 hD2 hLw
  have h72 := citedBlockAltSevenPL_holds G M (pCoreOf 2 H) L hK hphase.asc81bHyp hLw hX hS h5
  rwa [hphase.toTwoLocalPair.normalizer_twoCore_H] at h72

theorem eq_two_or_three_of_prime_dvd_card_inf_of_twelveCtx
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) {M : Subgroup G} {p : ℕ}
    {Q H : Subgroup G} (h : TwelveCtx G M p Q H) {L : Subgroup G}
    (hL : L ∈ weakBlockSet M H) (h5 : NineThreeFive M L) {r : ℕ} (hr : r.Prime)
    (hrd : r ∣ Nat.card ↥(H ⊓ L)) :
    r = 2 ∨ r = 3 := by
  have hXle : H ⊓ L ≤ M := inf_le_right.trans hL.le
  have hcard := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ((H ⊓ L).subgroupOf M)
  have hbar : ((H ⊓ L).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) =
      barM M (H ⊓ L) := rfl
  have hker : ((H ⊓ L).subgroupOf M) ⊓ (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker =
      ((H ⊓ L).subgroupOf M) ⊓ CFSG.pCore 2 ↥M := by
    rw [QuotientGroup.ker_mk']
  have hKcard : Nat.card ↥((H ⊓ L).subgroupOf M) = Nat.card ↥(H ⊓ L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv
  have hdvd : r ∣ Nat.card (barM M (H ⊓ L)) *
      Nat.card ↥((H ⊓ L).subgroupOf M ⊓ CFSG.pCore 2 ↥M) := by
    have h1' : Nat.card (barM M (H ⊓ L)) *
        Nat.card ↥((H ⊓ L).subgroupOf M ⊓ CFSG.pCore 2 ↥M) =
        Nat.card ↥(H ⊓ L) := by
      rw [← hbar, ← hker, ← hcard, hKcard]
    rw [h1']
    exact hrd
  have hker2 : IsPGroup 2
      ((((H ⊓ L).subgroupOf M) ⊓ CFSG.pCore 2 ↥M : Subgroup ↥M)) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).to_le inf_le_right
  rcases hr.dvd_mul.mp hdvd with hbar72 | hkerdiv
  · have h72 := card_barM_inf_dvd_seventyTwo_of_twelveCtx h1 h2 h25 h hL h5
    have hr72 : r ∣ 72 := hbar72.trans h72
    have hr72' : r ∣ 2 ^ 3 * 3 ^ 2 := by
      simpa [show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num] using hr72
    rcases hr.dvd_mul.mp hr72' with h2' | h3'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
        (hr.dvd_of_dvd_pow h2'))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
        (hr.dvd_of_dvd_pow h3'))
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hker2
    rw [hn] at hkerdiv
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow hkerdiv))

theorem center_barM_le_barM_inf_of_twelveCtx
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour) {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) {L : Subgroup G} (hL : L ∈ weakBlockSet M H)
    (h4 : NineThreeFour M (pCoreOf 2 H) L) :
    ∀ z ∈ Subgroup.center ↥(barM M L),
      (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M (H ⊓ L) := by
  intro z hz
  haveI : IsSimpleGroup G := h.cstar.simple
  have hphase : TwoLocalPhaseThree M H := h.twoLocalPhaseThree
  have hMtop : M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab M h.maxLocal.1
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper hMtop
  have hA : Asc81bHyp M (pCoreOf 2 H) := hphase.asc81bHyp
  have hNH : Subgroup.normalizer (pCoreOf 2 H : Set G) = H :=
    hphase.toTwoLocalPair.normalizer_twoCore_H
  have hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G :=
    noXBlockFor_of_standingGen h1 h2 h25 h.cstar.toStandingGen
  have hO := hphase.oddCore_le_centralizer hK h84 hD2
  have hLsn : (barM M L).IsSubnormal :=
    hL.toIsTwoPrimeComponent.component.2.1.mathlib Subgroup.IsSubnormal.top
  have hZsn : ((Subgroup.center ↥(barM M L)).map (barM M L).subtype).IsSubnormal :=
    Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hLsn
  have hZ3 : Nat.card ((Subgroup.center ↥(barM M L)).map (barM M L).subtype) = 3 := by
    rw [Subgroup.card_map_of_injective (barM M L).subtype_injective]
    exact h4.2.1
  have hZO := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 2 hZsn (by rw [hZ3]; norm_num)
  have hzc := hO (hZO ⟨z, hz, rfl⟩)
  obtain ⟨w, hwL, hwz⟩ := z.2
  refine ⟨w, Subgroup.mem_subgroupOf.mpr ⟨?_, Subgroup.mem_subgroupOf.mp hwL⟩, hwz⟩
  rw [← hNH]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.TenOneSixCenter.mem_normalizer_of_mk_mem_centralizer
    hA.twoRadical.1 hA.twoCore_le w (hwz ▸ hzc)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
