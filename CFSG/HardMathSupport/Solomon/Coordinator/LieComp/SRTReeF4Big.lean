module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTLargeReeComp
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartOne.KLC.Transport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.HardMathSupport.Dickson.SuzukiReeB (fixSubgroup_conj)


private theorem odd_index_of_two_elements' {Γ : Type*} [Group Γ] [Finite Γ] (C N : Subgroup Γ)
    (hNC : N ≤ C) (hN2 : ∀ g ∈ C, (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) :
    Odd (N.subgroupOf C).index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  have hPN : (P : Subgroup ↥C) ≤ N.subgroupOf C := by
    intro g hg
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 P.isPGroup' ⟨g, hg⟩
    refine hN2 (g : Γ) g.2 ⟨k, ?_⟩
    rw [Subgroup.orderOf_coe g, ← hk]
    exact (Subgroup.orderOf_mk g hg).symm
  have h1 : (N.subgroupOf C).index ∣ (P : Subgroup ↥C).index := Subgroup.index_dvd_of_le hPN
  have h2 : ¬ 2 ∣ (P : Subgroup ↥C).index := P.not_dvd_index
  exact (Nat.odd_iff.2 (by omega)).of_dvd_nat h1

theorem srtOut_of_component_data {q : ℕ} {S : Type} [Group S] [Finite S] (β : MulAut S)
    (N : Subgroup S) (hNC : N ≤ fixSubgroup β)
    (hN2 : ∀ g ∈ fixSubgroup β, (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N)
    (hall : ∀ D : Subgroup S, CFSG.RankThree.PartOne.IsComponentOf (fixSubgroup β) D → D = N)
    (hcomp : N ≠ ⊥ → CFSG.RankThree.PartOne.IsComponentOf (fixSubgroup β) N)
    (hX : N ≠ ⊥ → IsSimpleGroup ↥N ∧ LieFactorData q ↥N ∧
      (LieOrderBridge → IsEmpty (↥N ≃* alternatingGroup (Fin 6)))) : SRTOut q β := by
  by_cases hN : N = ⊥
  · refine srtOut_of_isSolvable q β ?_
    have h := odd_index_of_two_elements' (fixSubgroup β) N hNC hN2
    rw [hN, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ h
  · obtain ⟨hs, hl, h6⟩ := hX hN
    have hc := hcomp hN
    have hconj : ∀ g ∈ fixSubgroup β, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
      intro g hg n hn
      have h1 := CFSG.RankThree.PartOne.KLC.isComponentOf_map_mulEquiv' (MulAut.conj g) hc
      have hC : (fixSubgroup β).map (MulAut.conj g).toMonoidHom = fixSubgroup β := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact (fixSubgroup β).mul_mem ((fixSubgroup β).mul_mem hg hz)
            ((fixSubgroup β).inv_mem hg)
        · intro hy
          refine ⟨g⁻¹ * y * g, (fixSubgroup β).mul_mem
            ((fixSubgroup β).mul_mem ((fixSubgroup β).inv_mem hg) hy) hg, ?_⟩
          show g * (g⁻¹ * y * g) * g⁻¹ = y
          group
      rw [hC] at h1
      have h2 := hall _ h1
      rw [← h2]
      exact ⟨n, hn, rfl⟩
    haveI hNn : (N.subgroupOf (fixSubgroup β)).Normal :=
      (Subgroup.normal_subgroupOf_iff hNC).2 fun h k hh hk => hconj k hk h hh
    have hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ N.subgroupOf (fixSubgroup β)) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_index_of_two_elements' (fixSubgroup β) N hNC hN2)
    have hq : CFSG.Open.IsQuasisimple ↥N := LieSemisimple.open_isQuasisimple hc.2.1
    have hnc : ∃ a b : ↥N, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      haveI := hs
      have hc : commutator ↥N = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hcon y x
      rw [hq.1] at hc
      exact top_ne_bot hc
    refine srtOut_of_normal β hNC hsol hq hl fun hb => ?_
    haveI := hs
    have hZ : Subgroup.center ↥N = ⊥ := b3Lie_center_eq_bot hnc
    let eZ : (↥N ⧸ Subgroup.center ↥N) ≃* ↥N :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact ⟨fun f => (h6 hb).false (eZ.symm.trans f)⟩

section F4Big

set_option linter.unusedSectionVars false


theorem srtOut_reeGamma_F4_inner_gt3 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (y : ReeTag.F4.reeGamma K a) (hy : orderOf y = p) :
    SRTOut 2 (MulAut.conj y) := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨N, hNC, hN2, hall, hcomp, hchev⟩ := largeRee_component_chev ha hK hp hp3 y hy
  have hC := fixSubgroup_conj y
  rw [← hC] at hNC hN2 hall hcomp
  exact srtOut_of_component_data (MulAut.conj y) N hNC hN2 hall hcomp hchev

theorem srtOut_reeGamma_F4 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {β : MulAut (ReeTag.F4.reeGamma K a)} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    SRTOut 2 β := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases reeF4_inner_or_field ha hK hp hβ hβ1 with ⟨y, rfl, hy, hy1⟩ | ⟨σ, g, hσ, rfl⟩
  · exact srtOut_reeGamma_F4_inner_gt3 ha hK hp hp3 y (orderOf_eq_prime hy hy1)
  · exact (srtOut_fieldAut_F4 hK hp (by omega) σ hσ).conj (MulAut.conj g)

theorem srtOut_reeF4 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {S : Type}
    [Group S] [Finite S]
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : SRTOut 2 β := by
  obtain ⟨e0⟩ := he
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e0
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  refine SRTOut.of_congr e ?_
  refine srtOut_reeGamma_F4 ha hK hp hp3 (by rw [← map_pow, hβ, map_one]) ?_
  exact fun h => hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))

end F4Big

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
