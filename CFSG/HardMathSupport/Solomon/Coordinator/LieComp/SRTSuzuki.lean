module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSRT
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range fixSubgroup_conj)

theorem srtOut_suzukiGroup {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut (suzukiGroup a K)} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : SRTOut 2 β := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  have hord : orderOf β = p := orderOf_eq_prime hβ hβ1
  by_cases hin : β ∈ inner (suzukiGroup a K)
  · obtain ⟨x, rfl, hxp, hx1⟩ := exists_eq_conj_of_mem_range
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK) hin hβ hβ1
    have hodd : Odd (orderOf x) := by
      rw [orderOf_eq_prime hxp hx1]
      exact hp.odd_of_ne_two hp2
    obtain ⟨hcard, -⟩ :=
      (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).2 x hx1 hodd
    have hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (suzukiGroup a K))) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard
    exact srtOut_of_isSolvable 2 _ (by rw [fixSubgroup_conj]; exact hsolv)
  · obtain ⟨σ, h, b, k, _, _, -, -, hk, hconj, ⟨efix⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 β hord hin
    refine SRTOut.of_congr (MulAut.conj h : suzukiGroup a K ≃* suzukiGroup a K) ?_
    have hφ : MulAut.congr (MulAut.conj h : suzukiGroup a K ≃* suzukiGroup a K) β =
        szFieldAut a K σ := by
      have : MulAut.congr (MulAut.conj h : suzukiGroup a K ≃* suzukiGroup a K) β =
          MulAut.conj h * β * (MulAut.conj h)⁻¹ := rfl
      rw [this, hconj]
    rw [hφ]
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      have hfin0 : Finite (suzukiGroup 0 k) := finite_suzukiGroup hk
      have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
      have hcard := (suzuki_two_normal_five_complement_core_trivial hk2).1
      have hsolv : Group.IsSolvable (suzukiGroup 0 k) :=
        CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcard]; norm_num)
      exact srtOut_of_isSolvable 2 _
        (Group.isSolvable_of_isSolvable_injective (f := efix.toMonoidHom) efix.injective)
    · obtain ⟨hfink, hsk, hnck⟩ := suzukiGroup_simple_nonab hb1 hk
      haveI := hfink
      haveI := hsk
      haveI : IsSimpleGroup ↥(fixSubgroup (szFieldAut a K σ)) := efix.isSimpleGroup
      have hnc : ∃ x y : ↥(fixSubgroup (szFieldAut a K σ)), x * y ≠ y * x := by
        obtain ⟨x, y, hxy⟩ := hnck
        exact ⟨efix.symm x, efix.symm y, fun h => hxy (efix.symm.injective (by
          rw [map_mul, map_mul]
          exact h))⟩
      haveI : Finite ↥(fixSubgroup (szFieldAut a K σ)) := Finite.of_equiv _ efix.symm.toEquiv
      have hcat := nonempty_suzukiGroup_equiv_cat hb1 hk
      refine srtOut_of_derived (szFieldAut a K σ) (N := fixSubgroup (szFieldAut a K σ)) le_rfl
        (by rw [Subgroup.subgroupOf_self]; exact le_top) ?_ ?_ ?_
      · exact b3Lie_isQuasisimple_of_simple hnc
      · exact LieFactorData.of_mulEquiv efix.symm (lieFactorData_suzukiGroup hb1 hk)
      · intro hb
        obtain ⟨c⟩ := hcat
        exact isEmpty_quot_alternating_six_of_equiv_cat hb hnc ⟨_, suzuki_valid hb1⟩ ⟨efix.trans c⟩

theorem srtOut_suzuki (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) {S : Type} [Group S] [Finite S]
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : SRTOut 2 β := by
  obtain ⟨e⟩ := he
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  refine SRTOut.of_congr (e.trans θ) ?_
  refine srtOut_suzukiGroup ha hK hp hp2 (by rw [← map_pow, hβ, map_one]) ?_
  intro h
  exact hβ1 ((MulAut.congr (e.trans θ)).injective (by rw [h, map_one]))

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
