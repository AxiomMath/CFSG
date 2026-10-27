module

public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.SuzukiReeB

open CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

private theorem perfectInLayer_of_isSimpleGroup_fix {S : Type*} [Group S] (β : MulAut S)
    [IsSimpleGroup ↥(fixSubgroup β)] (hnc : ∃ x y : ↥(fixSubgroup β), x * y ≠ y * x) :
    PerfectInLayer β := by
  have hq : CFSG.Open.IsQuasisimple ↥(fixSubgroup β) := b3Lie_isQuasisimple_of_simple hnc
  intro P hP _
  exact hP.trans (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hq⟩)

private theorem exists_noncomm_of_isPerfect (G : Type*) [Group G] [Nontrivial G]
    [Group.IsPerfect G] : ∃ x y : G, x * y ≠ y * x := by
  by_contra hcon
  push_neg at hcon
  exact Group.IsPerfect.not_isMulCommutative G ⟨⟨hcon⟩⟩

private theorem perfectInLayer_of_equiv_suzukiGroup {X : Type*}
    [Group X] {α : MulAut X} {b : ℕ} {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2 ^ (2 * b + 1)) (e : ↥(fixSubgroup α) ≃* suzukiGroup b k) :
    PerfectInLayer α := by
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · subst hb0
    have hfin : Finite (suzukiGroup 0 k) := finite_suzukiGroup hk
    have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
    have hcard := (suzuki_two_normal_five_complement_core_trivial hk2).1
    have hsolv : Group.IsSolvable (suzukiGroup 0 k) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcard]; norm_num)
    refine perfectInLayer_of_isSolvable _ ?_
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨-, hnt, hsimple⟩ := suzuki_simple hb1 hk
    have : Group.IsPerfect (suzukiGroup b k) := (suzuki_perfect hb1 hk).2
    have : IsSimpleGroup ↥(fixSubgroup α) := e.isSimpleGroup
    refine perfectInLayer_of_isSimpleGroup_fix _ ?_
    obtain ⟨x, y, hxy⟩ := exists_noncomm_of_isPerfect (suzukiGroup b k)
    exact ⟨e.symm x, e.symm y, fun h => hxy (e.symm.injective (by simpa using h))⟩

private theorem perfectInLayer_suzukiGroup {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {β : MulAut (suzukiGroup a K)} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    PerfectInLayer β := by
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
    refine perfectInLayer_of_isSolvable _ ?_
    rw [fixSubgroup_conj]
    exact hsolv
  · obtain ⟨σ, h, b, k, _, _, -, -, hk, hconj, ⟨efix⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 β hord hin
    refine LieSemisimple.perfectInLayer_of_congr
      (MulAut.conj h : suzukiGroup a K ≃* suzukiGroup a K) β ?_
    have hφ : MulAut.congr (MulAut.conj h : suzukiGroup a K ≃* suzukiGroup a K) β =
        szFieldAut a K σ := by
      have : MulAut.congr (MulAut.conj h : suzukiGroup a K ≃* suzukiGroup a K) β =
          MulAut.conj h * β * (MulAut.conj h)⁻¹ := rfl
      rw [this, hconj]
    rw [hφ]
    exact perfectInLayer_of_equiv_suzukiGroup hk efix

theorem perfectInLayer_suzuki (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer β := by
  obtain ⟨e⟩ := he
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  refine LieSemisimple.perfectInLayer_of_congr (e.trans θ) β ?_
  refine perfectInLayer_suzukiGroup ha hK hp hp2 (by rw [← map_pow, hβ, map_one]) ?_
  intro h
  exact hβ1 ((MulAut.congr (e.trans θ)).injective (by rw [h, map_one]))

end CFSG.HardMathSupport.Dickson.SuzukiReeB
