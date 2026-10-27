module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieTits
import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSRT
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.Blueprint (suzukiGroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range fixSubgroup_conj)

section SzRow


private theorem lieRowSz_fixSubgroup_solvable {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) {β : MulAut (suzukiGroup 2 K)} (hβ : β ^ 5 = 1)
    (hβ1 : β ≠ 1) : Group.IsSolvable ↥(fixSubgroup β) := by
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hord : orderOf β = 5 := orderOf_eq_prime hβ hβ1
  have hZ : Subgroup.center (suzukiGroup 2 K) = ⊥ :=
    CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot (by norm_num) hK
  by_cases hin : β ∈ inner (suzukiGroup 2 K)
  · obtain ⟨x, rfl, hxp, hx1⟩ := exists_eq_conj_of_mem_range hZ hin hβ hβ1
    have hodd : Odd (orderOf x) := by
      rw [orderOf_eq_prime hxp hx1]
      exact ⟨2, by norm_num⟩
    obtain ⟨hcard, -⟩ :=
      (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers
        (by norm_num) hK).2 x hx1 hodd
    rw [fixSubgroup_conj]
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard
  · obtain ⟨σ, h, b, k, _, _, -, hb, hk, hconj, ⟨efix⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent 2 (by norm_num) K hK 5 hp hp2 β
        hord hin
    have hb0 : b = 0 := by omega
    subst hb0
    have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
    have hcard := (CFSG.LieType.Ree.suzuki_two_normal_five_complement_core_trivial hk2).1
    haveI : Finite (suzukiGroup 0 k) := CFSG.LieType.Simplicity.finite_suzukiGroup 0 k
    have hsolv : Group.IsSolvable (suzukiGroup 0 k) :=
      CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcard]; norm_num)
    have hfix : Group.IsSolvable ↥(fixSubgroup (szFieldAut 2 K σ)) :=
      Group.isSolvable_of_isSolvable_injective (f := efix.toMonoidHom) efix.injective
    refine CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRT.isSolvable_fixSubgroup_of_congr
      (MulAut.conj h : suzukiGroup 2 K ≃* suzukiGroup 2 K) β ?_
    have hφ : MulAut.congr (MulAut.conj h : suzukiGroup 2 K ≃* suzukiGroup 2 K) β =
        szFieldAut 2 K σ := by
      have : MulAut.congr (MulAut.conj h : suzukiGroup 2 K ≃* suzukiGroup 2 K) β =
          MulAut.conj h * β * (MulAut.conj h)⁻¹ := rfl
      rw [this, hconj]
    rw [hφ]
    exact hfix

theorem kdLieRowSzFive_holds : KDLieRowSzFive := by
  unfold KDLieRowSzFive
  intro hv
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv
  have ha2 : a = 2 := by omega
  subst ha2
  obtain ⟨hfin, hsimp, hncSz⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzukiGroup_simple_nonab (b := 2)
      (by norm_num) hK'
  haveI : Finite (suzukiGroup 2 K) := hfin
  haveI : IsSimpleGroup (suzukiGroup 2 K) := hsimp
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group :=
    Finite.of_equiv _ θ.symm.toEquiv
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group :=
    (MulEquiv.isSimpleGroup_congr θ).mpr hsimp
  have hnc : ∃ a b : (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hncSz
    exact ⟨θ.symm x, θ.symm y, fun h => hxy (by simpa using congrArg θ h)⟩
  have hk : catalogIs (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group (k2 5) :=
    ⟨TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩, by simp [k2, k2Lie], ⟨MulEquiv.refl _⟩⟩
  refine lieRowTits_downLe_two_of_solvable (p := 5) (by norm_num) hnc hk ?_
  intro β hβ hβ1
  refine CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRT.isSolvable_fixSubgroup_of_congr
    θ β ?_
  refine lieRowSz_fixSubgroup_solvable hK' ?_ ?_
  · rw [← map_pow, hβ, map_one]
  · intro h
    exact hβ1 ((MulAut.congr θ).map_eq_one_iff.mp h)

end SzRow

end CFSG.LocalAnalysis.GLTheoremA
