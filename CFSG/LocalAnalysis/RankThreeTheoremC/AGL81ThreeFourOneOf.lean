module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open Subgroup

theorem sylow_le_threeFourCore {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (R : Sylow p Y) {E : Subgroup Y} (hER : E ≤ R)
    (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    (R : Subgroup Y) ≤ if 3 ≤ CFSG.pRank p (R : Subgroup Y) then
      CFSG.Open.GLBWeakCore p (R : Subgroup Y) else CFSG.Open.GLBCore p 1 E := by
  haveI : Fact p.Prime := ⟨hp⟩
  split_ifs with h3
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    exact CFSG.PreuniquenessRankFour.Helpers.subgroup_le_weakCore_of_rank p hp _ h3
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    have hpR : p ∣ Nat.card (R : Subgroup Y) :=
      (dvd_pow_self p two_ne_zero).trans (by rw [← hEc]; exact card_dvd_of_le hER)
    haveI : Group.IsNilpotent (R : Subgroup Y) := R.isPGroup'.isNilpotent
    obtain ⟨x, hx⟩ :=
      exists_prime_orderOf_dvd_card' p (Group.IsNilpotent.prime_dvd_card_center hpR)
    set z : Y := ((x : (R : Subgroup Y)) : Y) with hz
    have hzR : z ∈ (R : Subgroup Y) := (x : (R : Subgroup Y)).2
    have hzo : orderOf z = p := by rw [hz, orderOf_coe, orderOf_coe, hx]
    have hzp : z ^ p = 1 := hzo ▸ pow_orderOf_eq_one z
    have hzc : ∀ g ∈ (R : Subgroup Y), g * z = z * g := fun g hg =>
      congrArg Subtype.val (mem_center_iff.mp x.2 ⟨g, hg⟩)
    have hzE : z ∈ E :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free.mem_of_central_of_pRank_le_two hp
        (by omega) hER hE hEc hzR hzp hzc
    have hrank : 1 ≤ CFSG.Open.pRank p (zpowers z) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl (CFSG.Open.isElemAbelian_zpowers hzp)
        (by rw [Nat.card_zpowers, hzo, pow_one])
    have hN : normalizer ((zpowers z : Subgroup Y) : Set Y) ≤ CFSG.Open.GLBCore p 1 E :=
      le_sSup ⟨zpowers z, zpowers_le.mpr hzE, hrank, rfl⟩
    refine fun g hg => hN (centralizer_le_normalizer _ (mem_centralizer_iff.mpr ?_))
    rintro _ ⟨n, rfl⟩
    exact (Commute.zpow_left (hzc g hg).symm n).eq

theorem kFactThreeFourOne_of_signalizerThree (h : KFactNineThreeSignalizerThree) :
    KFactThreeFourOne := by
  intro p Y _ _ K Y₀ E J R hp hp2 hp3 hKn hL _ _ _ hER hE hEc hcore _ hJs hJ3
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hKn
  have hRY₀ : (R : Subgroup Y) ≤ Y₀ := (sylow_le_threeFourCore hp R hER hE hEc).trans hcore
  set θ : Y →* MulAut K := MulAut.conjNormal with hθ
  have hθker : ∀ y : Y, θ y = 1 ↔ y ∈ centralizer (K : Set Y) := by
    intro y
    refine ⟨fun h => mem_centralizer_iff.mpr fun m hm => ?_, fun h => ?_⟩
    · have := congrArg Subtype.val (DFunLike.congr_fun h ⟨m, hm⟩)
      simp only [hθ, MulAut.conjNormal_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    · refine MulEquiv.ext fun m => Subtype.ext ?_
      simp only [hθ, MulAut.conjNormal_apply, MulAut.one_apply]
      rw [(mem_centralizer_iff.mp h m m.2).symm, mul_inv_cancel_right]
  have hJp : IsPGroup 3 (J.map θ) := by
    rintro ⟨_, j, hj, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow]
    exact (hθker _).mpr (hJ3 j hj)
  have hJW : J.map θ ≤ CFSG.Open.pCoreOf 3 (Y₀.map θ) :=
    CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 3 (hJs.map θ) hJp
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hW : CFSG.Open.pCoreOf 3 (Y₀.map θ) = ⊥ := by
    refine h p hp hp2 hp3 K hL T _
      (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 3 _) fun g hg w hw => ?_
    have hgR : (g : Y) ∈ (R : Subgroup Y) ⊓ K := by
      rw [← hT]
      exact mem_map_of_mem K.subtype hg
    have hgθ : MulAut.conj g = θ g := MulAut.conjNormal_val.symm
    rw [hgθ]
    exact (mem_normalizer_iff.mp (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf
      3 _ (mem_map_of_mem θ (hRY₀ hgR.1))) w).mp hw
  intro j hj
  rw [← hθker]
  have hjW := hJW (mem_map_of_mem θ hj)
  rwa [hW, mem_bot] at hjW

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
