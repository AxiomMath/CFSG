module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54E7D6
public import CFSG.LieType.HighestRoot.CentTrialityThree
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.E7Row

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem conjSub_mem_fund {R : Subgroup M₇}
    (hR : R ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups .E7 D₇) (g : M₇) :
    conjSub g R ∈ CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups .E7 D₇ := by
  obtain ⟨h, γ, hγ, rfl⟩ := hR
  refine ⟨g * h, γ, hγ, ?_⟩
  rw [conjSub, Subgroup.map_map]
  congr 1

theorem theta_le_centralizer (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {u : M₇}
    (hu : u ∈ stdRankOne D₇ thetaE7) (hu2 : orderOf u = 2) :
    stdRankOne D₇ thetaE7 ≤ centralizer {u} := by
  obtain ⟨-, hRθF, -⟩ := e7_fund_class hp2 hq
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : a * u * a⁻¹ ∈ stdRankOne D₇ thetaE7 :=
    mul_mem (mul_mem ha hu) (inv_mem ha)
  have hord : orderOf (a * u * a⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu2]
  exact mul_inv_eq_iff_eq_mul.1 (eq_of_orderOf_two_fund hp2 hq hRθF hmem hu hord hu2)

theorem HJ_le_centralizer (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {u : M₇}
    (hu : u ∈ stdRankOne D₇ thetaE7) : HJ p f ≤ centralizer {u} := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.2 (commutes_HJ_theta hp2 hq x hx u hu)

theorem conjSub_theta (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {u : M₇}
    (hu : u ∈ stdRankOne D₇ thetaE7) (hu2 : orderOf u = 2) {g : M₇} (hg : g * u = u * g) :
    conjSub g (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 := by
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨-, hRθF, hperf⟩ := e7_fund_class hp2 hq
  have hεu := εm_involution_std hp2 hq isRoot_thetaE7 hu hu2
  have hwd : εm (GaloisField p f) g *
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) *
        εm (GaloisField p f) g := by
    rw [← hεu, ← map_mul, ← map_mul, hg]
  apply eq_of_map_εm_eq (by rw [conjSub_commutator, hperf _ hRθF]) (hperf _ hRθF)
  rw [map_conjSub, map_stdRankOne_εm isRoot_thetaE7,
    map_conj_rootRankOneGroup_of_commute hF (εm_mem g) hwd]

theorem conjSub_HJ_le (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {u : M₇}
    (hu : u ∈ stdRankOne D₇ thetaE7) (hu2 : orderOf u = 2) {g : M₇} (hg : g * u = u * g) :
    conjSub g (HJ p f) ≤ HJ p f := by
  have hθ := conjSub_theta hp2 hq hu hu2 hg
  have hC := commutes_HJ_theta hp2 hq
  have hHJ : HJ p f = ⨆ i : Fin 6, rankOne (e7Datum (GaloisField p f)).rootGroup (iota7 i) := rfl
  conv_lhs => rw [hHJ]
  rw [conjSub, Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  change conjSub g (rankOne (e7Datum (GaloisField p f)).rootGroup (iota7 i)) ≤ HJ p f
  have hA : rankOne (e7Datum (GaloisField p f)).rootGroup (iota7 i) ∈
      CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups .E7 D₇ :=
    std_mem_fund hq (isRoot_single .E7 (iota7 i))
  have hcomm : Commutes (stdRankOne D₇ thetaE7)
      (conjSub g (rankOne (e7Datum (GaloisField p f)).rootGroup (iota7 i))) := by
    have h1 : Commutes (rankOne (e7Datum (GaloisField p f)).rootGroup (iota7 i))
        (stdRankOne D₇ thetaE7) := fun x hx y hy => hC x (rankOne_le_HJ i hx) y hy
    have h2 := h1.symm.conjSub g
    rwa [hθ] at h2
  obtain ⟨h, hh, hX⟩ := exists_mem_HJ_conj_of_commutes_theta hp2 hq (conjSub_mem_fund hA g) hcomm
  rw [hX]
  calc conjSub h (rankOne (e7Datum (GaloisField p f)).rootGroup (e7Idx 6))
      ≤ conjSub h (HJ p f) := conjSub_mono (rankOne_le_HJ_of_ne_zero (by decide))
    _ = HJ p f := conjSub_eq_self_of_mem hh

theorem nonempty_theta_equiv (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Nonempty (↥(stdRankOne D₇ thetaE7) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p f)) := by
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨-, hRθF, -⟩ := e7_fund_class hp2 hq
  let ψ := (εm (GaloisField p f)).domRestrict (stdRankOne D₇ thetaE7)
  have hψ : Function.Injective ψ := by
    refine (MonoidHom.ker_eq_bot_iff ψ).1 (eq_bot_iff.2 fun x hx => ?_)
    have h1 : εm (GaloisField p f) x = 1 := hx
    exact Subtype.ext (no_central_fund hp2 hq hRθF x.2 (εm_ker_le_center h1))
  have hr : ψ.range = rootRankOneGroup .E7 (GaloisField p f) thetaE7 := by
    rw [MonoidHom.domRestrict_range, map_stdRankOne_εm isRoot_thetaE7]
  obtain ⟨-, e, -⟩ :=
    (exceptional_Lang_root_rank_one_data .E7 (GaloisField p f) thetaE7).2.2.2.2.2.2.2.1 hF
  exact ⟨(MonoidHom.ofInjective hψ).trans ((MulEquiv.subgroupCongr hr).trans e.symm)⟩

end CFSG.ComponentClassification.HarrisLit.T1.P54.E7Row
