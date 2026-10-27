module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3E7Iso
public import CFSG.ClassicalInvolution.Q3.Q3E8BF5

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.F3.E7Three

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Q3.Q3W


local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)
local notation "M₁₂" =>
  CFSG.ClassicalInvolution.Generic.modelUniv StatedLieTag.POmegaPlus 6 3 1 Nat.prime_three

theorem theta_le_centralizer3 {u : M₇} (hu : u ∈ stdRankOne D₇ thetaE7) (hu2 : orderOf u = 2) :
    stdRankOne D₇ thetaE7 ≤ centralizer {u} := by
  have hRθF := e7_fund_class3.2
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : a * u * a⁻¹ ∈ stdRankOne D₇ thetaE7 := mul_mem (mul_mem ha hu) (inv_mem ha)
  have hord : orderOf (a * u * a⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hu2]
  exact mul_inv_eq_iff_eq_mul.1 (eq_of_orderOf_two_fund3 hRθF hmem hu hord hu2)

theorem HJ_le_centralizer3 {u : M₇} (hu : u ∈ stdRankOne D₇ thetaE7) :
    HJ 3 1 ≤ centralizer {u} := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.2 (commutes_HJ_theta3 x hx u hu)

theorem conjSub_theta3 {u : M₇} (hu : u ∈ stdRankOne D₇ thetaE7) (hu2 : orderOf u = 2) {g : M₇}
    (hg : g * u = u * g) : conjSub g (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hRθF := e7_fund_class3.2
  have hεu := εm_involution_std3 isRoot_thetaE7 hu hu2
  have hwd : εm (GaloisField 3 1) g *
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) *
        εm (GaloisField 3 1) g := by
    rw [← hεu, ← map_mul, ← map_mul, hg]
  apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups hRθF g) hRθF
  rw [map_conjSub, map_stdRankOne_εm isRoot_thetaE7,
    map_conj_rootRankOneGroup_of_commute hF (εm_mem g) hwd]

theorem conjSub_HJ_le3 {u : M₇} (hu : u ∈ stdRankOne D₇ thetaE7) (hu2 : orderOf u = 2) {g : M₇}
    (hg : g * u = u * g) : conjSub g (HJ 3 1) ≤ HJ 3 1 := by
  have hθ := conjSub_theta3 hu hu2 hg
  have hC := commutes_HJ_theta3
  have hHJ : HJ 3 1 = ⨆ i : Fin 6, rankOne (e7Datum (GaloisField 3 1)).rootGroup (iota7 i) := rfl
  conv_lhs => rw [hHJ]
  rw [conjSub, Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  change conjSub g (rankOne (e7Datum (GaloisField 3 1)).rootGroup (iota7 i)) ≤ HJ 3 1
  have hA : rankOne (e7Datum (GaloisField 3 1)).rootGroup (iota7 i) ∈
      ClassicalInvolution.Generic.fundamentalSubgroups .E7 D₇ :=
    std_mem_fund3 (isRoot_single .E7 (iota7 i))
  have hcomm : Commutes (stdRankOne D₇ thetaE7)
      (conjSub g (rankOne (e7Datum (GaloisField 3 1)).rootGroup (iota7 i))) := by
    have h1 : Commutes (rankOne (e7Datum (GaloisField 3 1)).rootGroup (iota7 i))
        (stdRankOne D₇ thetaE7) := fun x hx y hy => hC x (rankOne_le_HJ i hx) y hy
    have h2 := h1.symm.conjSub g
    rwa [hθ] at h2
  obtain ⟨h, hh, hX⟩ :=
    exists_mem_HJ_conj_of_commutes_theta3 (conjSub_mem_fundamentalSubgroups hA g) hcomm
  rw [hX]
  calc conjSub h (rankOne (e7Datum (GaloisField 3 1)).rootGroup (e7Idx 6))
      ≤ conjSub h (HJ 3 1) := conjSub_mono (rankOne_le_HJ_of_ne_zero (by decide))
    _ = HJ 3 1 := conjSub_eq_self_of_mem hh

theorem nonempty_theta_equiv3 :
    Nonempty (↥(stdRankOne D₇ thetaE7) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 1)) := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hRθF := e7_fund_class3.2
  let ψ := (εm (GaloisField 3 1)).domRestrict (stdRankOne D₇ thetaE7)
  have hψ : Function.Injective ψ := by
    refine (MonoidHom.ker_eq_bot_iff ψ).1 (eq_bot_iff.2 fun x hx => ?_)
    have h1 : εm (GaloisField 3 1) x = 1 := hx
    exact Subtype.ext (no_central_fund3 hRθF x.2 (εm_ker_le_center h1))
  have hr : ψ.range = rootRankOneGroup .E7 (GaloisField 3 1) thetaE7 := by
    rw [MonoidHom.domRestrict_range, map_stdRankOne_εm isRoot_thetaE7]
  obtain ⟨-, e, -⟩ :=
    (exceptional_Lang_root_rank_one_data .E7 (GaloisField 3 1) thetaE7).2.2.2.2.2.2.2.1 hF
  exact ⟨(MonoidHom.ofInjective hψ).trans ((MulEquiv.subgroupCongr hr).trans e.symm)⟩

theorem spin12_facts3 :
    IsQuasisimple (M₁₂).K ∧ IsPGroup 2 (center (M₁₂).K) ∧
      Blueprint.LieModel ((M₁₂).K ⧸ center (M₁₂).K) .POmegaPlus 6 3 1 :=
  E7Row.spin12_facts (p := 3) (f := 1) (by norm_num) one_ne_zero

theorem hj_facts3 :
    IsQuasisimple ↥(HJ 3 1) ∧ IsPGroup 2 (center ↥(HJ 3 1)) ∧
      Blueprint.LieModel (↥(HJ 3 1) ⧸ center ↥(HJ 3 1)) .POmegaPlus 6 3 1 := by
  obtain ⟨Ψ, hker, hrange, -⟩ := exists_psi_E7_layer3
  obtain ⟨hK, hZ, hL⟩ := spin12_facts3
  rw [← hrange]
  have hs : Function.Surjective Ψ.rangeRestrict := Ψ.rangeRestrict_surjective
  have hk : Ψ.rangeRestrict.ker ≤ center (M₁₂).K := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hne : ∃ x, Ψ.rangeRestrict x ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨-, -, a, b, hab⟩ := hK
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a ∈ center (M₁₂).K := hk (MonoidHom.mem_ker.2 (hall a))
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (mem_center_iff.1 ha b).symm]
  refine ⟨LieType.CurtisTits.isQuasisimple_of_surjective hK hs hne, ?_, ?_⟩
  · rw [LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hK hs hk]
    exact hZ.map _
  · exact LieType.CurtisTits.lieModel_of_mulEquiv
      (LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hK hs hk) hL

end CFSG.ComponentClassification.HarrisLit.T1.P54.F3.E7Three
