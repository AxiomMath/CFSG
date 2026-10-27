module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3Aux6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3Aux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3Aux3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_exists_k3Frame {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W] {R : QuadraticForm (ZMod 3) W} (hR : R.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 3) :
    ∃ fr : K3Frame R, R fr.u = (frameNorm R : ZMod 3) := by
  obtain ⟨z, u, v, hz, huv', hn, hzu, hzv, huv⟩ := k3_frame hR hdim
  exact ⟨⟨z, u, v, hzu, hzv, huv, hz, huv', by rw [hn]; exact frameNorm_ne_zero R⟩, hn⟩

theorem ff_polar_fixSp_commSp (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) {x y : V}
    (hx : x ∈ fixSp t) (hy : y ∈ commSp t) : polar Q x y = 0 := by
  rw [fixSp_eq_orthogonal_commSp hQ htt, LinearMap.BilinForm.mem_orthogonal_iff] at hx
  have h : Q.polarBilin y x = 0 := hx y hy
  rw [QuadraticMap.polarBilin_apply_apply] at h
  rw [QuadraticMap.polar_comm]
  exact h

theorem ff_K3_cover_of_involution (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1) {t : OGroup Q}
    (htt : t * t = 1) {α : ℤˣ} (hty : invType t = (3, α)) :
    ∃ w : ↥(omegaProj hQ),
      w ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)))) ∧
      w * w = 1 ∧ KM0 (projOrthToProjSim Q (w : ProjOrth Q)) ∧
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) (projOrthToProjSim Q (toProj Q t)) a * a⁻¹ = w := by
  have hdimW : Module.finrank (ZMod 3) (commSp t) = 3 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hdimU : Module.finrank (ZMod 3) (fixSp t) = 3 := by
    have := finrank_fixSp_add_finrank_commSp (Q := Q) t
    omega
  have hQU := nondegenerate_restrict_fixSp hQ htt
  have hQW := nondegenerate_restrict_commSp hQ htt
  obtain ⟨frU, hnU⟩ := ff_exists_k3Frame hQU hdimU
  obtain ⟨frW, hnW⟩ := ff_exists_k3Frame hQW hdimW
  have hcc := frameNorm_mul hQ htt hdim hsgn hty
  have hneg : ∀ a b : ZMod 3, a * b = -1 → b = -a := by decide
  have hQu : Q (frU.u : V) = (frameNorm (Q.restrict (fixSp t)) : ZMod 3) := hnU
  have hQv : Q (frU.v : V) = (frameNorm (Q.restrict (fixSp t)) : ZMod 3) :=
    (frU.huv'.symm.trans hnU : _)
  have hQu' : Q (frW.u : V) = -(frameNorm (Q.restrict (fixSp t)) : ZMod 3) :=
    hnW.trans (hneg _ _ hcc)
  have hQv' : Q (frW.v : V) = -(frameNorm (Q.restrict (fixSp t)) : ZMod 3) :=
    (frW.huv'.symm.trans hnW).trans (hneg _ _ hcc)
  have hσΩ : blockHom htt (frU.sig, frW.sig) ∈ omegaGroup hQ := by
    have h : blockHom htt (frU.sig, frW.sig) =
        blockHom htt (frU.sig, 1) * blockHom htt (1, frW.sig) := by
      rw [← map_mul]; simp
    rw [h]
    exact mul_mem (blockHom_left_mem_omegaGroup hQ htt (by omega) (frU.sig_mem hQU))
      (blockHom_right_mem_omegaGroup hQ htt (by omega) (frW.sig_mem hQW))
  have hσ3 : blockHom htt (frU.sig, frW.sig) ^ 3 = 1 := by
    rw [← map_pow, Prod.pow_def]
    simp only [frU.sig_cube hdimU, frW.sig_cube hdimW]
    exact map_one _
  have hσt : blockHom htt (frU.sig, frW.sig) * t = t * blockHom htt (frU.sig, frW.sig) := by
    have h : blockHom htt (frU.sig, frW.sig) ∈ (blockHom htt).range := ⟨_, rfl⟩
    rw [range_blockHom hQ htt] at h
    exact Subgroup.mem_centralizer_singleton_iff.mp h
  have hσv : ((blockHom htt (frU.sig, frW.sig) : OGroup Q) : V ≃ₗ[ZMod 3] V) (frU.v : V) =
      (frU.u : V) := by
    have h := blockHom_apply htt (frU.sig, frW.sig) frU.v 0
    simpa [frU.sig_apply_v] using h
  have hσv' : ((blockHom htt (frU.sig, frW.sig) : OGroup Q) : V ≃ₗ[ZMod 3] V) (frW.v : V) =
      (frW.u : V) := by
    have h := blockHom_apply htt (frU.sig, frW.sig) 0 frW.v
    simpa [frW.sig_apply_v] using h
  exact ff_K3_cover_of_data hQ hdim hsgn htt (frameNorm_ne_zero (Q.restrict (fixSp t)))
    hQu hQv hQu' hQv' frU.huv (ff_polar_fixSp_commSp hQ htt frU.u.2 frW.u.2)
    (ff_polar_fixSp_commSp hQ htt frU.u.2 frW.v.2)
    (ff_polar_fixSp_commSp hQ htt frU.v.2 frW.u.2)
    (ff_polar_fixSp_commSp hQ htt frU.v.2 frW.v.2) frW.huv
    (mem_fixSp_iff.mp frU.u.2) (mem_fixSp_iff.mp frU.v.2)
    ((mem_commSp_iff htt).mp frW.u.2) ((mem_commSp_iff htt).mp frW.v.2)
    hσΩ hσ3 hσt hσv hσv'

end CFSG.OddStandard.SmallF3.Omega
