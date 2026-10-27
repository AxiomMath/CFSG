module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3Aux2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap TauCeti

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
  {R : QuadraticForm (ZMod 3) W}

structure K3Frame (R : QuadraticForm (ZMod 3) W) where
  z : W
  u : W
  v : W
  hzu : polar R z u = 0
  hzv : polar R z v = 0
  huv : polar R u v = 0
  hz : R z = R u
  huv' : R u = R v
  hne : R u ≠ 0

namespace K3Frame

variable (fr : K3Frame R) (hR : R.Nondegenerate)

theorem polar_uz : polar R fr.u fr.z = 0 := (QuadraticMap.polar_comm R fr.u fr.z).trans fr.hzu

theorem polar_vz : polar R fr.v fr.z = 0 := (QuadraticMap.polar_comm R fr.v fr.z).trans fr.hzv

theorem hau : R (fr.u + fr.z) ≠ 0 := by
  rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, fr.polar_uz, add_zero, fr.hz]
  intro h
  have h2 : (2 : ZMod 3) * R fr.u = 0 := by rw [two_mul]; exact h
  exact fr.hne ((mul_eq_zero.mp h2).resolve_left (by decide))

theorem hbv : R (fr.v + fr.z) ≠ 0 := by
  rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, fr.polar_vz, add_zero, ← fr.huv', fr.hz]
  intro h
  have h2 : (2 : ZMod 3) * R fr.u = 0 := by rw [two_mul]; exact h
  exact fr.hne ((mul_eq_zero.mp h2).resolve_left (by decide))

theorem hau_hbv : R (fr.u + fr.z) = R (fr.v + fr.z) := by
  rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq,
    CFSG.RankThree.OrthogonalInvolutions.map_add_eq, fr.polar_uz, fr.polar_vz, add_zero,
    add_zero, fr.hz, fr.huv']

@[expose] noncomputable def sig : OGroup R :=
  k3Sig fr.z fr.u fr.v fr.hau fr.hbv

theorem sig_cube (hdW : Module.finrank (ZMod 3) W = 3) : fr.sig ^ 3 = 1 :=
  k3_sig_cube fr.z fr.u fr.v hdW fr.hzu fr.hzv fr.huv fr.hz fr.huv' fr.hne fr.hau fr.hbv

theorem sig_mem : fr.sig ∈ omegaGroup hR :=
  reflOf_mul_reflOf_mem_omegaGroup hR _ _ fr.hau fr.hbv fr.hau_hbv

theorem sig_apply_v : ((fr.sig : OGroup R) : W ≃ₗ[ZMod 3] W) fr.v = fr.u :=
  (k3Sig_actions fr.z fr.u fr.v fr.hzu fr.hzv fr.huv fr.hz fr.huv' fr.hne fr.hau fr.hbv).2.2

end K3Frame

theorem fixSp_eq_orthogonal_commSp (hR : R.Nondegenerate) {t : OGroup R} (htt : t * t = 1) :
    fixSp t = LinearMap.BilinForm.orthogonal R.polarBilin (commSp t) := by
  have hB : R.polarBilin.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff).mpr hR
  have hBsymm : R.polarBilin.IsRefl := R.isSymm_polarBilin.isRefl
  have h := congrArg (LinearMap.BilinForm.orthogonal R.polarBilin)
    (commSp_eq_orthogonal_fixSp hR htt)
  rw [LinearMap.BilinForm.orthogonal_orthogonal hB hBsymm] at h
  exact h.symm

end CFSG.OddStandard.SmallF3.Omega