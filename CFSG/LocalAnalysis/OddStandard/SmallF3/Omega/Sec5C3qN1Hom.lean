module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGL281Act

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

@[expose] noncomputable def sec5c3q_n1Equiv (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) :
    ProjSim Q ≃* MulAut (omegaProj hQ) :=
  MulEquiv.ofBijective (ffSimOmegaAct hQ (by omega))
    (ffSimOmegaAct_bijective_six_minus hQ hdim hsgn)

@[expose] noncomputable def sec5c3q_n1Psi (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {L : Subgroup G}
    (e : ↥L ⧸ center ↥L ≃* omegaProj hQ) {R : Subgroup G} (hR : R ≤ normalizer (L : Set G)) :
    ↥R →* ProjSim Q :=
  (sec5c3q_n1Equiv hQ hdim hsgn).symm.toMonoidHom.comp (fgThetaE e hR)

theorem sec5c3q_n1Psi_act (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {L : Subgroup G} (e : ↥L ⧸ center ↥L ≃* omegaProj hQ)
    {R : Subgroup G} (hR : R ≤ normalizer (L : Set G)) (r : ↥R) :
    ffSimOmegaAct hQ (by omega) (sec5c3q_n1Psi hQ hdim hsgn e hR r) = fgThetaE e hR r :=
  (sec5c3q_n1Equiv hQ hdim hsgn).apply_symm_apply _

theorem sec5c3q_n1Psi_induces (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {L : Subgroup G} (e : ↥L ⧸ center ↥L ≃* omegaProj hQ)
    {R : Subgroup G} (hR : R ≤ normalizer (L : Set G)) (r : ↥R) :
    InducesViaP L (center ↥L) hQ e (r : G) (sec5c3q_n1Psi hQ hdim hsgn e hR r) := by
  refine ⟨hR r.2, fun l l' hl => ?_⟩
  have hact : fgQuotAct L (Subgroup.inclusion hR r) (QuotientGroup.mk l) =
      QuotientGroup.mk l' := fgQuotAct_mk L _ l l' hl
  have hθ : fgThetaE e hR r (e (QuotientGroup.mk l)) = e (QuotientGroup.mk l') := by
    change (MulAut.congr e) (fgQuotAct L (Subgroup.inclusion hR r)) (e (QuotientGroup.mk l)) = _
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hact]
  calc ((e (QuotientGroup.mk l') : omegaProj hQ) : ProjOrth Q)
      = ((fgThetaE e hR r (e (QuotientGroup.mk l)) : omegaProj hQ) : ProjOrth Q) := by rw [hθ]
    _ = ((ffSimOmegaAct hQ (by omega) (sec5c3q_n1Psi hQ hdim hsgn e hR r)
          (e (QuotientGroup.mk l)) : omegaProj hQ) : ProjOrth Q) := by
        rw [sec5c3q_n1Psi_act]
    _ = projSimAct Q (sec5c3q_n1Psi hQ hdim hsgn e hR r)
          ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q) := coe_ffSimOmegaAct _ _ _ _

theorem sec5c3q_n1Psi_fibre (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {L : Subgroup G} (hL : commutator ↥L = ⊤)
    (e : ↥L ⧸ center ↥L ≃* omegaProj hQ) {R : Subgroup G} (hR : R ≤ normalizer (L : Set G))
    {r r' : ↥R} (h : sec5c3q_n1Psi hQ hdim hsgn e hR r = sec5c3q_n1Psi hQ hdim hsgn e hR r') :
    ((r⁻¹ * r' : ↥R) : G) ∈ centralizer (L : Set G) := by
  have h1 : sec5c3q_n1Psi hQ hdim hsgn e hR (r⁻¹ * r') = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : fgThetaE e hR (r⁻¹ * r') = 1 := by
    rw [← sec5c3q_n1Psi_act hQ hdim hsgn e hR, h1, map_one]
  have h3 : (MulAut.congr e) (fgQuotAct L (Subgroup.inclusion hR (r⁻¹ * r'))) = 1 := h2
  rw [MulEquiv.map_eq_one_iff] at h3
  exact (fgQuotAct_eq_one_iff hL (Subgroup.inclusion hR (r⁻¹ * r'))).mp h3

theorem sec5c3q_n1Psi_sq (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {L : Subgroup G} (e : ↥L ⧸ center ↥L ≃* omegaProj hQ)
    {R : Subgroup G} (hR : R ≤ normalizer (L : Set G)) (hsq : ∀ x ∈ R, x * x = 1) (r : ↥R) :
    sec5c3q_n1Psi hQ hdim hsgn e hR r * sec5c3q_n1Psi hQ hdim hsgn e hR r = 1 := by
  rw [← map_mul]
  have h : r * r = 1 := Subtype.ext (hsq r.1 r.2)
  rw [h, map_one]

end CFSG.OddStandard.SmallF3.Omega
