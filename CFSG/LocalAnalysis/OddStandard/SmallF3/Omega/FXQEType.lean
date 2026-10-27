module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQEDim2V
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZQ6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fx_qe_invType_q8 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {q r s : OGroup Q} (hq : q ∈ omegaGroup hQ) (hr : r ∈ omegaGroup hQ)
    (hyy : (q * q) * (q * q) = 1) (hy1 : q * q ≠ 1) (hyπ : q * q ≠ piOrth Q)
    (hrr : r * r = q * q) (hrq : r * q = q⁻¹ * r) (hss : s * s = q * q)
    (hsq : s * q = q * s) (hsr : s * r = r * s) : invType (q * q) = (4, 1) := by
  rcases m6z_invType_of_q8_lift_six hQ hdim hsgn hq hr hyy hy1 hyπ
      (Or.inl hrr) (Or.inl hrq) with hty | htypi
  · exact hty
  · exfalso
    have hn : Even (Module.finrank (ZMod 3) V) := by rw [hdim]; decide
    have hpi := invType_piOrth_mul_of_even_minus hQ hyy hn hsgn
    have hfst : Module.finrank (ZMod 3) V - invDim (q * q) = 4 := by
      have h := congrArg Prod.fst (hpi.symm.trans htypi)
      simpa only [invType] using h
    rw [hdim] at hfst
    have hle : invDim (q * q) ≤ 6 := by rw [← hdim]; exact invDim_le (q * q)
    exact fx_qe_no_q8_pair (y := q * q) hyy (by omega) rfl hrr hss hrq hsq hsr

end CFSG.OddStandard.SmallF3.Omega
