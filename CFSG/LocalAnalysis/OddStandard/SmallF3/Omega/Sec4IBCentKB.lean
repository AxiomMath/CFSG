module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBCentKLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBCentKG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4I_centK_B0 (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) {v w : Fin 7 → ZMod 2}
    (hv : IsEvenVec v) (hv6 : vecWeight v = 6) (hw : IsEvenVec w) {y : ProjOrth Q}
    (hy : orderOf y = 7) (hyv : y * sec4IPsi fr v = sec4IPsi fr v * y)
    (hyw : y * sec4IPsi fr w = sec4IPsi fr w * y) : w = 0 ∨ w = v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨g, hgy, hg7⟩ := sec4I_exists_lift_pow7 (y := y) (by rw [← hy]; exact pow_orderOf_eq_one y)
  have hgv : g * sec4IT fr v = sec4IT fr v * g :=
    sec4I_comm_T_of_comm_psi hQ fr v (by rw [hgy]; exact hyv)
  have hgw : g * sec4IT fr w = sec4IT fr w * g :=
    sec4I_comm_T_of_comm_psi hQ fr w (by rw [hgy]; exact hyw)
  have hg1 : g = 1 := sec4I_eq_one_of_pow_seven fr hv hv6 hw hcon.1 hcon.2 hg7 hgv hgw
  rw [hg1, map_one] at hgy
  rw [← hgy, orderOf_one] at hy
  exact absurd hy (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
