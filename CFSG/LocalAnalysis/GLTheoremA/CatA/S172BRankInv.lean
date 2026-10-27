module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem sq_reflect_mul_reflect {a c : V} (hac : polar Q a c = 0) :
    (reflect Q a * reflect Q c) ^ 2 = 1 := by
  rw [(reflect_commute_of_polar_eq_zero hac).mul_pow, pow_two, pow_two, reflect_mul_self,
    reflect_mul_self, one_mul]

theorem reflect_mul_reflect_conj_rot {a b c : V} (hac : polar Q a c = 0) (hbc : polar Q b c = 0) :
    reflect Q a * reflect Q c * rot Q a b * (reflect Q a * reflect Q c)⁻¹ = (rot Q a b)⁻¹ := by
  have h1 := reflect_commute_of_polar_eq_zero hac
  have h2 := reflect_commute_of_polar_eq_zero hbc
  have hcx : Commute (reflect Q c) (rot Q a b) := h1.symm.mul_right h2.symm
  have hconj : reflect Q c * rot Q a b * (reflect Q c)⁻¹ = rot Q a b := by
    rw [hcx.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc reflect Q a * reflect Q c * rot Q a b * (reflect Q a * reflect Q c)⁻¹
      = reflect Q a * (reflect Q c * rot Q a b * (reflect Q c)⁻¹) * (reflect Q a)⁻¹ := by group
    _ = reflect Q a * rot Q a b * (reflect Q a)⁻¹ := by rw [hconj]
    _ = (rot Q a b)⁻¹ := by
        rw [rot, mul_inv_rev, reflect_inv, reflect_inv]
        simp only [← mul_assoc, reflect_mul_self, one_mul]

theorem commute_reflect_mul_reflect_rot {a c a' b' : V} (h1 : polar Q a a' = 0)
    (h2 : polar Q a b' = 0) (h3 : polar Q c a' = 0) (h4 : polar Q c b' = 0) :
    Commute (reflect Q a * reflect Q c) (rot Q a' b') := by
  unfold rot
  exact Commute.mul_left
    (Commute.mul_right (reflect_commute_of_polar_eq_zero h1) (reflect_commute_of_polar_eq_zero h2))
    (Commute.mul_right (reflect_commute_of_polar_eq_zero h3) (reflect_commute_of_polar_eq_zero h4))

end CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

end
