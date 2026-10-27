module

public import CFSG.ClassicalGroups.Alternating.I4SpDefs
public import CFSG.ClassicalGroups.Alternating.RT1SpBasic

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)

variable {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem form_comm_charTwo [CharP K 2] (hBN : BN.IsAlt) (x y : N) : BN x y = BN y x := by
  rw [← hBN.neg_eq x y, CharTwo.neg_eq]

theorem lineElt_eq_Tsp (hBN : BN.IsAlt) (a c : N) :
    lineElt hBN a c = Tsp hBN (a + c) 1 * Tsp hBN c (-1) * Tsp hBN a (-1) := by
  have h : lineElt hBN a c = Ssp hBN a c 0 := rfl
  rw [h, Ssp_eq, zero_sub]

theorem conj_lineElt (hBN : BN.IsAlt) (g : Gsp BN) (a c : N) :
    g * lineElt hBN a c * g⁻¹ = lineElt hBN (g.app a) (g.app c) := by
  rw [lineElt_eq_Tsp, lineElt_eq_Tsp]
  have h : ∀ x y z : Gsp BN,
      g * (x * y * z) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹) :=
    fun x y z => by group
  rw [h, Tsp_conj, Tsp_conj, Tsp_conj, Gsp.map_add]

theorem commute_lineElt_of_app_eq (hBN : BN.IsAlt) {g : Gsp BN} {a c : N} (ha : g.app a = a)
    (hc : g.app c = c) : Commute g (lineElt hBN a c) := by
  have h := conj_lineElt hBN g a c
  rw [ha, hc] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem lineElt_mul_self [CharP K 2] (hBN : BN.IsAlt) {a c : N} (hac : BN a c = 0) :
    lineElt hBN a c * lineElt hBN a c = 1 := by
  refine Gsp.ext' fun x => ?_
  have hca : BN c a = 0 := by rw [← form_comm_charTwo hBN a c, hac]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Gsp.app_mul, lineElt_app hBN hac, lineElt_app hBN hac, Gsp.app_one]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hac,
    hca, hBN.self_eq_zero, mul_zero, add_zero]
  have : x + BN x a • c + BN x c • a + BN x a • c + BN x c • a =
      x + (2 : K) • (BN x a • c + BN x c • a) := by module
  rw [this, h2, zero_smul, add_zero]

theorem lineElt_ne_one (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) {a c : N} (hac : BN a c = 0)
    (hind : LinearIndependent K ![a, c]) : lineElt hBN a c ≠ 1 := by
  intro h
  have ha0 : a ≠ 0 := by simpa using hind.ne_zero (0 : Fin 2)
  apply ha0
  refine hBNnd.2 a fun x => ?_
  have h1 := congrArg (fun g : Gsp BN => g.app x) h
  simp only [lineElt_app hBN hac, Gsp.app_one] at h1
  have h2 : BN x c • a + BN x a • c = 0 := by linear_combination (norm := module) h1
  exact (LinearIndependent.eq_zero_of_pair hind h2).2

end CFSG.ClassicalGroups.Alternating
