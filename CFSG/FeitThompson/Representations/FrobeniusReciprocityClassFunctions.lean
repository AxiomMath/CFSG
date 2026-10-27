module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open ComplexConjugate

variable {G : Type*} [Group G] (H : Subgroup G)

noncomputable def extendByZero (f : H → ℂ) : G → ℂ := Function.extend H.subtype f 0

@[simp]
theorem extendByZero_apply_coe (f : H → ℂ) (x : H) : extendByZero H f x = f x :=
  H.subtype_injective.extend_apply f 0 x

theorem extendByZero_of_notMem (f : H → ℂ) {g : G} (hg : g ∉ H) : extendByZero H f g = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨a, rfl⟩
  exact hg a.2

theorem extendByZero_apply_dite [DecidablePred (· ∈ H)] (f : H → ℂ) (z : G) :
    extendByZero H f z = if h : z ∈ H then f ⟨z, h⟩ else 0 := by
  by_cases h : z ∈ H
  · rw [dif_pos h]
    exact H.subtype_injective.extend_apply f 0 ⟨z, h⟩
  · rw [dif_neg h]
    exact extendByZero_of_notMem H f h

theorem indClassFun_eq_sum_extendByZero [Fintype G] (f : H → ℂ) (g : G) :
    indClassFun H f g = (Nat.card H : ℂ)⁻¹ * ∑ x : G, extendByZero H f (x⁻¹ * g * x) := by
  classical
  rw [indClassFun_apply]
  congr 1
  exact Finset.sum_congr rfl fun x _ => (extendByZero_apply_dite H f _).symm

def resClassFun (h : G → ℂ) : H → ℂ := fun x => h x

@[simp]
theorem resClassFun_apply (h : G → ℂ) (x : H) : resClassFun H h x = h x := (rfl)

theorem resClassFun_mem_classFun {h : G → ℂ} (hh : h ∈ classFun G) :
    resClassFun H h ∈ classFun H := by
  rw [mem_classFun]
  intro x y hxy
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hc' : (c : G) * (x : G) * ((c : G))⁻¹ = (y : G) := by
    exact_mod_cast congrArg Subtype.val hc
  simp only [resClassFun_apply]
  rw [← hc', classFun.apply_conj hh]

theorem indClassFun_eq_sum_subtype [Fintype G] [DecidablePred (· ∈ H)] (f : H → ℂ) (g : G) :
    indClassFun H f g =
      (Nat.card H : ℂ)⁻¹ * ∑ x : {y : G // y⁻¹ * g * y ∈ H}, f ⟨(x : G)⁻¹ * g * x, x.2⟩ := by
  rw [indClassFun_eq_sum_extendByZero]
  congr 1
  have step1 : ∑ x : G, extendByZero H f (x⁻¹ * g * x)
      = ∑ x : {y : G // y⁻¹ * g * y ∈ H}, extendByZero H f ((x : G)⁻¹ * g * x) := by
    rw [← Finset.sum_subtype (p := fun x : G => x⁻¹ * g * x ∈ H)
      {x ∈ Finset.univ | x⁻¹ * g * x ∈ H} (by simp)
      (fun x : G => extendByZero H f (x⁻¹ * g * x))]
    exact (Finset.sum_filter_of_ne fun x _ hx => by
      by_contra hmem; exact hx (extendByZero_of_notMem H f hmem)).symm
  rw [step1]
  exact Finset.sum_congr rfl fun x _ => extendByZero_apply_coe H f ⟨_, x.2⟩

theorem cfInner_indClassFun [Fintype G] [Fintype H] (f : H → ℂ) {h : G → ℂ}
    (hh : h ∈ classFun G) :
    cfInner (indClassFun H f) h = cfInner f (resClassFun H h) := by
  classical
  have hGne : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have key : ∀ x : G, ∑ g : G, extendByZero H f (x⁻¹ * g * x) * conj (h g)
      = ∑ u : G, extendByZero H f u * conj (h u) := by
    intro x
    refine (Fintype.sum_equiv ((Equiv.mulLeft x).trans (Equiv.mulRight x⁻¹)) _ _ fun u => ?_).symm
    have he : ((Equiv.mulLeft x).trans (Equiv.mulRight x⁻¹)) u = x * u * x⁻¹ := rfl
    rw [he, classFun.apply_conj hh u x, show x⁻¹ * (x * u * x⁻¹) * x = u by group]
  have hsupp : ∑ u : H, f u * conj (resClassFun H h u)
      = ∑ u : G, extendByZero H f u * conj (h u) := by
    have h1 : ∑ u : H, f u * conj (resClassFun H h u)
        = ∑ u : H, extendByZero H f (u : G) * conj (h (u : G)) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [extendByZero_apply_coe, resClassFun_apply]
    rw [h1, ← Finset.sum_subtype (p := fun x : G => x ∈ H) {x ∈ Finset.univ | x ∈ H} (by simp)
      (fun u : G => extendByZero H f u * conj (h u))]
    exact Finset.sum_filter_of_ne fun x _ hx => by
      by_contra hmem
      exact hx (by rw [extendByZero_of_notMem H f hmem, zero_mul])
  rw [cfInner_def, cfInner_def, hsupp]
  have e1 : ∑ g : G, indClassFun H f g * conj (h g)
      = ∑ g : G, ∑ x : G, (Nat.card H : ℂ)⁻¹ * (extendByZero H f (x⁻¹ * g * x) * conj (h g)) := by
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [indClassFun_eq_sum_extendByZero, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => mul_assoc _ _ _
  rw [e1, Finset.sum_comm]
  have e2 : ∑ x : G, ∑ g : G, (Nat.card H : ℂ)⁻¹ * (extendByZero H f (x⁻¹ * g * x) * conj (h g))
      = ∑ _x : G, (Nat.card H : ℂ)⁻¹ * ∑ u : G, extendByZero H f u * conj (h u) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, key x]
  rw [e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    inv_mul_cancel_left₀ hGne]

end

end CFSG.FeitThompson
