module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.ClassicalGroups.Orthogonal.NormClass.Plane
import CFSG.ClassicalGroups.Orthogonal.TwoHyperplanes.Generation
import CFSG.LieType.Universal.SpinOmega.Reflections
import CFSG.ClassicalGroups.Orthogonal.Represents

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem exists_polar_eq_zero_map_eq_neg [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {S : Submodule K V} (hS : PolarNondegOn Q S) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (hab : Q a = Q b) (hQa : Q a ≠ 0) (hB : polar Q a b = 2 * Q a) (hi : a - b ≠ 0) :
    ∃ w ∈ S, Q w = Q a ∧ polar Q a w = 0 ∧ polar Q w b = -Q a := by
  set i : V := a - b with hi_def
  have hi' : i ≠ 0 := by rw [hi_def]; exact hi
  have hiS : i ∈ S := S.sub_mem ha hb
  have hQi : Q i = 0 := by
    rw [hi_def, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right,
      ← hab, hB]; ring
  have hai : polar Q a i = 0 := by
    rw [hi_def, polar_sub_right, polar_self_eq_two_mul, hB]; ring
  have hT : PolarNondegOn Q (S ⊓ LinearMap.ker (polarBilin Q a)) :=
    PolarNondegOn.inf_ker h2 hS ha hQa
  have hiT : i ∈ S ⊓ LinearMap.ker (polarBilin Q a) := by
    refine ⟨hiS, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply]
    exact hai
  obtain ⟨j₀, hj₀T, hj₀⟩ := hT.exists_polar_ne_zero hiT hi'
  have hj₀a : polar Q a j₀ = 0 := by
    have h := hj₀T.2
    rwa [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply] at h
  set j : V := (polar Q i j₀)⁻¹ • j₀ with hj_def
  have hi_j : polar Q i j = 1 := by
    rw [hj_def, polar_smul_right_eq, inv_mul_cancel₀ hj₀]
  have ha_j : polar Q a j = 0 := by
    rw [hj_def, polar_smul_right_eq, hj₀a, mul_zero]
  have hjS : j ∈ S := S.smul_mem _ hj₀T.1
  set w : V := (1 - Q a * Q j) • i + Q a • j with hw
  have hwS : w ∈ S := by
    rw [hw]
    exact S.add_mem (S.smul_mem _ hiS) (S.smul_mem _ hjS)
  have hQw : Q w = Q a := by
    rw [hw, QuadraticMap.map_add Q, map_smul_eq_sq Q (1 - Q a * Q j) i,
      map_smul_eq_sq Q (Q a) j, polar_smul_left_eq Q (1 - Q a * Q j) i (Q a • j),
      polar_smul_right_eq Q (Q a) i j, hQi, hi_j]
    ring
  have haw : polar Q a w = 0 := by
    rw [hw, polar_add_right, polar_smul_right_eq Q (1 - Q a * Q j) a i,
      polar_smul_right_eq Q (Q a) a j, hai, ha_j]
    ring
  have hwi : polar Q w i = Q a := by
    rw [hw, polar_add_left, polar_smul_left_eq Q (1 - Q a * Q j) i i,
      polar_smul_left_eq Q (Q a) j i, polar_self_eq_zero hQi, polar_comm Q j i, hi_j]
    ring
  have hwb : polar Q w b = -Q a := by
    have hb_eq : b = a - i := by rw [hi_def]; abel
    rw [hb_eq, polar_sub_right, polar_comm Q w a, haw, hwi]
    ring
  exact ⟨w, hwS, hQw, haw, hwb⟩

private theorem reflect_mul_reflect_mem_closure_of_polar_eq [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {S : Submodule K V} (hS : PolarNondegOn Q S)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hab : Q a = Q b) (hQa : Q a ≠ 0)
    (hB : polar Q a b = 2 * Q a) {c : K} (hc : c ≠ 0) :
    reflect Q a * reflect Q b ∈ Subgroup.closure (reflect Q '' {x | x ∈ S ∧ Q x = c}) := by
  by_cases hi : a - b = 0
  · have hab' : a = b := sub_eq_zero.mp hi
    rw [hab', reflect_mul_self Q b]
    exact Subgroup.one_mem _
  · obtain ⟨w, hwS, hQw, haw, hwb⟩ :=
      exists_polar_eq_zero_map_eq_neg h2 hS ha hb hab hQa hB hi
    set X := Subgroup.closure (reflect Q '' {x | x ∈ S ∧ Q x = c}) with hX
    have h4 : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num]
      exact mul_ne_zero h2 h2
    have h1 : reflect Q a * reflect Q w ∈ X := by
      refine reflect_mul_reflect_mem_closure_of_sq_ne h2 ha hwS ?_ ?_ hc
      · rw [hQw]
      · rw [haw, hQw]
        have h4a : (4 : K) * Q a * Q a ≠ 0 := mul_ne_zero (mul_ne_zero h4 hQa) hQa
        intro h
        exact h4a (by simpa using h.symm)
    have hQb : Q b ≠ 0 := by rw [← hab]; exact hQa
    have hsq : Q b ^ 2 ≠ 4 * Q b * Q b := by
      intro h
      have h3b : (3 : K) * Q b ^ 2 ≠ 0 := mul_ne_zero h3 (pow_ne_zero 2 hQb)
      apply h3b
      have hkey : (4 : K) * Q b * Q b - Q b ^ 2 = 3 * Q b ^ 2 := by ring
      rw [← hkey, ← h, sub_self]
    have h2' : reflect Q w * reflect Q b ∈ X := by
      refine reflect_mul_reflect_mem_closure_of_sq_ne h2 hwS hb ?_ ?_ hc
      · rw [hQw, ← hab]
      · rw [hwb, hQw, hab]
        simpa [neg_sq] using hsq
    have hmul : (reflect Q a * reflect Q w) * (reflect Q w * reflect Q b) =
        reflect Q a * reflect Q b := by
      rw [show (reflect Q a * reflect Q w) * (reflect Q w * reflect Q b) =
          reflect Q a * (reflect Q w * reflect Q w) * reflect Q b from by group]
      rw [reflect_mul_self Q w, mul_one]
    rw [← hmul]
    exact X.mul_mem h1 h2'

theorem reflect_mul_reflect_mem_closure_of_map_eq [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {S : Submodule K V} (hS : PolarNondegOn Q S) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) (hab : Q a = Q b) {c : K} (hc : c ≠ 0) :
    reflect Q a * reflect Q b ∈ Subgroup.closure (reflect Q '' {x | x ∈ S ∧ Q x = c}) := by
  by_cases hQa : Q a = 0
  · have hQb : Q b = 0 := by rw [← hab]; exact hQa
    rw [reflect_of_map_eq_zero hQa, reflect_of_map_eq_zero hQb, one_mul]
    exact Subgroup.one_mem _
  · by_cases hd : polar Q a b ^ 2 = 4 * Q a * Q b
    · have hd' : polar Q a b ^ 2 = 4 * Q a * Q a := by simpa only [← hab] using hd
      have hfac : (polar Q a b - 2 * Q a) * (polar Q a b + 2 * Q a) = 0 := by
        have hkey : (polar Q a b - 2 * Q a) * (polar Q a b + 2 * Q a) =
            polar Q a b ^ 2 - 4 * Q a * Q a := by ring
        rw [hkey, hd', sub_self]
      rcases mul_eq_zero.mp hfac with h | h
      · have hB : polar Q a b = 2 * Q a := sub_eq_zero.mp h
        exact reflect_mul_reflect_mem_closure_of_polar_eq h2 h3 hS ha hb hab hQa hB hc
      · have hneg : reflect Q (-b) = reflect Q b := by
          have hsmul := CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero (Q := Q)
            (t := (-1 : K)) (by norm_num) b
          simpa using hsmul
        have hB' : polar Q a (-b) = 2 * Q a := by
          rw [polar_neg_right]
          have h' : polar Q a b = -(2 * Q a) := eq_neg_of_add_eq_zero_left h
          rw [h', neg_neg]
        have hmem := reflect_mul_reflect_mem_closure_of_polar_eq h2 h3 hS ha
          (S.neg_mem hb) (by rw [QuadraticMap.map_neg]; exact hab) hQa hB' hc
        rwa [hneg] at hmem
    · exact reflect_mul_reflect_mem_closure_of_sq_ne h2 ha hb hab hd hc

theorem reflect_mul_reflect_mem_closure_reflect [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) {a b : V}
    (hab : Q a = Q b) {c : K} (hc : c ≠ 0) :
    reflect Q a * reflect Q b ∈ Subgroup.closure (reflect Q '' {x | Q x = c}) := by
  have h := reflect_mul_reflect_mem_closure_of_map_eq (S := ⊤) h2 h3
    (polarNondegOn_top hQ) Submodule.mem_top Submodule.mem_top hab hc
  simpa only [Submodule.mem_top, true_and] using h

theorem commutator_orthogonalGroup_le_closure_reflect [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) {c : K}
    (hc : c ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      Subgroup.closure (reflect Q '' {x | Q x = c}) := by
  exact commutator_orthogonalGroup_le_of_reflect_mul_reflect_mem h2 hQ
    (fun a b hab => reflect_mul_reflect_mem_closure_reflect h2 h3 hQ hab hc)

private theorem exists_mem_apply_eq_of_map_sub_eq_zero
    (h2 : (2 : K) ≠ 0) {X : Subgroup (V ≃ₗ[K] V)}
    (hX : ∀ a b : V, Q a = Q b → reflect Q a * reflect Q b ∈ X)
    {e u : V} (he : Q e ≠ 0) (hu : Q u = Q e) (hQeu : Q (e - u) = 0) :
    ∃ k ∈ X, k e = u := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hQsub : Q (e - u) = Q e + Q u - polar Q e u := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right]
    ring
  have hB : polar Q e u = Q e + Q u := by
    have h : Q e + Q u - polar Q e u = 0 := by rw [← hQsub, hQeu]
    exact (sub_eq_zero.mp h).symm
  have hsum : Q (e + u) = 4 * Q e := by
    rw [QuadraticMap.map_add Q, hB, hu]
    ring
  have hBsum : polar Q (e + u) e = Q (e + u) := by
    rw [polar_add_left, polar_self_eq_two_mul, polar_comm Q u e, hB, hu, hsum]
    ring
  have hsum_ne : Q (e + u) ≠ 0 := by
    rw [hsum]
    exact mul_ne_zero h4 he
  have hru : reflect Q (e + u) e = -u := by
    rw [reflect_apply hsum_ne, hBsum, div_self hsum_ne, one_smul]
    abel
  have hQu : Q u ≠ 0 := by rw [hu]; exact he
  have hru_neg : reflect Q u (-u) = u := by
    rw [reflect_apply hQu, polar_neg_right, polar_self_eq_two_mul, neg_div,
      mul_div_cancel_right₀ _ hQu, neg_smul, sub_neg_eq_add, two_smul]
    abel
  have h2inv : (2 : K)⁻¹ ≠ 0 := inv_ne_zero h2
  set a : V := (2 : K)⁻¹ • (e + u) with ha
  have haQ : Q a = Q u := by
    rw [ha, map_smul_eq_sq, hsum, hu]
    have hcoef : ((2 : K)⁻¹) ^ 2 * (4 : K) = 1 := by
      calc ((2 : K)⁻¹) ^ 2 * (4 : K) = ((2 : K)⁻¹ * 2) * ((2 : K)⁻¹ * 2) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ h2, one_mul]
    rw [← mul_assoc, hcoef, one_mul]
  have hra : reflect Q a = reflect Q (e + u) := by
    rw [ha]
    exact CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero h2inv (e + u)
  refine ⟨reflect Q u * reflect Q a, hX u a haQ.symm, ?_⟩
  rw [LinearEquiv.mul_apply, hra, hru, hru_neg]

private theorem exists_mem_apply_eq_of_map_sub_ne_zero [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 3 ≤ Module.finrank K V) {X : Subgroup (V ≃ₗ[K] V)}
    (hX : ∀ a b : V, Q a = Q b → reflect Q a * reflect Q b ∈ X)
    {e u : V} (he : Q e ≠ 0) (hu : Q u = Q e) (hQeu : Q (e - u) ≠ 0) :
    ∃ k ∈ X, k e = u := by
  have hQu : Q u ≠ 0 := by rw [hu]; exact he
  have hQsub : Q (e - u) = Q e + Q u - polar Q e u := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right]
    ring
  have hB : polar Q (e - u) e = Q (e - u) := by
    rw [hQsub, polar_sub_left, polar_self_eq_two_mul, hu, polar_comm Q u e]
    ring
  have hru : reflect Q (e - u) e = u := by
    rw [reflect_apply hQeu, hB, div_self hQeu, one_smul]
    abel
  have hT : PolarNondegOn Q (⊤ ⊓ LinearMap.ker (polarBilin Q u)) :=
    PolarNondegOn.inf_ker h2 (polarNondegOn_top hQ) Submodule.mem_top hQu
  have hfr := finrank_inf_ker_polarBilin_add_one h2 (S := ⊤) (u := u) Submodule.mem_top hQu
  rw [finrank_top] at hfr
  have hdimT : 2 ≤ Module.finrank K ↥(⊤ ⊓ LinearMap.ker (polarBilin Q u)) := by omega
  obtain ⟨b, hbT, hQb⟩ := PolarNondegOn.exists_map_eq (Q := Q) h2 hT hdimT (Q (e - u))
  have hub : polar Q u b = 0 := by
    have h := hbT.2
    rwa [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply] at h
  have hbu : polar Q b u = 0 := by rw [polar_comm]; exact hub
  have hrb : reflect Q b u = u := reflect_apply_of_polar_eq_zero hbu
  refine ⟨reflect Q b * reflect Q (e - u), hX b (e - u) hQb, ?_⟩
  rw [LinearEquiv.mul_apply, hru, hrb]

theorem exists_mem_apply_eq_of_reflect_mul_reflect_mem [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank K V)
    {X : Subgroup (V ≃ₗ[K] V)} (hX : ∀ a b : V, Q a = Q b → reflect Q a * reflect Q b ∈ X)
    {e u : V} (he : Q e ≠ 0) (hu : Q u = Q e) : ∃ k ∈ X, k e = u := by
  by_cases hQeu : Q (e - u) = 0
  · exact exists_mem_apply_eq_of_map_sub_eq_zero h2 hX he hu hQeu
  · exact exists_mem_apply_eq_of_map_sub_ne_zero h2 hQ hdim hX he hu hQeu

end CFSG.ClassicalGroups.Orthogonal

end
