module

public import CFSG.LieType.SeitzGeneration.OrthSingular

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] in
theorem exists_mem_orth_not_span {S : Submodule K V} (h3 : 3 ≤ finrank K S) (a : V) :
    ∃ c ∈ S, polar Q a c = 0 ∧ c ∉ Submodule.span K {a} := by
  let φ : V →ₗ[K] K := polarBilin Q a
  have hker : 2 ≤ finrank K ↥(S ⊓ LinearMap.ker φ) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker φ)
    have h2 := Submodule.finrank_le (S ⊔ LinearMap.ker φ)
    have h3' := LinearMap.finrank_range_add_finrank_ker φ
    have h4 : finrank K (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      rwa [Module.finrank_self] at this
    omega
  by_contra hcon
  push Not at hcon
  have hle : S ⊓ LinearMap.ker φ ≤ Submodule.span K {a} := fun c hc =>
    hcon c hc.1 (by simpa [φ, polarBilin_apply_apply] using hc.2)
  have h1 := Submodule.finrank_mono hle
  have h2 : finrank K (Submodule.span K {a}) ≤ 1 := by
    have := finrank_span_finset_le_card (R := K) ({a} : Finset V)
    rwa [Finset.coe_singleton, Finset.card_singleton] at this
  omega

theorem exists_singular_of_three_le_charTwo (h2 : (2 : K) = 0) {S : Submodule K V}
    (h3 : 3 ≤ finrank K S) : ∃ x ∈ S, x ≠ 0 ∧ Q x = 0 := by
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨e, heS, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := S) fun h => by
    rw [h, finrank_bot] at h3
    omega
  by_cases hQe : Q e = 0
  · exact ⟨e, heS, he0, hQe⟩
  obtain ⟨c, hcS, hec, hcspan⟩ := exists_mem_orth_not_span (Q := Q) h3 e
  have hc0 : c ≠ 0 := fun h => hcspan (h ▸ Submodule.zero_mem _)
  by_cases hQc : Q c = 0
  · exact ⟨c, hcS, hc0, hQc⟩
  obtain ⟨y, hy⟩ := isSquare_of_charTwo' (Q e / Q c)
  have hyy : y * y * Q c = Q e := by
    rw [← hy]
    field_simp
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hQe (by rw [← hyy]; ring)
  refine ⟨e + y • c, S.add_mem heS (S.smul_mem _ hcS), fun h => hcspan ?_, ?_⟩
  · have hc : c = (-y⁻¹) • e := by
      have h' : y • c = -e := eq_neg_of_add_eq_zero_right h
      calc c = y⁻¹ • (y • c) := by rw [smul_smul, inv_mul_cancel₀ hy0, one_smul]
        _ = (-y⁻¹) • e := by rw [h', smul_neg, neg_smul]
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
  · rw [QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, hec, mul_zero, add_zero]
    linear_combination hyy + (Q e) * h2

theorem exists_singular_of_three_le_any {S : Submodule K V} (h3 : 3 ≤ finrank K S) :
    ∃ x ∈ S, x ≠ 0 ∧ Q x = 0 := by
  by_cases h2 : (2 : K) = 0
  · exact exists_singular_of_three_le_charTwo h2 h3
  · exact exists_singular_of_three_le_odd h2 h3

theorem exists_singular_in_kernel_any {S : Submodule K V} (h6 : 6 ≤ finrank K S)
    (f : Fin 3 → V →ₗ[K] K) : ∃ s ∈ S, s ≠ 0 ∧ Q s = 0 ∧ ∀ i, f i s = 0 := by
  let Φ : ↥S →ₗ[K] (Fin 3 → K) := LinearMap.pi fun i => (f i).comp S.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hrange : finrank K Φ.range ≤ 3 := by
    have := Submodule.finrank_le Φ.range
    simpa using this
  set U : Submodule K V := (LinearMap.ker Φ).map S.subtype with hU
  have hUdim : 3 ≤ finrank K U := by
    have hinj : Function.Injective S.subtype := S.injective_subtype
    have : finrank K U = finrank K (LinearMap.ker Φ) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective S.subtype hinj (LinearMap.ker Φ))).symm
    omega
  obtain ⟨s, hsU, hs0, hsQ⟩ := exists_singular_of_three_le_any (Q := Q) hUdim
  obtain ⟨s', hs', rfl⟩ := Submodule.mem_map.mp hsU
  refine ⟨(s' : V), s'.2, hs0, hsQ, fun i => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hs') i
  simpa [Φ] using this

end CFSG.LieType.SeitzGeneration.OrthBlk
