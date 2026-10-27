module

public import CFSG.ClassicalInvolution.Q3.TL4D4NCOneB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace Trip

variable (T : Trip Q)

theorem no_invariant_ts [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {U : Submodule K V}
    (hdim : 2 * Module.finrank K U = Module.finrank K V) (hts : ∀ x ∈ U, Q x = 0)
    (hinv : ∀ E ∈ T.eich, U.map (E : V →ₗ[K] V) = U) : False := by
  have hinv' : ∀ E ∈ T.eich, ∀ x ∈ U, E x ∈ U := fun E hE x hx => by
    rw [← hinv E hE]
    exact ⟨x, hx, rfl⟩
  have hperp : ∀ u ∈ U, polar Q u T.p = 0 := by
    intro u hu
    have hdW := T.proj_mem u
    obtain ⟨h1, h2', h3⟩ := T.sub_proj_perp h2 u
    have hfix : ∀ E ∈ T.eich, E (T.proj u) = T.proj u := by
      intro E hE
      have hEu : E u = E (T.proj u) + (u - T.proj u) := by
        have e : u = T.proj u + (u - T.proj u) := by abel
        conv_lhs => rw [e]
        rw [map_add, T.eich_fix hE h1 h2' h3]
      have hmem : E (T.proj u) - T.proj u ∈ U := by
        have e : E (T.proj u) - T.proj u = E u - u := by rw [hEu]; abel
        rw [e]
        exact U.sub_mem (hinv' E hE u hu) hu
      exact sub_eq_zero.mp
        (T.eq_zero_of_invariant h2 hts hinv' hmem (sub_mem (T.eich_mem hE hdW) hdW))
    have hd0 := T.eq_zero_of_fixed h2 hdW hfix
    rw [hd0, sub_zero] at h1
    exact h1
  have hts' : ∀ x ∈ U ⊔ Submodule.span K {T.p}, Q x = 0 := by
    intro x hx
    obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [QuadraticMap.map_add Q, hts u hu, map_smul_eq_sq, T.Qp, polar_smul_right_eq,
      hperp u hu]
    ring
  have hle := two_mul_finrank_le hQ hts'
  have heq : U = U ⊔ Submodule.span K {T.p} :=
    Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
  have hpU : T.p ∈ U := by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  exact T.p_ne_zero (T.eq_zero_of_invariant h2 hts hinv' hpU T.p_mem)

theorem exists_singular_perp [Finite K] [FiniteDimensional K V] (hodd : Odd (Nat.card K))
    (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) (hV : 6 ≤ Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ Q v = 0 ∧ polar Q v T.p = 0 ∧ polar Q v T.q = 0 ∧
      polar Q v T.a = 0 := by
  set Wp : Submodule K V := LinearMap.ker (polarBilin Q T.p) ⊓
    LinearMap.ker (polarBilin Q T.q) ⊓ LinearMap.ker (polarBilin Q T.a) with hWp
  have hmem : ∀ {x : V}, x ∈ Wp ↔
      polar Q x T.p = 0 ∧ polar Q x T.q = 0 ∧ polar Q x T.a = 0 := by
    intro x
    simp only [hWp, Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply]
    rw [polar_comm Q T.p x, polar_comm Q T.q x, polar_comm Q T.a x]
    tauto
  have hsup : T.span ⊔ Wp = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have e : x = T.proj x + (x - T.proj x) := by abel
    rw [e]
    exact Submodule.add_mem_sup (T.proj_mem x) (hmem.mpr (T.sub_proj_perp h2 x))
  have hW3 : Module.finrank K T.span ≤ 3 := by
    classical
    have h := finrank_span_finset_le_card (R := K) ({T.p, T.q, T.a} : Finset V)
    have h3 : ({T.p, T.q, T.a} : Finset V).card ≤ 3 := Finset.card_le_three
    simp only [Finset.coe_insert, Finset.coe_singleton] at h
    exact le_trans h h3
  have hdim : 3 ≤ Module.finrank K Wp := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq T.span Wp
    rw [hsup, finrank_top] at h
    omega
  have key : ∀ v : Wp, (∀ w : Wp, polar (Q.comp Wp.subtype) v w = 0) → v = 0 := by
    intro v hv
    refine Subtype.ext (hQ.1 (v : V) fun y => ?_)
    obtain ⟨hp, hq, ha⟩ := hmem.mp v.2
    have e : y = T.proj y + (y - T.proj y) := by abel
    have h1 : polar Q (v : V) (T.proj y) = 0 := T.polar_eq_zero_of_perp hp hq ha (T.proj_mem y)
    have h2'' : polar Q (v : V) (y - T.proj y) = 0 := by
      exact hv ⟨y - T.proj y, hmem.mpr (T.sub_proj_perp h2 y)⟩
    rw [polarBilin_apply_apply, e, polar_add_right, h1, h2'', add_zero]
  have hnd : (polarBilin (Q.comp Wp.subtype)).Nondegenerate :=
    ⟨fun v hv => key v fun w => by simpa using hv w,
      fun w hw => key w fun v => by rw [polar_comm]; simpa using hw v⟩
  obtain ⟨v, hv0, hQv⟩ :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.exists_isotropic_of_three_le hodd
      (Q.comp Wp.subtype) hnd hdim
  obtain ⟨h1, h2', h3⟩ := hmem.mp v.2
  exact ⟨v, fun h => hv0 (Subtype.ext h), hQv, h1, h2', h3⟩

end Trip

end CFSG.ClassicalInvolution.Q3.TL4
