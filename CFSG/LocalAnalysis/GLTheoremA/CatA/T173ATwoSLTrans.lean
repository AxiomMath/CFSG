module

public import Mathlib.LinearAlgebra.Determinant

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open Module

private lemma exists_basis_finrank_apply_zero {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    (hA : 0 < Module.finrank K A) {u : A} (hu : u ≠ 0) :
    ∃ b : Basis (Fin (Module.finrank K A)) K A, b ⟨0, hA⟩ = u := by
  classical
  let p : Submodule K A := K ∙ u
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl p
  have hp1 : Module.finrank K p = 1 := by
    dsimp only [p]
    exact finrank_span_singleton hu
  have hfin : Module.finrank K p + Module.finrank K Q = Module.finrank K A :=
    Submodule.finrank_add_eq_of_isCompl hQ
  have hdim : Module.finrank K Q + 1 = Module.finrank K A := by
    rw [← hp1, add_comm]
    exact hfin
  have hli : ∀ (c : K), ∀ x ∈ Q, c • u + x = 0 → c = 0 := by
    intro c x hx h
    have hcuQ : c • u ∈ Q := by
      have h' : c • u = -x := add_eq_zero_iff_eq_neg.mp h
      rw [h']
      exact neg_mem hx
    have hcup : c • u ∈ p := by
      dsimp only [p]
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    have hbot : c • u ∈ (⊥ : Submodule K A) := by
      rw [← hQ.disjoint.eq_bot]
      exact ⟨hcup, hcuQ⟩
    have hzero : c • u = 0 := by simpa using hbot
    rcases smul_eq_zero.mp hzero with hc | hu'
    · exact hc
    · exact absurd hu' hu
  have hsp : ∀ z : A, ∃ c : K, z + c • u ∈ Q := by
    intro z
    have hz : z ∈ p ⊔ Q := by
      rw [hQ.codisjoint.eq_top]
      trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
    have ha' : a ∈ K ∙ u := by simpa only [p] using ha
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha'
    refine ⟨-c, ?_⟩
    have hz' : z + (-c) • u = b := by
      rw [← hab, ← hc, neg_smul]
      abel
    rw [hz']
    exact hb
  let bQ : Basis (Fin (Module.finrank K Q)) K Q := Module.finBasis K Q
  let b' : Basis (Fin (Module.finrank K Q + 1)) K A := Basis.mkFinCons u bQ hli hsp
  refine ⟨b'.reindex (finCongr hdim), ?_⟩
  rw [Basis.reindex_apply, Basis.coe_mkFinCons]
  rfl

theorem lin_two_sl_transitive {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A]
    [FiniteDimensional K A] (hA : 2 ≤ Module.finrank K A) {u w : A} (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ T : A ≃ₗ[K] A, LinearMap.det (T : A →ₗ[K] A) = 1 ∧ T u = w := by
  classical
  have hpos : 0 < Module.finrank K A := by omega
  have hlt : 1 < Module.finrank K A := by omega
  obtain ⟨b, hb⟩ := exists_basis_finrank_apply_zero (K := K) (A := A) hpos hu
  obtain ⟨b', hb'⟩ := exists_basis_finrank_apply_zero (K := K) (A := A) hpos hw
  let i0 : Fin (Module.finrank K A) := ⟨0, hpos⟩
  let i1 : Fin (Module.finrank K A) := ⟨1, hlt⟩
  let T₀ : A ≃ₗ[K] A := b.equiv b' (Equiv.refl (Fin (Module.finrank K A)))
  have hT₀u : T₀ u = w := by
    rw [← hb, ← hb']
    simp [T₀]
  have hdetT₀ : LinearMap.det (T₀ : A →ₗ[K] A) = b.det b' := by
    rw [show (T₀ : A →ₗ[K] A) =
      (b.equiv b' (Equiv.refl (Fin (Module.finrank K A)))).toLinearMap from rfl]
    exact Module.Basis.det_basis b' b
  let cu : Kˣ := (b.isUnit_det b').unit⁻¹
  have hcu : (cu : K) = (b.det b')⁻¹ := by
    simp [cu, IsUnit.unit_spec]
  let w₀ : Fin (Module.finrank K A) → Kˣ := Function.update (fun _ => 1) i1 cu
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  let b'' : Basis (Fin (Module.finrank K A)) K A := b'.unitsSMul w₀
  have hb''0 : b'' i0 = w := by
    change b'.unitsSMul w₀ i0 = w
    rw [Module.Basis.unitsSMul_apply]
    rw [show w₀ i0 = 1 by simp [w₀, Function.update_of_ne h01], one_smul, hb']
  let D : A ≃ₗ[K] A := b'.equiv b'' (Equiv.refl (Fin (Module.finrank K A)))
  have hDw : D w = w := by
    rw [← hb']
    simp only [D, Module.Basis.equiv_apply, Equiv.refl_apply]
    exact hb''0.trans hb'.symm
  have hdetD : LinearMap.det (D : A →ₗ[K] A) = ∏ i, (w₀ i : K) := by
    have h1 : LinearMap.det (D : A →ₗ[K] A) = b'.det b'' := by
      rw [show (D : A →ₗ[K] A) =
        (b'.equiv b'' (Equiv.refl (Fin (Module.finrank K A)))).toLinearMap from rfl]
      exact Module.Basis.det_basis b'' b'
    rw [h1]
    change b'.det (b'.unitsSMul w₀) = ∏ i, (w₀ i : K)
    exact Module.Basis.det_unitsSMul_self b' w₀
  have hprod : ∏ i, (w₀ i : K) = (b.det b')⁻¹ := by
    rw [Fintype.prod_eq_single i1]
    · simp [w₀, hcu]
    · intro j hj
      simp [w₀, Function.update_of_ne hj]
  let T : A ≃ₗ[K] A := T₀.trans D
  refine ⟨T, ?_, ?_⟩
  · have hdetT : LinearMap.det (T : A →ₗ[K] A) =
        LinearMap.det (D : A →ₗ[K] A) * LinearMap.det (T₀ : A →ₗ[K] A) := by
      rw [show (T : A →ₗ[K] A) = (D : A →ₗ[K] A).comp (T₀ : A →ₗ[K] A) from rfl]
      exact LinearMap.det_comp _ _
    rw [hdetT, hdetD, hdetT₀, hprod]
    exact inv_mul_cancel₀ (b.isUnit_det b').ne_zero
  · show T u = w
    simp only [T, LinearEquiv.trans_apply, hT₀u, hDw]

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
