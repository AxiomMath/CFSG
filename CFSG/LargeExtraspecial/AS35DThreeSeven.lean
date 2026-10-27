module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S3Basic
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem polar_eq_zero_of_singular {U : Submodule (ZMod 2) S.Qt}
    (hUs : ∀ x ∈ U, S.q x = 0) {x y : S.Qt} (hx : x ∈ U) (hy : y ∈ U) :
    polar S.q x y = 0 := by
  have h := QuadraticMap.map_add S.q x y
  rw [hUs _ (U.add_mem hx hy), hUs x hx, hUs y hy, zero_add, zero_add] at h
  exact h.symm

section OneIsometry

variable {U : Submodule (ZMod 2) S.Qt} (hUs : ∀ x ∈ U, S.q x = 0) {u : S.Qt} (huU : u ∈ U)
  (hu0 : u ≠ 0) {σ : S.Qt ≃ₗ[ZMod 2] S.Qt} (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q)
  (hc : ∀ c, (∀ x ∈ U, polar S.q x c = 0) → σ c - c ∈ Submodule.span (ZMod 2) {u})
include hUs huU hu0 hc

theorem apply_eq_self_of_sub_mem_span : σ u = u := by
  have h := hc u fun x hx => S.polar_eq_zero_of_singular hUs hx huU
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  rcases zmod2_cases a with rfl | rfl
  · rw [zero_smul, eq_comm, sub_eq_zero] at ha
    exact ha
  · rw [one_smul] at ha
    exfalso
    apply hu0
    have h2 : σ u = u + u := by
      calc σ u = (σ u - u) + u := by abel
        _ = u + u := by rw [← ha]
    rw [CFSG.RankThree.OrthogonalInvolutions.add_self_vec (ZMod 2)] at h2
    have h3 : σ u = σ 0 := by rw [h2, map_zero]
    exact σ.injective h3

include hσ in
theorem polar_sub_eq_zero_of_sub_mem_span (v : S.Qt) : polar S.q u (σ v - v) = 0 := by
  have h1 : polar S.q (σ u) (σ v) = polar S.q u v :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hσ u v
  rw [S.apply_eq_self_of_sub_mem_span hUs huU hu0 hc] at h1
  rw [polar_sub_right, h1, sub_self]

include hσ in
theorem sub_mem_span_of_polar_eq_zero (hU2 : finrank (ZMod 2) U = 2) {y : S.Qt}
    (hy : polar S.q u y = 0) : σ y - y ∈ Submodule.span (ZMod 2) {u} := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hσu := S.apply_eq_self_of_sub_mem_span hUs huU hu0 hc
  by_cases hyC : ∀ x ∈ U, polar S.q x y = 0
  · exact hc y hyC
  push Not at hyC
  obtain ⟨e, heU, he⟩ := hyC
  set d := σ y - y with hd
  have hdU : d ∈ U := by
    have hperp : d ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin
        (LinearMap.BilinForm.orthogonal S.q.polarBilin U) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro c hc'
      have hcU : ∀ x ∈ U, polar S.q x c = 0 := fun x hx => by
        have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hc') x hx
        rwa [polarBilin_apply_apply] at this
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hc c hcU)
      have h1 : polar S.q (σ c) (σ y) = polar S.q c y :=
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hσ c y
      have hσc : σ c = c + a • u := by rw [ha]; abel
      have h2 : polar S.q u (σ y) = polar S.q u y := by
        have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hσ u y
        rwa [hσu] at this
      rw [hσc, polar_add_left, polar_smul_left, h2, hy, smul_zero, add_zero] at h1
      change S.q.polarBilin c d = 0
      rw [polarBilin_apply_apply, hd, polar_sub_right, h1, sub_self]
    rwa [LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl]
      at hperp
  have hdy : polar S.q y d = 0 := by
    have h1 : S.q (σ y) = S.q y := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hσ y
    have h2 : σ y = y + d := by rw [hd]; abel
    rw [h2, QuadraticMap.map_add S.q y d, hUs d hdU, add_zero] at h1
    have h3 : S.q y + polar S.q y d - S.q y = 0 := by rw [h1, sub_self]
    rwa [add_sub_cancel_left] at h3
  have he1 : polar S.q e y = 1 := by
    rcases zmod2_cases (polar S.q e y) with h | h
    · exact absurd h he
    · exact h
  have hli : LinearIndependent (ZMod 2) ![u, e] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : polar S.q (s • u + t • e) y = 0 := by rw [hst, polar_zero_left]
    rw [polar_add_left, polar_smul_left, polar_smul_left, hy, he1, smul_zero, zero_add,
      smul_eq_mul, mul_one] at h1
    subst h1
    rw [zero_smul, add_zero] at hst
    rcases zmod2_cases s with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [one_smul] at hst
      exact absurd hst hu0
  have hspan : Submodule.span (ZMod 2) {u, e} = U := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro w (rfl | rfl)
      · exact huU
      · exact heU
    · have h1 := finrank_span_eq_card hli
      rw [show Set.range ![u, e] = {u, e} by
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
          Set.singleton_union]] at h1
      rw [h1, hU2]
      rfl
  rw [← hspan] at hdU
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hdU
  have h1 : polar S.q y (a • u + b • e) = 0 := by rw [hab]; exact hdy
  rw [polar_add_right, polar_smul_right, polar_smul_right, polar_comm (⇑S.q) y u, hy,
    polar_comm (⇑S.q) y e, he1, smul_zero, zero_add, smul_eq_mul, mul_one] at h1
  rw [h1, zero_smul, add_zero] at hab
  rw [← hab]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self u)

end OneIsometry

theorem commute_of_sub_mem_span {U : Submodule (ZMod 2) S.Qt} (hU2 : finrank (ZMod 2) U = 2)
    (hUs : ∀ x ∈ U, S.q x = 0) {u : S.Qt} (huU : u ∈ U) (hu0 : u ≠ 0)
    {σ₁ σ₂ : S.Qt ≃ₗ[ZMod 2] S.Qt} (h1 : σ₁ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q)
    (h2 : σ₂ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q)
    (hc1 : ∀ c, (∀ x ∈ U, polar S.q x c = 0) → σ₁ c - c ∈ Submodule.span (ZMod 2) {u})
    (hc2 : ∀ c, (∀ x ∈ U, polar S.q x c = 0) → σ₂ c - c ∈ Submodule.span (ZMod 2) {u}) :
    σ₁ * σ₂ = σ₂ * σ₁ := by
  have hσ1u := S.apply_eq_self_of_sub_mem_span hUs huU hu0 hc1
  have hσ2u := S.apply_eq_self_of_sub_mem_span hUs huU hu0 hc2
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, polar S.q u w₀ = 1 := by
    by_contra! h
    apply hu0
    refine S.q_nondegenerate.1 u fun n => ?_
    rw [polarBilin_apply_apply]
    rcases zmod2_cases (polar S.q u n) with h' | h'
    · exact h'
    · exact absurd h' (h n)
  set a := σ₁ w₀ - w₀ with ha
  set b := σ₂ w₀ - w₀ with hb
  have hua : polar S.q u a = 0 := S.polar_sub_eq_zero_of_sub_mem_span hUs huU hu0 h1 hc1 w₀
  have hub : polar S.q u b = 0 := S.polar_sub_eq_zero_of_sub_mem_span hUs huU hu0 h2 hc2 w₀
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp
    (S.sub_mem_span_of_polar_eq_zero hUs huU hu0 h1 hc1 hU2 hub)
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp
    (S.sub_mem_span_of_polar_eq_zero hUs huU hu0 h2 hc2 hU2 hua)
  have hσ1w : σ₁ w₀ = w₀ + a := by rw [ha]; abel
  have hσ2w : σ₂ w₀ = w₀ + b := by rw [hb]; abel
  have hσ1b : σ₁ b = b + c₁ • u := by rw [hc₁]; abel
  have hσ2a : σ₂ a = a + c₂ • u := by rw [hc₂]; abel
  have e1 : c₁ = polar S.q a b := by
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup h1 b w₀
    rw [hσ1b, hσ1w, polar_add_left, polar_add_right, polar_add_right, polar_smul_left,
      polar_smul_left, hw₀, hua, smul_zero, add_zero, smul_eq_mul,
      mul_one] at this
    have h3 : polar S.q b a + c₁ = 0 := by
      calc polar S.q b a + c₁ = (polar S.q b w₀ + polar S.q b a + c₁) - polar S.q b w₀ := by
            ring
        _ = 0 := by rw [this, sub_self]
    rw [polar_comm (⇑S.q) b a] at h3
    rcases zmod2_cases c₁ with h4 | h4 <;> rcases zmod2_cases (polar S.q a b) with h5 | h5 <;>
      rw [h4, h5] at h3 ⊢ <;> first | rfl | exact absurd h3 (by decide)
  have e2 : c₂ = polar S.q a b := by
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup h2 a w₀
    rw [hσ2a, hσ2w, polar_add_left, polar_add_right, polar_add_right, polar_smul_left,
      polar_smul_left, hw₀, hub, smul_zero, add_zero, smul_eq_mul,
      mul_one] at this
    have h3 : polar S.q a b + c₂ = 0 := by
      calc polar S.q a b + c₂ = (polar S.q a w₀ + polar S.q a b + c₂) - polar S.q a w₀ := by
            ring
        _ = 0 := by rw [this, sub_self]
    rcases zmod2_cases c₂ with h4 | h4 <;> rcases zmod2_cases (polar S.q a b) with h5 | h5 <;>
      rw [h4, h5] at h3 ⊢ <;> first | rfl | exact absurd h3 (by decide)
  refine LinearEquiv.ext fun v => ?_
  change σ₁ (σ₂ v) = σ₂ (σ₁ v)
  set s := polar S.q u v with hs
  set v' := v - s • w₀ with hv'
  have hv'u : polar S.q u v' = 0 := by
    rw [hv', polar_sub_right, polar_smul_right, hw₀, smul_eq_mul, mul_one, ← hs, sub_self]
  obtain ⟨e₁, he₁⟩ := Submodule.mem_span_singleton.mp
    (S.sub_mem_span_of_polar_eq_zero hUs huU hu0 h1 hc1 hU2 hv'u)
  obtain ⟨e₂, he₂⟩ := Submodule.mem_span_singleton.mp
    (S.sub_mem_span_of_polar_eq_zero hUs huU hu0 h2 hc2 hU2 hv'u)
  have hσ1v' : σ₁ v' = v' + e₁ • u := by rw [he₁]; abel
  have hσ2v' : σ₂ v' = v' + e₂ • u := by rw [he₂]; abel
  have hv : v = v' + s • w₀ := by rw [hv']; abel
  have L : σ₁ (σ₂ v) = v' + e₂ • u + e₁ • u + s • (w₀ + a + (b + c₁ • u)) := by
    rw [hv, map_add, map_smul, hσ2v', hσ2w, map_add, map_smul, map_add, map_smul, map_add,
      hσ1v', hσ1u, hσ1w, hσ1b]
    abel
  have R : σ₂ (σ₁ v) = v' + e₁ • u + e₂ • u + s • (w₀ + b + (a + c₂ • u)) := by
    rw [hv, map_add, map_smul, hσ1v', hσ1w, map_add, map_smul, map_add, map_smul, map_add,
      hσ2v', hσ2u, hσ2w, hσ2a]
    abel
  rw [L, R, e1, e2]
  module

end Setting

end CFSG.LargeExtraspecial
