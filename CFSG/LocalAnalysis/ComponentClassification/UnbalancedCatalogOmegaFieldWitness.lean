module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticRankTwoCounts

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin Module

namespace FieldWitness

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K ≃+* K}

theorem exists_fixed_sq_eq [Finite K] [CharP K 2] {x : K} (hx : σ x = x) :
    ∃ b : K, σ b = b ∧ b ^ 2 = x := by
  obtain ⟨b, hb⟩ := exists_sq_eq_charTwo x
  refine ⟨b, eq_of_sq_eq_sq_charTwo ?_, hb⟩
  rw [← map_pow, hb, hx]

theorem exists_fixed_orthonormal_pair [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1) {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate)
    (hV : 3 ≤ finrank K V) {T : V →ₛₗ[(σ : K →+* K)] V} (hTT : ∀ v, T (T v) = v)
    (hTQ : ∀ v, Q (T v) = σ (Q v)) :
    ∃ u v : V, T u = u ∧ T v = v ∧ Q u = 1 ∧ Q v = 1 ∧ polar Q u v = 0 ∧
      LinearIndependent K ![u, v] := by
  have hσσ' : ∀ a, σ (σ a) = a := fun a => by
    change (σ * σ) a = a
    rw [hσσ]
    rfl
  obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
    by_contra! h
    exact hσ1 (RingEquiv.ext h)
  have hspan := span_fixSpace hσσ' hTT hc
  obtain ⟨w, hwT, hw0⟩ : ∃ w, T w = w ∧ Q w ≠ 0 := by
    by_contra! h0
    have hpol : ∀ w, T w = w → ∀ x, polar Q w x = 0 := by
      intro w hw x
      have hx : x ∈ Submodule.span K (fixSpace T : Set V) := hspan ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy =>
        have hy' : T y = y := hy
        rw [polar, h0 _ (by rw [map_add, hw, hy']), h0 w hw, h0 y hy', sub_zero, sub_zero]
      | zero => exact polar_zero_right Q _
      | add x y _ _ hx hy => rw [polar_add_right, hx, hy, add_zero]
      | smul a x _ hx => rw [polar_smul_right_eq, hx, mul_zero]
    have hbot : Submodule.span K (fixSpace T : Set V) = ⊥ := by
      rw [Submodule.span_eq_bot]
      exact fun w hw => eq_zero_of_polar_eq_zero hQ (hpol w hw)
    have h1 : finrank K V = 0 := by
      rw [← finrank_top K V, ← hspan, hbot, finrank_bot]
    omega
  have hσw : σ (Q w)⁻¹ = (Q w)⁻¹ := by rw [map_inv₀, ← hTQ, hwT]
  obtain ⟨a, haσ, ha⟩ := exists_fixed_sq_eq hσw
  set u := a • w with hudef
  have huT : T u = u := by
    rw [hudef, map_smulₛₗ, RingEquiv.coe_toRingHom, haσ, hwT]
  have hu : Q u = 1 := by
    rw [hudef, QuadraticMap.map_smul, smul_eq_mul, ← pow_two, ha, inv_mul_cancel₀ hw0]
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hu
    exact zero_ne_one hu
  obtain ⟨w', hw'T, hw'u, hw'K⟩ : ∃ w', T w' = w' ∧ polar Q u w' = 0 ∧ ∀ b : K, b • u ≠ w' := by
    by_contra! h
    have hle : LinearMap.ker (polarBilin Q u) ≤ K ∙ u := by
      intro x hx
      have hx0 : polar Q u x = 0 := hx
      have hTx : polar Q u (T x) = 0 := by
        rw [← huT, polar_semilinear hTQ, hx0, map_zero]
      have h₁ := inv_smul_sub_mem_fixSpace hσσ' hTT (c := c) x
      have h₀ := sub_smul_inv_smul_mem_fixSpace hσσ' hTT hc x
      set x₁ := (c - σ c)⁻¹ • (x - T x) with hx₁
      have hp₁ : polar Q u x₁ = 0 := by
        rw [hx₁, polar_smul_right_eq, polar_sub_right, hx0, hTx, sub_zero, mul_zero]
      have hp₀ : polar Q u (x - c • x₁) = 0 := by
        rw [polar_sub_right, polar_smul_right_eq, hp₁, hx0, mul_zero, sub_zero]
      obtain ⟨b₁, hb₁⟩ := h x₁ h₁ hp₁
      obtain ⟨b₀, hb₀⟩ := h _ h₀ hp₀
      rw [Submodule.mem_span_singleton]
      refine ⟨b₀ + c * b₁, ?_⟩
      rw [add_smul, mul_smul, hb₁, hb₀, sub_add_cancel]
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu0] at h1
    have h2 := LinearMap.finrank_range_add_finrank_ker (polarBilin Q u)
    have h3 : finrank K (LinearMap.range (polarBilin Q u)) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range (polarBilin Q u))
      rwa [finrank_self] at this
    omega
  have hσw' : σ (1 + Q w') = 1 + Q w' := by rw [map_add, map_one, ← hTQ, hw'T]
  obtain ⟨a', ha'σ, ha'⟩ := exists_fixed_sq_eq hσw'
  refine ⟨u, w' + a' • u, huT, ?_, hu, ?_, ?_, ?_⟩
  · rw [map_add, map_smulₛₗ, RingEquiv.coe_toRingHom, ha'σ, huT, hw'T]
  · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, smul_eq_mul, hu, polar_smul_right_eq,
      polar_comm, hw'u, mul_zero, add_zero, mul_one, ← pow_two, ha']
    linear_combination (Q w') * (CharTwo.two_eq_zero : (2 : K) = 0)
  · rw [polar_add_right, polar_smul_right_eq, polar_self_charTwo, hw'u, mul_zero, add_zero]
  · rw [LinearIndependent.pair_iff' hu0]
    intro b hb
    apply hw'K (b - a')
    rw [sub_smul, hb, add_sub_cancel_right]

end FieldWitness

open FieldWitness in
theorem even_split_eight_field_involution_centralizer_count_witness {K : Type*} [Field K]
    [Finite K] [CharP K 2] {σ : K ≃+* K} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    {T : (Fin 4 ⊕ Fin 4 → K) →ₛₗ[(σ : K →+* K)] (Fin 4 ⊕ Fin 4 → K)} (hTT : ∀ v, T (T v) = v)
    (hTQ : ∀ v, quadPlus 4 K (T v) = σ (quadPlus 4 K v)) :
    ∃ g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K),
      g ∈ orthElementaryGroup (quadPlus 4 K) ∧ g * g = 1 ∧ g ≠ 1 ∧ (∀ x, g (T x) = T (g x)) ∧
      Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} =
        (Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1) + Nat.card K ^ 4 ∧
      Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
        2 * (Nat.card K ^ 3 + Nat.card K ^ 2 + Nat.card K + 1) ∧
      ∀ M : Submodule K (Fin 4 ⊕ Fin 4 → K), M ∈ singularSubspaces (quadPlus 4 K) 4 ↔
        (∀ x ∈ M, quadPlus 4 K x = 0) ∧
          ∀ M', M ≤ M' → (∀ x ∈ M', quadPlus 4 K x = 0) → M' = M := by
  have hV : 3 ≤ finrank K (Fin 4 ⊕ Fin 4 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨u, v, huT, hvT, hu, hv, hB, huv⟩ := exists_fixed_orthonormal_pair hσσ hσ1
    (nondegenerate_polarBilin_quadPlus 4 K) hV hTT hTQ
  obtain ⟨-, -, -, hgE, hgg, hg1, hg, hL, hM, hmax⟩ :=
    even_split_eight_rank_two_elementary_fixed_counts huv hu hv hB
  refine ⟨eichler (quadPlus 4 K) (u + v) u, hgE, hgg, hg1, fun x => ?_, hL, hM, hmax⟩
  rw [hg, hg, map_add, map_add, map_smulₛₗ, map_smulₛₗ, RingEquiv.coe_toRingHom,
    ← polar_semilinear hTQ, ← polar_semilinear hTQ, huT, hvT]

end CFSG.ComponentClassification.UnbalancedCatalog
