module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticSingularImage

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin Module Submodule

theorem even_split_eight_linear_involution_centralizer_count_witness {K : Type*} [Field K]
    [Finite K] [CharP K 2] {T : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)) (hT2 : T * T = 1) :
    ∃ g ∈ orthElementaryGroup (quadPlus 4 K), g * g = 1 ∧ g ≠ 1 ∧ g * T = T * g ∧
      Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} ≠
      2 * Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) //
        L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
          L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} := by
  set N : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
    (T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) - LinearMap.id with hNdef
  have hQn : (polarBilin (quadPlus 4 K)).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 K
  have hNx : ∀ x, N x = T x - x := fun x => rfl
  have hTT : ∀ x, T (T x) = x := fun x => by
    change (T * T) x = x
    rw [hT2]
    rfl
  have hNN : ∀ x, N (N x) = 0 := by
    intro x
    rw [hNx, hNx, map_sub, hTT]
    calc x - T x - (T x - x) = (2 : K) • (x - T x) := by module
      _ = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  have hfixN : ∀ x ∈ LinearMap.ker N, T x = x := fun x hx => by
    have h1 : N x = 0 := hx
    rw [hNx, sub_eq_zero] at h1
    exact h1
  have hRle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨x, rfl⟩
    exact hNN x
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  rw [finrank_split] at hrn
  have hRk := Submodule.finrank_mono hRle
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hq4 : 0 < Nat.card K ^ 4 := by positivity
  by_cases hsing : ∀ x ∈ LinearMap.ker N, quadPlus 4 K x = 0
  ·
    have hk := two_mul_finrank_le_of_singular hQn hsing
    rw [finrank_split] at hk
    have hX : LinearMap.range N ∈ singularSubspaces (quadPlus 4 K) 4 :=
      ⟨by omega, fun x hx => hsing x (hRle hx)⟩
    obtain ⟨hE, hne, hp, hm, -⟩ :=
      even_split_eight_singular_image_involution_fixed_counts hT hT2 hX
    refine ⟨T, hE, hT2, hne, rfl, ?_⟩
    rw [hp, hm]
    omega
  ·
    push Not at hsing
    obtain ⟨w, hwN, hw0⟩ := hsing
    obtain ⟨c, hc⟩ := exists_sq_eq_charTwo (quadPlus 4 K w)⁻¹
    obtain ⟨u, hu⟩ : ∃ u, u = c • w := ⟨_, rfl⟩
    have huN : u ∈ LinearMap.ker N := hu ▸ Submodule.smul_mem _ c hwN
    have hQu : quadPlus 4 K u = 1 := by
      rw [hu, map_smul_eq_sq, hc, inv_mul_cancel₀ hw0]
    have hu0 : u ≠ 0 := fun h => by
      rw [h, QuadraticMap.map_zero] at hQu
      exact zero_ne_one hQu
    have huu : polar (quadPlus 4 K) u u = 0 := polar_self_charTwo _ u
    set W := LinearMap.ker N ⊓ LinearMap.ker (polarBilin (quadPlus 4 K) u) with hW
    have hWdim : 3 ≤ finrank K W := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (polarBilin (quadPlus 4 K) u)
      have h2 : finrank K (LinearMap.range (polarBilin (quadPlus 4 K) u)) ≤ 1 := by
        have := Submodule.finrank_le (LinearMap.range (polarBilin (quadPlus 4 K) u))
        rwa [Module.finrank_self] at this
      have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker N)
        (LinearMap.ker (polarBilin (quadPlus 4 K) u))
      have h4 := Submodule.finrank_le (LinearMap.ker N ⊔
        LinearMap.ker (polarBilin (quadPlus 4 K) u))
      rw [finrank_split] at h1 h4
      rw [← hW] at h3
      omega
    obtain ⟨y, hyW, hyu⟩ : ∃ y ∈ W, y ∉ K ∙ u := by
      by_contra hcon
      push Not at hcon
      have hle : W ≤ K ∙ u := fun y hy => hcon y hy
      have h1 := Submodule.finrank_mono hle
      have h2 := finrank_span_singleton (K := K) hu0
      omega
    obtain ⟨hyN, hyB⟩ := Submodule.mem_inf.mp hyW
    have hyB' : polar (quadPlus 4 K) u y = 0 := by
      have h1 : polarBilin (quadPlus 4 K) u y = 0 := hyB
      rwa [polarBilin_apply_apply] at h1
    obtain ⟨a, ha⟩ := exists_sq_eq_charTwo (1 + quadPlus 4 K y)
    obtain ⟨v, hv⟩ : ∃ v, v = y + a • u := ⟨_, rfl⟩
    have hvN : v ∈ LinearMap.ker N := hv ▸ add_mem hyN (Submodule.smul_mem _ a huN)
    have hQv : quadPlus 4 K v = 1 := by
      rw [hv, QuadraticMap.map_add (quadPlus 4 K), map_smul_eq_sq, hQu, polar_smul_right_eq,
        polar_comm, hyB', mul_zero, add_zero, mul_one, ha]
      linear_combination (quadPlus 4 K y) * (CharTwo.two_eq_zero : (2 : K) = 0)
    have hBuv : polar (quadPlus 4 K) u v = 0 := by
      rw [hv, polar_add_right, polar_smul_right_eq, hyB', huu, mul_zero, add_zero]
    have huv : LinearIndependent K ![u, v] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have ht : t = 0 := by
        by_contra ht
        apply hyu
        have h1 : t • y = (-(s + t * a)) • u := by
          rw [hv, smul_add, smul_smul] at hst
          rw [neg_smul, eq_neg_iff_add_eq_zero, add_smul, ← hst]
          abel
        have h2 : y = (t⁻¹ * (-(s + t * a))) • u := by
          rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [h2]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
      subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hu0, rfl⟩
    obtain ⟨-, -, -, hgE, hgg, hg1, hgx, hp, hm, -⟩ :=
      even_split_eight_rank_two_elementary_fixed_counts huv hQu hQv hBuv
    refine ⟨eichler (quadPlus 4 K) (u + v) u, hgE, hgg, hg1, ?_, ?_⟩
    ·
      refine LinearEquiv.ext fun x => ?_
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgx, hgx, map_add, map_add, map_smul,
        map_smul, hfixN u huN, hfixN v hvN]
      rw [← polar_map_of_mem hT x u, ← polar_map_of_mem hT x v, hfixN u huN, hfixN v hvN]
    · rw [hp, hm]
      omega

end CFSG.ComponentClassification.UnbalancedCatalog
