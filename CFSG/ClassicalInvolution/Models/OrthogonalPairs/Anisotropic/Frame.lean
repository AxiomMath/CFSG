module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Root
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Generation
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

variable {K K' V : Type} [Field K] [Field K'] [Algebra K K'] {σ : K' ≃+* K'} [AddCommGroup V]
  [Module K V] {Q : QuadraticForm K V}

theorem Aniso.two_ne_zero_of (h2 : (2 : K) ≠ 0) : (2 : K') ≠ 0 := by
  intro h
  apply h2
  apply (algebraMap K K').injective
  rw [map_ofNat, h, map_zero]

theorem Aniso.sigma_inv_two (σ : K' ≃+* K') : σ ((2 : K')⁻¹) = (2 : K')⁻¹ := by
  rw [map_inv₀, map_ofNat]

namespace QuadExt

variable (E : QuadExt K K' σ)

@[expose] noncomputable def tau : K' := E.isUnitary.exists_traceZero.choose

theorem tau_spec : E.tau ≠ 0 ∧ E.tau + σ E.tau = 0 :=
  E.isUnitary.exists_traceZero.choose_spec

theorem tau_ne_zero : E.tau ≠ 0 := E.tau_spec.1

theorem sigma_tau : σ E.tau = -E.tau := by
  have := E.tau_spec.2
  linear_combination this

end QuadExt

structure HypBasis (σ : K' ≃+* K') where
  a : Fin 3 → K'
  b : Fin 3 → K'
  herm_aa : herm σ a a = 0
  herm_bb : herm σ b b = 0
  herm_ab : herm σ a b = 1

theorem HypBasis.herm_ba (P : HypBasis σ) (hσ : ∀ c, σ (σ c) = c) : herm σ P.b P.a = 1 := by
  rw [herm_conj σ hσ, P.herm_ab, map_one]

namespace UnitaryEmbedding

variable (D : UnitaryEmbedding Q σ)

theorem polar_incl_smul (hσ : ∀ c, σ (σ c) = c) (l m : K') (x y : Fin 3 → K') :
    algebraMap K K' (polar Q (D.incl (l • x)) (D.incl (m • y))) =
      σ l * m * herm σ x y + σ (σ l * m * herm σ x y) := by
  rw [D.polar_incl hσ, herm_smul_left, herm_smul_right, ← mul_assoc]

theorem Q_incl_smul {x : Fin 3 → K'} (hx : herm σ x x = 0) (l : K') : Q (D.incl (l • x)) = 0 :=
  D.Q_incl_eq_zero (by rw [herm_smul_left, herm_smul_right, hx]; ring)

variable (E : QuadExt K K' σ) (h2 : (2 : K) ≠ 0) (P : HypBasis σ)

section Polar

include E h2

theorem hyp_polar_e₁_f₁ :
    polar Q (D.incl P.a) (D.incl ((2 : K')⁻¹ • P.b)) = 1 := by
  apply (algebraMap K K').injective
  have h := D.polar_incl_smul E.isUnitary.invol 1 (2 : K')⁻¹ P.a P.b
  rw [one_smul] at h
  rw [h, P.herm_ab, map_one σ, one_mul, mul_one, Aniso.sigma_inv_two,
    map_one (algebraMap K K')]
  have h2' : (2 : K') ≠ 0 := Aniso.two_ne_zero_of h2
  field_simp
  norm_num

theorem hyp_polar_e₂_f₂ :
    polar Q (D.incl (E.tau • P.a)) (D.incl ((-(2 * E.tau)⁻¹) • P.b)) = 1 := by
  apply (algebraMap K K').injective
  have h2' : (2 : K') ≠ 0 := Aniso.two_ne_zero_of h2
  have hτ := E.tau_ne_zero
  have e : σ E.tau * (-(2 * E.tau)⁻¹) * herm σ P.a P.b = (2 : K')⁻¹ := by
    rw [P.herm_ab, E.sigma_tau]
    field_simp
  rw [D.polar_incl_smul E.isUnitary.invol, e, Aniso.sigma_inv_two, map_one (algebraMap K K')]
  field_simp
  norm_num

omit h2 in
theorem hyp_polar_e₁_e₂ : polar Q (D.incl P.a) (D.incl (E.tau • P.a)) = 0 := by
  apply (algebraMap K K').injective
  have h := D.polar_incl_smul E.isUnitary.invol 1 E.tau P.a P.a
  rw [one_smul] at h
  rw [h, P.herm_aa, mul_zero, map_zero, add_zero, map_zero]

theorem hyp_polar_e₁_f₂ :
    polar Q (D.incl P.a) (D.incl ((-(2 * E.tau)⁻¹) • P.b)) = 0 := by
  apply (algebraMap K K').injective
  have h2' : (2 : K') ≠ 0 := Aniso.two_ne_zero_of h2
  have hτ := E.tau_ne_zero
  have h := D.polar_incl_smul E.isUnitary.invol 1 (-(2 * E.tau)⁻¹) P.a P.b
  rw [one_smul] at h
  rw [h, P.herm_ab, map_one σ, one_mul, mul_one, map_neg, map_inv₀, map_mul, map_ofNat,
    E.sigma_tau, map_zero]
  field_simp
  ring

omit h2 in
theorem hyp_polar_f₁_e₂ :
    polar Q (D.incl ((2 : K')⁻¹ • P.b)) (D.incl (E.tau • P.a)) = 0 := by
  apply (algebraMap K K').injective
  rw [D.polar_incl_smul E.isUnitary.invol, P.herm_ba E.isUnitary.invol, Aniso.sigma_inv_two,
    mul_one, map_mul, Aniso.sigma_inv_two, E.sigma_tau, map_zero]
  ring

omit h2 in
theorem hyp_polar_f₁_f₂ :
    polar Q (D.incl ((2 : K')⁻¹ • P.b)) (D.incl ((-(2 * E.tau)⁻¹) • P.b)) = 0 := by
  apply (algebraMap K K').injective
  rw [D.polar_incl_smul E.isUnitary.invol, P.herm_bb, mul_zero, map_zero, add_zero, map_zero]

end Polar


@[expose] noncomputable def hypFrame : Frame Q where
  P := ⟨D.incl P.a, D.incl ((2 : K')⁻¹ • P.b), D.Q_incl_eq_zero P.herm_aa,
    D.Q_incl_smul P.herm_bb _, D.hyp_polar_e₁_f₁ E h2 P⟩
  P' := ⟨D.incl (E.tau • P.a), D.incl ((-(2 * E.tau)⁻¹) • P.b), D.Q_incl_smul P.herm_aa _,
    D.Q_incl_smul P.herm_bb _, D.hyp_polar_e₂_f₂ E h2 P⟩
  orth := ⟨D.hyp_polar_e₁_e₂ E P, D.hyp_polar_e₁_f₂ E h2 P, D.hyp_polar_f₁_e₂ E P,
    D.hyp_polar_f₁_f₂ E P⟩

theorem hypFrame_e₁ : (D.hypFrame E h2 P).e₁ = D.incl P.a := rfl

theorem hypFrame_f₁ : (D.hypFrame E h2 P).f₁ = D.incl ((2 : K')⁻¹ • P.b) := rfl

theorem hypFrame_e₂ : (D.hypFrame E h2 P).e₂ = D.incl (E.tau • P.a) := rfl

theorem hypFrame_f₂ : (D.hypFrame E h2 P).f₂ = D.incl ((-(2 * E.tau)⁻¹) • P.b) := rfl

end UnitaryEmbedding

namespace QuadExt

variable (E : QuadExt K K' σ)

theorem trace_zero_e (c : K) :
    (σ E.tau * algebraMap K K' c - σ (algebraMap K K' c) * E.tau) +
      σ (σ E.tau * algebraMap K K' c - σ (algebraMap K K' c) * E.tau) = 0 := by
  simp only [map_sub, map_mul, map_neg, E.fix, E.sigma_tau]
  ring

theorem trace_zero_f (h2 : (2 : K) ≠ 0) (c : K) :
    (σ ((2 : K')⁻¹) * (algebraMap K K' c * (-(2 * E.tau)⁻¹)) -
        σ (algebraMap K K' c * (-(2 * E.tau)⁻¹)) * (2 : K')⁻¹) +
      σ (σ ((2 : K')⁻¹) * (algebraMap K K' c * (-(2 * E.tau)⁻¹)) -
        σ (algebraMap K K' c * (-(2 * E.tau)⁻¹)) * (2 : K')⁻¹) = 0 := by
  have h2' : (2 : K') ≠ 0 := Aniso.two_ne_zero_of h2
  have hτ := E.tau_ne_zero
  simp only [map_sub, map_mul, map_neg, map_inv₀, map_ofNat, E.fix, E.sigma_tau]
  field_simp
  ring

theorem exists_eq_e {x : K'} (h2 : (2 : K) ≠ 0) (hx : x + σ x = 0) :
    ∃ c : K, x = σ E.tau * algebraMap K K' c - σ (algebraMap K K' c) * E.tau := by
  have h2' : (2 : K') ≠ 0 := Aniso.two_ne_zero_of h2
  have hτ := E.tau_ne_zero
  have hσx : σ x = -x := by linear_combination hx
  have hr : σ (-x / (2 * E.tau)) = -x / (2 * E.tau) := by
    rw [map_div₀, map_neg, map_mul, map_ofNat, hσx, E.sigma_tau]
    field_simp
  obtain ⟨c, hc⟩ := E.exists_of_fix _ hr
  refine ⟨c, ?_⟩
  rw [E.fix, hc, E.sigma_tau]
  field_simp
  ring

theorem exists_eq_f {x : K'} (h2 : (2 : K) ≠ 0) (hx : x + σ x = 0) :
    ∃ c : K, x = σ ((2 : K')⁻¹) * (algebraMap K K' c * (-(2 * E.tau)⁻¹)) -
        σ (algebraMap K K' c * (-(2 * E.tau)⁻¹)) * (2 : K')⁻¹ := by
  have h2' : (2 : K') ≠ 0 := Aniso.two_ne_zero_of h2
  have hτ := E.tau_ne_zero
  have hσx : σ x = -x := by linear_combination hx
  have hr : σ (-x * (2 * E.tau)) = -x * (2 * E.tau) := by
    rw [map_mul, map_neg, map_mul, map_ofNat, hσx, E.sigma_tau]
    ring
  obtain ⟨c, hc⟩ := E.exists_of_fix _ hr
  refine ⟨c, ?_⟩
  simp only [map_mul, map_neg, map_inv₀, map_ofNat, E.sigma_tau, hc, hσx]
  field_simp
  ring

end QuadExt

namespace UnitaryEmbedding

variable (D : UnitaryEmbedding Q σ) (E : QuadExt K K' σ) (h2 : (2 : K) ≠ 0) (P : HypBasis σ)

theorem theta_tv_e (c : K) :
    D.theta (tv E.isUnitary.invol P.herm_aa (E.trace_zero_e c)) =
      eichler Q (D.hypFrame E h2 P).e₂ (c • (D.hypFrame E h2 P).e₁) := by
  rw [D.theta_tv E.isUnitary.invol P.herm_aa E.tau (algebraMap K K' c) (E.trace_zero_e c),
    hypFrame_e₂, hypFrame_e₁, ← D.incl_algebraMap_smul]

theorem theta_tv_f (c : K) :
    D.theta (tv E.isUnitary.invol P.herm_bb (E.trace_zero_f h2 c)) =
      eichler Q (D.hypFrame E h2 P).f₁ (c • (D.hypFrame E h2 P).f₂) := by
  rw [D.theta_tv E.isUnitary.invol P.herm_bb (2 : K')⁻¹
    (algebraMap K K' c * (-(2 * E.tau)⁻¹)) (E.trace_zero_f h2 c),
    hypFrame_f₁, hypFrame_f₂, ← D.incl_algebraMap_smul, smul_smul]

theorem hypFrame_La_range :
    (D.hypFrame E h2 P).La.range =
      (Subgroup.closure (tvAt σ P.a ∪ tvAt σ P.b)).map D.theta := by
  rw [Frame.La_range_eq_closure]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [← D.theta_tv_e E h2 P c]
      exact ⟨_, Subgroup.subset_closure (Or.inl (tv_mem_tvAt _ _ _)), rfl⟩
    · rw [← D.theta_tv_f E h2 P c]
      exact ⟨_, Subgroup.subset_closure (Or.inr (tv_mem_tvAt _ _ _)), rfl⟩
  · rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg | hg, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := exists_eq_tv_of_mem_tvAt E.isUnitary.invol P.herm_aa hg
      obtain ⟨c, rfl⟩ := E.exists_eq_e h2 hx
      rw [D.theta_tv_e E h2 P c]
      exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
    · obtain ⟨x, hx, rfl⟩ := exists_eq_tv_of_mem_tvAt E.isUnitary.invol P.herm_bb hg
      obtain ⟨c, rfl⟩ := E.exists_eq_f h2 hx
      rw [D.theta_tv_f E h2 P c]
      exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

theorem hypFrame_span_le {S : Submodule K V} (h₁ : ∀ l : K', D.incl (l • P.a) ∈ S)
    (h₂ : ∀ m : K', D.incl (m • P.b) ∈ S) : (D.hypFrame E h2 P).span ≤ S := by
  rintro _ ⟨X, rfl⟩
  have e₁ : D.incl P.a ∈ S := by simpa using h₁ 1
  rw [Frame.incl_apply, hypFrame_e₁, hypFrame_f₁, hypFrame_e₂, hypFrame_f₂]
  exact S.add_mem (S.add_mem (S.add_mem (S.smul_mem _ e₁) (S.smul_mem _ (h₂ _)))
    (S.smul_mem _ (h₁ _))) (S.smul_mem _ (h₂ _))

end UnitaryEmbedding

@[expose] noncomputable def HypBasis.ofWitt (W : WittData σ) (c : Fin 3) : HypBasis σ where
  a := insZero c (W.hypA 0)
  b := insZero c (W.hypB 0)
  herm_aa := by rw [herm_insZero]; exact W.herm_hypA_hypA
  herm_bb := by rw [herm_insZero]; exact W.herm_hypB_hypB
  herm_ab := by rw [herm_insZero]; exact W.herm_hypA_hypB

namespace UnitaryEmbedding

variable (D : UnitaryEmbedding Q σ) (E : QuadExt K K' σ) (h2 : (2 : K) ≠ 0)

theorem hypFrame_La_range_block (W : WittData σ) (c : Fin 3) :
    (D.hypFrame E h2 (HypBasis.ofWitt W c)).La.range = (embSUid σ c).range.map D.theta := by
  rw [D.hypFrame_La_range E h2, ← closure_tvAt_insZero E.isUnitary W c]
  rfl

theorem hypFrame_span_le_of_coord (W : WittData σ) (c : Fin 3) {S : Submodule K V}
    (hS : ∀ x : Fin 3 → K', x c = 0 → D.incl x ∈ S) :
    (D.hypFrame E h2 (HypBasis.ofWitt W c)).span ≤ S := by
  refine D.hypFrame_span_le E h2 _ (fun l => hS _ ?_) (fun m => hS _ ?_) <;>
    simp [HypBasis.ofWitt, insZero_self]

end UnitaryEmbedding

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
