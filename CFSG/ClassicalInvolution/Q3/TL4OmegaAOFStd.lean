module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFLevi
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFHyp
public import CFSG.ClassicalInvolution.Q3.Q3NMDiag
public import CFSG.ClassicalInvolution.Q3.Q3NMOrth

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open Matrix CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Standard

variable {F : Type} [Field F] [Finite F] {n : ℕ}

@[expose] def hypIdxN (n : ℕ) : Fin n × Bool ≃ Fin n ⊕ Fin n where
  toFun p := if p.2 then Sum.inl p.1 else Sum.inr p.1
  invFun := Sum.elim (fun i => (i, true)) (fun i => (i, false))
  left_inv := by
    rintro ⟨i, s⟩
    cases s <;> rfl
  right_inv := by
    rintro (i | i) <;> rfl

theorem hypIdxN_true (i : Fin n) : hypIdxN n (i, true) = Sum.inl i := rfl

theorem hypIdxN_false (i : Fin n) : hypIdxN n (i, false) = Sum.inr i := rfl

omit [Finite F] in
theorem exists_standardizing_n (h2 : (2 : F) ≠ 0)
    (hQ : (polarBilin (quadPlus n F)).Nondegenerate)
    {a : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)} (ha2 : a * a = 1)
    (hsim : ∀ v, quadPlus n F (a v) = -quadPlus n F v) :
    ∃ θ : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F),
      θ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) ∧ a * θ = θ * Levi.a₀ F n := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hdim : Module.finrank F (Fin n ⊕ Fin n → F) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  obtain ⟨v, hv, hu, hw⟩ := exists_hypFam_eigen_n h2 hQ hdim ha2 hsim
  set θ₀ : (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F) :=
    (hypComb v).comp (LinearMap.funLeft F F (hypIdxN n)) with hθ₀
  have hθapp : ∀ x, θ₀ x = ∑ p : Fin n × Bool, x (hypIdxN n p) • v p.1 p.2 := fun x => by
    rw [hθ₀, LinearMap.comp_apply, hypComb_apply]
    rfl
  have hinj : Function.Injective θ₀ :=
    (hypComb_injective hv).comp
      (LinearMap.funLeft_injective_of_surjective F F (hypIdxN n) (hypIdxN n).surjective)
  have hQθ : ∀ x, quadPlus n F (θ₀ x) = quadPlus n F x := by
    intro x
    have h1 : θ₀ x = hypComb v (x ∘ hypIdxN n) := by rw [hθapp, hypComb_apply]; rfl
    rw [h1, map_hypComb hv, quadPlus_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  refine ⟨LinearEquiv.ofInjectiveEndo θ₀ hinj, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    exact hQθ x
  · refine LinearEquiv.ext fun x => ?_
    show a (θ₀ x) = θ₀ (Levi.a₀ F n x)
    rw [hθapp, hθapp, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨i, s⟩
    cases s
    · rw [map_smul, hw, hypIdxN_false, Levi.a₀_apply]
      simp [Levi.dsign]
    · rw [map_smul, hu, hypIdxN_true, Levi.a₀_apply]
      simp [Levi.dsign]

theorem oddCoreIn_fixed_conjES_of_sim_involution_n (hF : Nat.card F = 3) (hn : 2 ≤ n)
    (hSL : CFSG.Open.IsQuasisimple SL(n, F)) (hSLZ : IsPGroup 2 (Subgroup.center SL(n, F)))
    (hQ : (polarBilin (quadPlus n F)).Nondegenerate)
    (hE : elementaryGroup (quadPlus n F) = ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F)⁆)
    {a : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)} (ha2 : a * a = 1)
    (hg : ∀ v, quadPlus n F (a v) = (-1 : F) * quadPlus n F v) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup (quadPlus n F))
      (Q3MFOD.conjES (quadPlus n F) hE (neg_ne_zero.mpr one_ne_zero) hg))) = ⊥ := by
  classical
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  have hμ : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hg₀ : ∀ v, quadPlus n F (Levi.a₀ F n v) = (-1 : F) * quadPlus n F v := fun v => by
    rw [Levi.quadPlus_a₀, neg_one_mul]
  obtain ⟨θ, hθO, hθ⟩ := exists_standardizing_n h2 hQ ha2 (fun v => by rw [hg v, neg_one_mul])
  have h0 := Levi.oddCoreIn_fixed_conjES_a₀ hF hn hSL hSLZ hQ hE
  have hcomm : Q3MFOD.conjES (quadPlus n F) hE hμ hg * conjE (quadPlus n F) θ hθO =
      conjE (quadPlus n F) θ hθO * Q3MFOD.conjES (quadPlus n F) hE hμ hg₀ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    show a * (θ * (b : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) * θ⁻¹) * a⁻¹ =
      θ * (Levi.a₀ F n * (b : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) *
        (Levi.a₀ F n)⁻¹) * θ⁻¹
    calc a * (θ * (b : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) * θ⁻¹) * a⁻¹
        = (a * θ) * (b : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) * (a * θ)⁻¹ := by
          group
      _ = (θ * Levi.a₀ F n) * (b : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) *
          (θ * Levi.a₀ F n)⁻¹ := by rw [hθ]
      _ = θ * (Levi.a₀ F n * (b : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) *
          (Levi.a₀ F n)⁻¹) * θ⁻¹ := by group
  have heq : Q3MFOD.conjES (quadPlus n F) hE hμ hg =
      conjE (quadPlus n F) θ hθO * Q3MFOD.conjES (quadPlus n F) hE hμ hg₀ *
        (conjE (quadPlus n F) θ hθO)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hcomm
  rw [heq, map_mul, map_mul, map_inv]
  exact oddCoreIn_fixed_conj_eq_bot _ _ h0

end Standard

end CFSG.ClassicalInvolution.Q3.TL4
