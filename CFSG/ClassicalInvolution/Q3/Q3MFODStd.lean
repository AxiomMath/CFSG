module

public import CFSG.ClassicalInvolution.Q3.Q3MFODBlock
public import CFSG.ClassicalInvolution.Q3.Q3NMDiag
public import CFSG.ClassicalInvolution.Q3.Q3NMOrth

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open Matrix CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Hyp

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem exists_hypFam_eigen (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 8) {a : V ≃ₗ[F] V} (ha2 : a * a = 1)
    (hsim : ∀ v, Q (a v) = -Q v) :
    ∃ v : Fin 4 → Bool → V, IsHypFam Q v ∧ (∀ i, a (v i true) = v i true) ∧
      (∀ i, a (v i false) = -v i false) := by
  classical
  set P := plusSp a with hP
  set M := minusSp a with hM
  have hc : IsCompl P M := isCompl_plusSp_minusSp h2 ha2
  have hQP : ∀ u ∈ P, Q u = 0 := by
    intro u hu
    have h1 := hsim u
    rw [mem_plusSp.mp hu] at h1
    have : (2 : F) * Q u = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left h2
  have hQM : ∀ w ∈ M, Q w = 0 := by
    intro w hw
    have h1 := hsim w
    rw [mem_minusSp.mp hw, QuadraticMap.map_neg] at h1
    have : (2 : F) * Q w = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left h2
  have hpol : ∀ U : Submodule F V, (∀ u ∈ U, Q u = 0) →
      ∀ u ∈ U, ∀ u' ∈ U, polar Q u u' = 0 := by
    intro U hU u hu u' hu'
    have e := QuadraticMap.map_add Q u u'
    rw [hU (u + u') (U.add_mem hu hu'), hU u hu, hU u' hu'] at e
    linear_combination -e
  have hPP := hpol P hQP
  have hMM := hpol M hQM
  have hsum : Module.finrank F P + Module.finrank F M = 8 := by
    rw [← hdim]
    exact Submodule.finrank_add_eq_of_isCompl hc
  have hle : ∀ U : Submodule F V, (∀ u ∈ U, ∀ u' ∈ U, polar Q u u' = 0) →
      Module.finrank F U ≤ 4 := by
    intro U hU
    have hUle : U ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U := by
      intro u hu
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro x hx
      rw [polarBilin_apply_apply]
      exact hU x hx u hu
    have h1 := Submodule.finrank_mono hUle
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, hdim] at h1
    have h3 := Submodule.finrank_le U
    omega
  have hP4 : Module.finrank F P = 4 := by
    have := hle P hPP
    have := hle M hMM
    omega
  have hM4 : Module.finrank F M = 4 := by omega
  let b : Module.Basis (Fin 4) F P := Module.finBasisOfFinrankEq F P hP4
  let Ψ : M →ₗ[F] (Fin 4 → F) :=
    LinearMap.pi fun i => (polarBilin Q (b i : V)).comp M.subtype
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : ∀ i, polar Q (b i : V) (w : V) = 0 := fun i => by
      have := congrFun hw i
      simpa [Ψ, polarBilin_apply_apply] using this
    have hfun : ((polarBilin Q).flip (w : V)).comp P.subtype = 0 :=
      b.ext fun i => by
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply,
          LinearMap.flip_apply, polarBilin_apply_apply]
        exact hw' i
    have hPw : ∀ u ∈ P, polar Q u (w : V) = 0 := fun u hu => by
      have := LinearMap.congr_fun hfun ⟨u, hu⟩
      simpa [polarBilin_apply_apply] using this
    have hall : ∀ x : V, polar Q (w : V) x = 0 := by
      intro x
      have hx : x ∈ P ⊔ M := by rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨p, hp, m, hm, rfl⟩ := Submodule.mem_sup.mp hx
      rw [QuadraticMap.polar_add_right, polar_comm Q (w : V) p, hPw p hp, hMM _ w.2 m hm,
        add_zero]
    exact Subtype.ext (hQ.1 (w : V) fun x => by
      rw [polarBilin_apply_apply]
      exact hall x)
  have hΨsurj : Function.Surjective Ψ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hΨinj
    rw [hM4, Module.finrank_fin_fun]
  choose w hw using fun j : Fin 4 => hΨsurj (Pi.single j 1)
  have huw : ∀ i j, polar Q (b i : V) ((w j : M) : V) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (hw j) i
    simp only [Ψ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      polarBilin_apply_apply, Pi.single_apply] at this
    rw [this]
  refine ⟨_, isHypFam_of_table (fun i => (b i : V)) (fun j => ((w j : M) : V))
    (fun i => hQP _ (b i).2) (fun j => hQM _ (w j).2)
    (fun i j => hPP _ (b i).2 _ (b j).2) (fun i j => hMM _ (w i).2 _ (w j).2) huw, ?_, ?_⟩
  · intro i
    exact mem_plusSp.mp (b i).2
  · intro i
    exact mem_minusSp.mp (w i).2

end Hyp

section Standard

variable {F : Type} [Field F] [Finite F]

@[expose] def hypIdx : Fin 4 × Bool ≃ Fin 4 ⊕ Fin 4 where
  toFun p := if p.2 then Sum.inl p.1 else Sum.inr p.1
  invFun := Sum.elim (fun i => (i, true)) (fun i => (i, false))
  left_inv := by
    rintro ⟨i, s⟩
    cases s <;> rfl
  right_inv := by
    rintro (i | i) <;> rfl

theorem hypIdx_true (i : Fin 4) : hypIdx (i, true) = Sum.inl i := rfl

theorem hypIdx_false (i : Fin 4) : hypIdx (i, false) = Sum.inr i := rfl

theorem exists_standardizing (h2 : (2 : F) ≠ 0) (hQ : (polarBilin (quadPlus 4 F)).Nondegenerate)
    {a : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)} (ha2 : a * a = 1)
    (hsim : ∀ v, quadPlus 4 F (a v) = -quadPlus 4 F v) :
    ∃ θ : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F),
      θ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F) ∧ a * θ = θ * a₀ F := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hdim : Module.finrank F (Fin 4 ⊕ Fin 4 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  obtain ⟨v, hv, hu, hw⟩ := exists_hypFam_eigen h2 hQ hdim ha2 hsim
  set θ₀ : (Fin 4 ⊕ Fin 4 → F) →ₗ[F] (Fin 4 ⊕ Fin 4 → F) :=
    (hypComb v).comp (LinearMap.funLeft F F hypIdx) with hθ₀
  have hθapp : ∀ x, θ₀ x = ∑ p : Fin 4 × Bool, x (hypIdx p) • v p.1 p.2 := fun x => by
    rw [hθ₀, LinearMap.comp_apply, hypComb_apply]
    rfl
  have hinj : Function.Injective θ₀ :=
    (hypComb_injective hv).comp
      (LinearMap.funLeft_injective_of_surjective F F hypIdx hypIdx.surjective)
  have hQθ : ∀ x, quadPlus 4 F (θ₀ x) = quadPlus 4 F x := by
    intro x
    have h1 : θ₀ x = hypComb v (x ∘ hypIdx) := by rw [hθapp, hypComb_apply]; rfl
    rw [h1, map_hypComb hv, quadPlus_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  refine ⟨LinearEquiv.ofInjectiveEndo θ₀ hinj, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    exact hQθ x
  · refine LinearEquiv.ext fun x => ?_
    show a (θ₀ x) = θ₀ (a₀ F x)
    rw [hθapp, hθapp, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨i, s⟩
    cases s
    · rw [map_smul, hw, hypIdx_false, a₀_apply]
      simp [dsign]
    · rw [map_smul, hu, hypIdx_true, a₀_apply]
      simp [dsign]

theorem oddCoreIn_fixed_conjES_of_sim_involution (hF : Nat.card F = 3)
    (hSL : CFSG.Open.IsQuasisimple SL(4, F)) (hSLZ : IsPGroup 2 (Subgroup.center SL(4, F)))
    (hQ : (polarBilin (quadPlus 4 F)).Nondegenerate)
    (hE : elementaryGroup (quadPlus 4 F) = ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F)⁆)
    {a : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)} (ha2 : a * a = 1)
    (hg : ∀ v, quadPlus 4 F (a v) = (-1 : F) * quadPlus 4 F v) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup (quadPlus 4 F))
      (conjES (quadPlus 4 F) hE (neg_ne_zero.mpr one_ne_zero) hg))) = ⊥ := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_three hF
  have hμ : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hg₀ : ∀ v, quadPlus 4 F (a₀ F v) = (-1 : F) * quadPlus 4 F v := fun v => by
    rw [quadPlus_a₀, neg_one_mul]
  obtain ⟨θ, hθO, hθ⟩ := exists_standardizing h2 hQ ha2 (fun v => by rw [hg v, neg_one_mul])
  have h0 := oddCoreIn_fixed_conjES_a₀ hF hSL hSLZ hQ hE
  have hcomm : conjES (quadPlus 4 F) hE hμ hg * conjE (quadPlus 4 F) θ hθO =
      conjE (quadPlus 4 F) θ hθO * conjES (quadPlus 4 F) hE hμ hg₀ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    show a * (θ * (b : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) * θ⁻¹) * a⁻¹ =
      θ * (a₀ F * (b : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) * (a₀ F)⁻¹) * θ⁻¹
    calc a * (θ * (b : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) * θ⁻¹) * a⁻¹
        = (a * θ) * (b : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) * (a * θ)⁻¹ := by group
      _ = (θ * a₀ F) * (b : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) * (θ * a₀ F)⁻¹ := by
        rw [hθ]
      _ = θ * (a₀ F * (b : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) * (a₀ F)⁻¹) * θ⁻¹ := by
        group
  have heq : conjES (quadPlus 4 F) hE hμ hg =
      conjE (quadPlus 4 F) θ hθO * conjES (quadPlus 4 F) hE hμ hg₀ *
        (conjE (quadPlus 4 F) θ hθO)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hcomm
  rw [heq, map_mul, map_mul, map_inv]
  exact oddCoreIn_fixed_conj_eq_bot _ _ h0

end Standard

end CFSG.ClassicalInvolution.Q3.Q3MFOD
