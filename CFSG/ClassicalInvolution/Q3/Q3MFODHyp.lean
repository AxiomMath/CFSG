module

public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTags
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthEigen
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthWitt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOD

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin

section Hyp

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem exists_isHypFam_of_sim_involution (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 8) {a : V ≃ₗ[F] V} (ha2 : a * a = 1)
    (hsim : ∀ v, Q (a v) = -Q v) : ∃ v : Fin 4 → Bool → V, IsHypFam Q v := by
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
      rw [QuadraticMap.polar_add_right, polar_comm Q (w : V) p, hPw p hp, hMM _ w.2 m hm, add_zero]
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
    (fun i j => hPP _ (b i).2 _ (b j).2) (fun i j => hMM _ (w i).2 _ (w j).2) huw⟩

end Hyp

section Count

variable {F : Type} [Field F] [Finite F]

theorem false_of_isHypFam_quadMinus (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 2 ≤ Nat.card F)
    (v : Fin 4 → Bool → (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F))
    (hv : IsHypFam (quadMinus 4 F b c) v) : False := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  let e' : Fin 4 × Bool ≃ Fin 4 ⊕ Fin 4 :=
    (Equiv.prodComm (Fin 4) Bool).trans (Equiv.boolProdEquivSum (Fin 4))
  let ψ₀ : (Fin 4 ⊕ Fin 4 → F) →ₗ[F] (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) :=
    (OrthAut.hypComb v).comp (LinearMap.funLeft F F e')
  have hψQ : ∀ w, quadMinus 4 F b c (ψ₀ w) = quadPlus 4 F w := by
    intro w
    show quadMinus 4 F b c (OrthAut.hypComb v (w ∘ e')) = _
    rw [OrthAut.map_hypComb hv, quadPlus_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show w (e' (i, true)) * w (e' (i, false)) = _
    simp [e', Equiv.boolProdEquivSum, mul_comm]
  have hinj : Function.Injective ψ₀ :=
    (OrthAut.hypComb_injective hv).comp
      (LinearMap.funLeft_injective_of_surjective F F e' e'.surjective)
  have hdim : Module.finrank F (Fin 4 ⊕ Fin 4 → F) =
      Module.finrank F (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp
  have hsurj : Function.Surjective ψ₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  have hcard : Nat.card {w : Fin 4 ⊕ Fin 4 → F // quadPlus 4 F w = 0} =
      Nat.card {x : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) // quadMinus 4 F b c x = 0} :=
    Nat.card_congr ((Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩).subtypeEquiv fun w => by
      rw [show (Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩) w = ψ₀ w from rfl, hψQ w])
  have e1 : (Nat.card {w : Fin 4 ⊕ Fin 4 → F // quadPlus 4 F w = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ 4 - 1) * ((Nat.card F : ℤ) ^ 3 + 1) :=
    CFSG.ClassicalInvolution.card_singular_quadPlus 3
  have e2 : (Nat.card {x : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) //
      quadMinus 4 F b c x = 0} : ℤ) = 1 + ((Nat.card F : ℤ) ^ 4 + 1) * ((Nat.card F : ℤ) ^ 3 - 1) :=
    CFSG.ClassicalInvolution.card_singular_quadMinus_of_two_ne_zero h2 hirr 3
  rw [hcard] at e1
  have hq : (2 : ℤ) ≤ (Nat.card F : ℤ) := by exact_mod_cast h4
  have key : ((Nat.card F : ℤ) ^ 4 - 1) * ((Nat.card F : ℤ) ^ 3 + 1) -
      ((Nat.card F : ℤ) ^ 4 + 1) * ((Nat.card F : ℤ) ^ 3 - 1) =
      2 * ((Nat.card F : ℤ) ^ 3 * ((Nat.card F : ℤ) - 1)) := by ring
  have hpos : 0 < (Nat.card F : ℤ) ^ 3 * ((Nat.card F : ℤ) - 1) :=
    mul_pos (pow_pos (by linarith) 3) (by linarith)
  linarith

theorem false_of_sim_involution_minus4 (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 2 ≤ Nat.card F)
    (hQ : (polarBilin (quadMinus 4 F b c)).Nondegenerate)
    (hdim : Module.finrank F (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) = 8)
    {a : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) ≃ₗ[F] (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F)}
    (ha2 : a * a = 1) (hsim : ∀ v, quadMinus 4 F b c (a v) = -quadMinus 4 F b c v) : False := by
  obtain ⟨v, hv⟩ := exists_isHypFam_of_sim_involution h2 hQ hdim ha2 hsim
  exact false_of_isHypFam_quadMinus h2 hirr h4 v hv

end Count

end CFSG.ClassicalInvolution.Q3.Q3MFOD
