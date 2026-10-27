module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentForm
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionEigen

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open TensorProduct

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem induction_form (h : UnitaryFieldData p f E) {W : Submodule h.fixedField V}
    (hW : Function.Surjective (LinearMap.liftBaseChange E W.subtype)) {P : V → Prop}
    (hs : ∀ (a : E) (w : W), P (a • (w : V))) (ha : ∀ x y, P x → P y → P (x + y))
    (v : V) : P v := by
  obtain ⟨t, rfl⟩ := hW v
  induction t using TensorProduct.inductionOn with
  | tmul a w => rw [LinearMap.liftBaseChange_tmul]; exact hs a w
  | add x y hx hy => rw [map_add]; exact ha _ _ hx hy

theorem exists_ext_of_forms (h : UnitaryFieldData p f E) {W W' : Submodule h.fixedField V}
    (hW : Function.Bijective (LinearMap.liftBaseChange E W.subtype))
    (hW' : Function.Bijective (LinearMap.liftBaseChange E W'.subtype))
    (ι : W ≃ₗ[h.fixedField] W') : ∃ g : V ≃ₗ[E] V, ∀ w : W, g (w : V) = (ι w : V) := by
  set e := LinearEquiv.ofBijective (LinearMap.liftBaseChange E W.subtype) hW with he
  set e' := LinearEquiv.ofBijective (LinearMap.liftBaseChange E W'.subtype) hW' with he'
  refine ⟨e.symm.trans ((LinearEquiv.baseChange h.fixedField E W W' ι).trans e'), fun w => ?_⟩
  have h1 : e.symm (w : V) = (1 : E) ⊗ₜ w := by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.ofBijective_apply,
      LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1, LinearEquiv.baseChange_tmul, he',
    LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem exists_conj_antiunitary (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    (hn : finrank E V = 3) {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm)
    (hnd : Hf.SeparatingLeft) (τ τ' : V →ₛₗ[h.bar] V) (hτ : Function.Bijective τ)
    (hτ' : Function.Bijective τ') (hτH : ∀ v w, Hf (τ v) (τ w) = h.bar (Hf v w))
    (hτ'H : ∀ v w, Hf (τ' v) (τ' w) = h.bar (Hf v w)) (μ μ' : Eˣ)
    (hμ : ∀ v, τ (τ v) = (μ : E) • v) (hμ' : ∀ v, τ' (τ' v) = (μ' : E) • v) :
    μ = 1 ∧ μ' = 1 ∧ ∃ (g : V ≃ₗ[E] V) (c : E), c ≠ 0 ∧
      (∀ v w, Hf (g v) (g w) = Hf v w) ∧ ∀ v, g (τ v) = c • τ' (g v) := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have : Finite E := h.finite
  have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero_of_odd h hp h1
  have hk2 : ringChar h.fixedField ≠ 2 := by
    intro hc
    apply h2
    have h0 := ringChar.Nat.cast_ringChar (R := h.fixedField)
    rw [hc] at h0
    exact_mod_cast h0
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by omega) hH hnd τ hτ hτH μ hμ
  obtain ⟨hbτ, hfinW, hbij, hB1, hB2⟩ := hall b t hb ht
  have hμ1' : μ = 1 := by
    rcases hμ1 with h1 | h1
    · exact h1
    · obtain ⟨-, -, -, -, heven, -⟩ := hB2 h1
      rw [hn] at heven
      exact absurd heven (by decide)
  obtain ⟨B, hBv, hsym, hBnd, -, -⟩ := hB1 hμ1'
  obtain ⟨hμ1₂, ⟨b', hb'⟩, ⟨t', ht'⟩, hall'⟩ := odd_unitary_conjugate_semilinear_involution_descent
    h hodd (by omega) hH hnd τ' hτ' hτ'H μ' hμ'
  obtain ⟨hbτ', hfinW', hbij', hB1', hB2'⟩ := hall' b' t' hb' ht'
  have hμ1'' : μ' = 1 := by
    rcases hμ1₂ with h1 | h1
    · exact h1
    · obtain ⟨-, -, -, -, heven, -⟩ := hB2' h1
      rw [hn] at heven
      exact absurd heven (by decide)
  obtain ⟨B', hBv', hsym', hBnd', -, -⟩ := hB1' hμ1''
  refine ⟨hμ1', hμ1'', ?_⟩
  have : Module.Finite h.fixedField (conjFixed h ((b : E) • τ)) := finite_conjFixed
  have : Module.Finite h.fixedField (conjFixed h ((b' : E) • τ')) := finite_conjFixed
  have hdW : finrank h.fixedField (conjFixed h ((b : E) • τ)) = 2 * 1 + 1 := by rw [hfinW, hn]
  have hdW' : finrank h.fixedField (conjFixed h ((b' : E) • τ')) = 2 * 1 + 1 := by
    rw [hfinW', hn]
  have hpol := CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B hsym h2
  have hpol' := CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym' h2
  obtain ⟨d₁, hd₁, ⟨e₁⟩⟩ := CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd hk2 _
    (by rw [hpol]; exact hBnd) hdW
  obtain ⟨d₂, hd₂, ⟨e₂⟩⟩ := CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd hk2 _
    (by rw [hpol']; exact hBnd') hdW'
  set ι := e₁.trans e₂.symm with hι
  have hQι : ∀ x, d₂ * CatalogueBOrthogonalDescent.originalQuadratic B' (ι x) =
      d₁ * CatalogueBOrthogonalDescent.originalQuadratic B x := fun x => by
    have := ι.map_app x
    simpa using this
  have hιB : ∀ w w', B' (ι w) (ι w') * d₂ = B w w' * d₁ := by
    intro w w'
    have hpB := LinearMap.congr_fun₂ hpol w w'
    have hpB' := LinearMap.congr_fun₂ hpol' (ι w) (ι w')
    change QuadraticMap.polar _ w w' = _ at hpB
    change QuadraticMap.polar _ (ι w) (ι w') = _ at hpB'
    rw [QuadraticMap.polar] at hpB hpB'
    rw [← map_add] at hpB'
    rw [← hpB, ← hpB']
    have e1 := hQι (w + w')
    have e2 := hQι w
    have e3 := hQι w'
    linear_combination e1 - e2 - e3
  set c₀ : h.fixedField := d₁ / d₂ with hc₀
  have hc₀0 : c₀ ≠ 0 := div_ne_zero hd₁ hd₂
  have hιB' : ∀ w w', B' (ι w) (ι w') = c₀ * B w w' := fun w w' => by
    rw [hc₀, div_mul_eq_mul_div, eq_div_iff hd₂, mul_comm d₁]
    exact hιB w w'
  obtain ⟨g₀, hg₀⟩ := exists_ext_of_forms h hbij hbij' ι.toLinearEquiv
  have hfix : ∀ w : conjFixed h ((b : E) • τ), ((b : E) • τ) (w : V) = w := fun w => w.2
  have hfix' : ∀ w : conjFixed h ((b' : E) • τ'), ((b' : E) • τ') (w : V) = w := fun w => w.2
  have hg₀τ : ∀ v, g₀ (((b : E) • τ) v) = ((b' : E) • τ') (g₀ v) := by
    refine induction_form h hbij.2 (fun a w => ?_) (fun x y hx hy => ?_)
    · rw [LinearMap.map_smulₛₗ, hfix, map_smul, map_smul, hg₀, LinearMap.map_smulₛₗ]
      exact congrArg _ (hfix' (ι w)).symm
    · rw [map_add, map_add, hx, hy, map_add, map_add]
  have hg₀H : ∀ v v', Hf (g₀ v) (g₀ v') = (c₀ : E) * Hf v v' := by
    intro v
    refine induction_form h hbij.2 (fun a' w' => ?_) (fun x y hx hy => ?_)
    · revert v
      refine induction_form h hbij.2 (fun a w => ?_) (fun x y hx hy => ?_)
      · have e1 : g₀ (a • (w : V)) = a • ((ι w : conjFixed h ((b' : E) • τ')) : V) := by
          rw [map_smul, hg₀]
          rfl
        have e2 : g₀ (a' • (w' : V)) = a' • ((ι w' : conjFixed h ((b' : E) • τ')) : V) := by
          rw [map_smul, hg₀]
          rfl
        rw [e1, e2, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, LinearMap.map_smulₛₗ₂,
          LinearMap.map_smul, ← hBv', ← hBv, hιB']
        simp only [smul_eq_mul, Subfield.coe_mul]
        ring
      · rw [map_add, LinearMap.map_add₂, hx, hy, LinearMap.map_add₂, mul_add]
    · rw [map_add, map_add, hx, hy, map_add, mul_add]
  obtain ⟨μ₀, hμ₀⟩ := (unitary_field_norm h).2.1 (Units.mk0 c₀⁻¹ (inv_ne_zero hc₀0))
  have hN : h.norm (μ₀ : E) = ((c₀⁻¹ : h.fixedField) : E) :=
    congrArg (fun u : h.fixedFieldˣ => ((u : h.fixedField) : E)) hμ₀
  have hμ₀0 : (μ₀ : E) ≠ 0 := μ₀.ne_zero
  have hb0 : (b : E) ≠ 0 := b.ne_zero
  set g := g₀.trans (LinearEquiv.smulOfUnit μ₀) with hg
  have hgv : ∀ v, g v = (μ₀ : E) • g₀ v := fun v => rfl
  refine ⟨g, (μ₀ : E) * ((b' : E) / (b : E)) * h.bar (μ₀ : E)⁻¹, ?_, ?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero hμ₀0 (div_ne_zero b'.ne_zero hb0)) ?_
    rw [map_inv₀]
    exact inv_ne_zero ((map_ne_zero h.bar).mpr hμ₀0)
  · intro v w
    rw [hgv, hgv, LinearMap.map_smulₛₗ₂, map_smul, hg₀H, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← mul_assoc]
    have hc : h.bar (μ₀ : E) * (μ₀ : E) * (c₀ : E) = 1 := by
      have e1 : h.bar (μ₀ : E) * (μ₀ : E) = ((c₀⁻¹ : h.fixedField) : E) := by
        rw [mul_comm, ← hN]
        rfl
      rw [e1, ← Subfield.coe_mul, inv_mul_cancel₀ hc₀0, Subfield.coe_one]
    rw [hc, one_mul]
  · intro v
    have h1 : (b : E) • g₀ (τ v) = (b' : E) • τ' (g₀ v) := by
      have := hg₀τ v
      rwa [LinearMap.smul_apply, map_smul, LinearMap.smul_apply] at this
    have h2' : g₀ (τ v) = ((b' : E) / (b : E)) • τ' (g₀ v) := by
      rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← h1, smul_smul, inv_mul_cancel₀ hb0, one_smul]
    have h3 : g₀ v = (μ₀ : E)⁻¹ • g v := by
      rw [hgv, smul_smul, inv_mul_cancel₀ hμ₀0, one_smul]
    rw [hgv, h2', h3, LinearMap.map_smulₛₗ, smul_smul, smul_smul]

end CFSG.ComponentClassification.GSThmB.CF23I
