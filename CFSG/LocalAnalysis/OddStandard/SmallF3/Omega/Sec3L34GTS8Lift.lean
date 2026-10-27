module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GTS8Card

public section

namespace CFSG.OddStandard.SmallF3.Omega

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private lemma lift_c {E : Type} [Group E] (ρ : E →* SL23) (hρ : Function.Surjective ρ)
    {σ : E} (hσ2 : σ * σ = 1) (hσc : ∀ e : E, e * σ = σ * e)
    (hker : ∀ e : E, ρ e = 1 ↔ e = 1 ∨ e = σ) :
    ∃ ct : E, ρ ct = slC ∧ ct ^ 3 = 1 := by
  classical
  obtain ⟨c0, hc0⟩ := hρ slC
  have hρσ : ρ σ = 1 := (hker σ).mpr (Or.inr rfl)
  have hc0ker : c0 ^ 3 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hc0, slC_cubed]
  have hc0cases : c0 ^ 3 = 1 ∨ c0 ^ 3 = σ := (hker (c0 ^ 3)).mp hc0ker
  refine ⟨if c0 ^ 3 = 1 then c0 else c0 * σ, ?_, ?_⟩
  · split_ifs with h
    · exact hc0
    · rw [map_mul, hc0, hρσ, mul_one]
  · split_ifs with h
    · exact h
    · have hcs : c0 ^ 3 = σ := hc0cases.resolve_left h
      have hcomm : Commute c0 σ := hσc c0
      rw [hcomm.mul_pow, hcs]
      have hσ3 : σ ^ 3 = σ := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_two, hσ2, one_mul, pow_one]
      rw [hσ3, hσ2]

private lemma lift_quaternion {E : Type} [Group E] (ρ : E →* SL23)
    (hρ : Function.Surjective ρ)
    {σ : E} (hσ2 : σ * σ = 1) (hσc : ∀ e : E, e * σ = σ * e)
    (hker : ∀ e : E, ρ e = 1 ↔ e = 1 ∨ e = σ)
    (ct : E) (hρct : ρ ct = slC) :
    ∃ it jt : E, ρ it = slI ∧ ρ jt = slJ ∧
      ct * it * ct⁻¹ = jt ∧ ct * jt * ct⁻¹ = it * jt := by
  classical
  have hρσ : ρ σ = 1 := (hker σ).mpr (Or.inr rfl)
  obtain ⟨i0, hi0⟩ := hρ slI
  set j0 : E := ct * i0 * ct⁻¹ with hj0def
  set k0 : E := ct * j0 * ct⁻¹ with hk0def
  have hρj0 : ρ j0 = slJ := by
    rw [hj0def, map_mul, map_mul, map_inv, hρct, hi0, slC_conj_I]
  have hρk0 : ρ k0 = slI * slJ := by
    rw [hk0def, map_mul, map_mul, map_inv, hρct, hρj0, slC_conj_J]
  have hwker : i0 * j0 * k0⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hi0, hρj0, hρk0]
    group
  have hwcases : i0 * j0 * k0⁻¹ = 1 ∨ i0 * j0 * k0⁻¹ = σ := (hker _).mp hwker
  set it : E := if i0 * j0 * k0⁻¹ = 1 then i0 else i0 * σ with hitdef
  set jt : E := ct * it * ct⁻¹ with hjtdef
  set kt : E := ct * jt * ct⁻¹ with hktdef
  have hρit : ρ it = slI := by
    rw [hitdef]
    split_ifs with h
    · exact hi0
    · rw [map_mul, hi0, hρσ, mul_one]
  have hρjt : ρ jt = slJ := by
    rw [hjtdef, map_mul, map_mul, map_inv, hρct, hρit, slC_conj_I]
  have hconjσ : ∀ e : E, ct * (e * σ) * ct⁻¹ = (ct * e * ct⁻¹) * σ := by
    intro e
    calc ct * (e * σ) * ct⁻¹ = ct * e * (σ * ct⁻¹) := by group
      _ = ct * e * (ct⁻¹ * σ) := by rw [(hσc ct⁻¹).symm]
      _ = (ct * e * ct⁻¹) * σ := by group
  have hmulσσ : ∀ a b : E, (a * σ) * (b * σ) = a * b := by
    intro a b
    calc (a * σ) * (b * σ) = (a * σ) * (σ * b) := by rw [hσc b]
      _ = a * (σ * σ) * b := by group
      _ = a * 1 * b := by rw [hσ2]
      _ = a * b := by group
  have hitjt : it * jt = kt := by
    rw [hitdef]
    split_ifs with h
    · have hjt : jt = j0 := by rw [hjtdef, hitdef, if_pos h]
      have hkt : kt = k0 := by rw [hktdef, hjt]
      rw [hjt, hkt]
      have hij : i0 * j0 = k0 := by
        have := congrArg (· * k0) h
        simpa [mul_assoc] using this
      rw [hij]
    · have hwσ : i0 * j0 * k0⁻¹ = σ := hwcases.resolve_left h
      have hjt : jt = j0 * σ := by
        rw [hjtdef, hitdef, if_neg h, hj0def, hconjσ]
      have hkt : kt = k0 * σ := by
        rw [hktdef, hjt, hk0def, hconjσ]
      rw [hjt, hkt, hmulσσ]
      have hij : i0 * j0 = k0 * σ := by
        have : i0 * j0 = σ * k0 := by
          have := congrArg (· * k0) hwσ
          simpa [mul_assoc] using this
        rw [this, hσc k0]
      rw [hij]
  exact ⟨it, jt, hρit, hρjt, hjtdef.symm, hktdef.symm.trans hitjt.symm⟩

private lemma lift_ct_conj_it_sq {E : Type} [Group E] (ρ : E →* SL23)
    {σ : E} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hσc : ∀ e : E, e * σ = σ * e)
    (hker : ∀ e : E, ρ e = 1 ↔ e = 1 ∨ e = σ)
    (ct it : E) (hρct : ρ ct = slC) (hρit : ρ it = slI) (hct3 : ct ^ 3 = 1) :
    ct * it ^ 2 * ct⁻¹ = it ^ 2 := by
  have hconjσ : ∀ e : E, ct * (e * σ) * ct⁻¹ = (ct * e * ct⁻¹) * σ := by
    intro e
    calc ct * (e * σ) * ct⁻¹ = ct * e * (σ * ct⁻¹) := by group
      _ = ct * e * (ct⁻¹ * σ) := by rw [(hσc ct⁻¹).symm]
      _ = (ct * e * ct⁻¹) * σ := by group
  have hρα : ρ (it ^ 2) = slI ^ 2 := by rw [map_pow, hρit]
  have hρconj : ρ (ct * it ^ 2 * ct⁻¹) = ρ (it ^ 2) := by
    rw [map_mul, map_mul, map_inv, hρct, hρα, slC_conj_I_sq]
  have hkerconj : (ct * it ^ 2 * ct⁻¹) * (it ^ 2)⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρconj, mul_inv_cancel]
  have hcases : (ct * it ^ 2 * ct⁻¹) * (it ^ 2)⁻¹ = 1 ∨
      (ct * it ^ 2 * ct⁻¹) * (it ^ 2)⁻¹ = σ := (hker _).mp hkerconj
  have hcases' : ct * it ^ 2 * ct⁻¹ = it ^ 2 ∨ ct * it ^ 2 * ct⁻¹ = it ^ 2 * σ := by
    rcases hcases with h | h
    · left
      have := congrArg (· * it ^ 2) h
      simpa [mul_assoc] using this
    · right
      have hx : ct * it ^ 2 * ct⁻¹ = σ * it ^ 2 := by
        have := congrArg (· * it ^ 2) h
        simpa [mul_assoc] using this
      rw [hx, hσc (it ^ 2)]
  rcases hcases' with h | h
  · exact h
  · exfalso
    have h2 : ct ^ 2 * it ^ 2 * (ct ^ 2)⁻¹ = it ^ 2 := by
      calc ct ^ 2 * it ^ 2 * (ct ^ 2)⁻¹ = ct * (ct * it ^ 2 * ct⁻¹) * ct⁻¹ := by
            simp only [pow_two, inv_pow]; group
        _ = ct * (it ^ 2 * σ) * ct⁻¹ := by rw [h]
        _ = (ct * it ^ 2 * ct⁻¹) * σ := hconjσ (it ^ 2)
        _ = (it ^ 2 * σ) * σ := by rw [h]
        _ = it ^ 2 := by rw [mul_assoc, hσ2, mul_one]
    have h3 : ct ^ 3 * it ^ 2 * (ct ^ 3)⁻¹ = it ^ 2 * σ := by
      calc ct ^ 3 * it ^ 2 * (ct ^ 3)⁻¹ = ct * (ct ^ 2 * it ^ 2 * (ct ^ 2)⁻¹) * ct⁻¹ := by
            group
        _ = ct * it ^ 2 * ct⁻¹ := by rw [h2]
        _ = it ^ 2 * σ := h
    have h3' : it ^ 2 = it ^ 2 * σ := by simpa [hct3] using h3
    have hσeq : 1 = σ := by
      have := congrArg (fun x => (it ^ 2)⁻¹ * x) h3'
      simpa [mul_assoc] using this
    exact hσ1 hσeq.symm

private lemma lift_relations {E : Type} [Group E] (ρ : E →* SL23)
    {σ : E} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hσc : ∀ e : E, e * σ = σ * e)
    (hker : ∀ e : E, ρ e = 1 ↔ e = 1 ∨ e = σ)
    (ct it jt : E) (hρit : ρ it = slI) (hρjt : ρ jt = slJ)
    (hctit : ct * it * ct⁻¹ = jt) (hctjt : ct * jt * ct⁻¹ = it * jt)
    (hctα : ct * it ^ 2 * ct⁻¹ = it ^ 2) :
    jt ^ 2 = it ^ 2 ∧ jt * it * jt⁻¹ = it⁻¹ ∧ it ^ 4 = 1 := by
  have hjt2 : jt ^ 2 = it ^ 2 := by
    rw [← hctit]
    calc (ct * it * ct⁻¹) ^ 2 = ct * it ^ 2 * ct⁻¹ := by simp only [pow_two]; group
      _ = it ^ 2 := hctα
  have hρconj2 : ρ (jt * it * jt⁻¹) = ρ (it⁻¹) := by
    simp only [map_mul, map_inv, hρjt, hρit, slJ_conj_I]
  have hkerconj2 : (jt * it * jt⁻¹) * it ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, hρconj2, map_inv, inv_mul_cancel]
  have hcases2 : (jt * it * jt⁻¹) * it = 1 ∨ (jt * it * jt⁻¹) * it = σ :=
    (hker _).mp hkerconj2
  have hconj : jt * it * jt⁻¹ = it⁻¹ := by
    rcases hcases2 with h | h
    · have := congrArg (· * it⁻¹) h
      simpa [mul_assoc] using this
    · exfalso
      have hx : jt * it * jt⁻¹ = it⁻¹ * σ := by
        have : jt * it * jt⁻¹ = σ * it⁻¹ := by
          have := congrArg (· * it⁻¹) h
          simpa [mul_assoc] using this
        rw [this, hσc (it⁻¹)]
      have hkt2 : (it * jt) ^ 2 = it ^ 2 := by
        calc (it * jt) ^ 2 = (ct * jt * ct⁻¹) ^ 2 := by rw [← hctjt]
          _ = ct * jt ^ 2 * ct⁻¹ := by simp only [pow_two]; group
          _ = ct * it ^ 2 * ct⁻¹ := by rw [hjt2]
          _ = it ^ 2 := hctα
      have hitjt2 : (it * jt) ^ 2 = σ * it ^ 2 := by
        calc (it * jt) ^ 2 = it * (jt * it * jt⁻¹) * jt ^ 2 := by
              simp only [pow_two]; group
          _ = it * (it⁻¹ * σ) * it ^ 2 := by rw [hx, hjt2]
          _ = σ * it ^ 2 := by group
      rw [hitjt2] at hkt2
      have hσeq : σ = 1 := by
        have := congrArg (fun x => x * (it ^ 2)⁻¹) hkt2
        simpa [mul_assoc] using this
      exact hσ1 hσeq
  have hit4 : it ^ 4 = 1 := by
    have h1 : jt * it ^ 2 * jt⁻¹ = (jt * it * jt⁻¹) ^ 2 := by
      simp only [pow_two]; group
    have h2 : jt * it ^ 2 * jt⁻¹ = it ^ 2 := by
      rw [← hjt2]
      group
    have hαinv : it ^ 2 = (it ^ 2)⁻¹ := by
      rw [h2] at h1
      rw [hconj] at h1
      nth_rewrite 1 [h1]
      group
    have hα2 : it ^ 2 * it ^ 2 = 1 := by
      have := congrArg (· * it ^ 2) hαinv
      simpa [mul_assoc] using this
    calc it ^ 4 = (it ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = it ^ 2 * it ^ 2 := by rw [pow_two]
      _ = 1 := hα2
  exact ⟨hjt2, hconj, hit4⟩

lemma l34g_sl23_lifts {E : Type} [Group E] [Finite E]
    (ρ : E →* SL23) (hρ : Function.Surjective ρ)
    {σ : E} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hσc : ∀ e : E, e * σ = σ * e)
    (hker : ∀ e : E, ρ e = 1 ↔ e = 1 ∨ e = σ) :
    ∃ ct it jt : E,
      ρ ct = slC ∧ ρ it = slI ∧ ρ jt = slJ ∧
      ct ^ 3 = 1 ∧ ct * it * ct⁻¹ = jt ∧
      it ^ 4 = 1 ∧ jt ^ 2 = it ^ 2 ∧ jt * it * jt⁻¹ = it⁻¹ ∧
      ct * jt * ct⁻¹ = it * jt := by
  obtain ⟨ct, hρct, hct3⟩ := lift_c ρ hρ hσ2 hσc hker
  obtain ⟨it, jt, hρit, hρjt, hctit, hctjt⟩ := lift_quaternion ρ hρ hσ2 hσc hker ct hρct
  have hctα := lift_ct_conj_it_sq ρ hσ2 hσ1 hσc hker ct it hρct hρit hct3
  obtain ⟨hjt2, hconj, hit4⟩ :=
    lift_relations ρ hσ2 hσ1 hσc hker ct it jt hρit hρjt hctit hctjt hctα
  exact ⟨ct, it, jt, hρct, hρit, hρjt, hct3, hctit, hit4, hjt2, hconj, hctjt⟩

end CFSG.OddStandard.SmallF3.Omega
