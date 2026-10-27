module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Beta

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem msum8_xor (a b : ℕ) (f : ℕ → Mat8) : msum8 4 (a ^^^ b) f = msum8 4 a f + msum8 4 b f := by
  simp only [msum8, Nat.testBit_xor, bz_xor, add_smul, Finset.sum_add_distrib]

theorem deltaM_msum8 (ν : ℕ) (f : ℕ → Mat8) : deltaM (msum8 4 ν f) = msum8 4 ν (deltaM ∘ f) := by
  simp only [deltaM, msum8, Finset.mul_sum, Finset.sum_mul, Function.comp, mul_smul_comm,
    smul_mul_assoc, smul_add, Finset.sum_add_distrib]

theorem mat8_add_self' (X : Mat8) : X + X = 0 := matN_add_self X

theorem eq_of_add_eq_zero8 {X Y : Mat8} (h : X + Y = 0) : X = Y := by
  have := congrArg (· + Y) h
  simpa [add_assoc, mat8_add_self'] using this

theorem xor_lt16 {a b : ℕ} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 :=
  Nat.xor_lt_two_pow (n := 4) ha hb

theorem eq_of_msum8_eq {a b : ℕ} (ha : a < 16) (hb : b < 16)
    (h : msum8 4 a aM2 = msum8 4 b aM2) : a = b := by
  have h0 : msum8 4 (a ^^^ b) aM2 = 0 := by rw [msum8_xor, h, mat8_add_self']
  have := aIndep (xor_lt16 ha hb) h0
  exact Nat.eq_of_xor_eq_zero this

theorem msum8_two_pow (m : ℕ) (hm : m < 4) (f : ℕ → Mat8) : msum8 4 (2 ^ m) f = f m := by
  rw [msum8, Finset.sum_eq_single m]
  · rw [Nat.testBit_two_pow_self, bz_true, one_smul]
  · intro b _ hb
    rw [Nat.testBit_two_pow, decide_eq_false (Ne.symm hb), bz_false, zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr hm) h

theorem exists_mask_of_mem {X : Mat8} (hX : X ∈ aSpan2) : ∃ μ < 16, msum8 4 μ aM2 = X := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    refine ⟨2 ^ (m : ℕ), ?_, msum8_two_pow m m.isLt aM2⟩
    have := m.isLt
    interval_cases (m : ℕ) <;> norm_num
  | zero => exact ⟨0, by norm_num, by simp [msum8]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a ^^^ b, xor_lt16 ha hb, msum8_xor a b aM2⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
    · exact ⟨0, by norm_num, by simp [msum8]⟩
    · exact ⟨a, ha, by rw [one_smul]⟩

theorem tnCheck_spec {j : ℕ} (hj : j < 4) :
    tM2 * n0M2 j = n0M2 j * tM2 ∧ tM2 * n1M2 j = n1M2 j * tM2 := by
  have h := tnCheck_eq_true
  simp only [tnCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := (h.1 j hj)
  refine ⟨?_, ?_⟩
  · rw [tM2, n0M2, ← toMat_bmul, ← toMat_bmul, h1]
  · rw [tM2, n1M2, ← toMat_bmul, ← toMat_bmul, h2]

theorem deltaM_conj {j : ℕ} (hj : j < 4) (X : Mat8) :
    deltaM (n0M2 j * X * n1M2 j) = n0M2 j * deltaM X * n1M2 j := by
  obtain ⟨h0, h1⟩ := tnCheck_spec hj
  have key : tM2 * (n0M2 j * X * n1M2 j) * tM2 = n0M2 j * (tM2 * X * tM2) * n1M2 j := by
    calc tM2 * (n0M2 j * X * n1M2 j) * tM2 = (tM2 * n0M2 j) * X * (n1M2 j * tM2) := by
          simp only [mul_assoc]
      _ = (n0M2 j * tM2) * X * (tM2 * n1M2 j) := by rw [h0, h1]
      _ = n0M2 j * (tM2 * X * tM2) * n1M2 j := by simp only [mul_assoc]
  unfold deltaM
  rw [key, mul_add, add_mul]

theorem aConj_spec {j m : ℕ} (hj : j < 4) (hm : m < 4) :
    n0M2 j * aM2 m * n1M2 j = msum8 4 (cMask2 j m) aM2 ∧ deltaM (aM2 m) = 0 := by
  have h := aConjCheck2_eq_true
  simp only [aConjCheck2, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ⟨?_, ?_⟩
  · have := congrArg (toMat 8 8) (h.1 j hj m hm)
    rwa [toMat_bmul, toMat_bmul, toMat_msum2] at this
  · have := congrArg (toMat 8 8) (h.2 m hm)
    rwa [toMat_bxor, toMat_bmul, toMat_bmul, toMat_zero8'] at this

theorem deltaM_msum8_a (μ : ℕ) : deltaM (msum8 4 μ aM2) = 0 := by
  rw [deltaM_msum8]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Function.comp_apply, (aConj_spec (j := 0) (by norm_num) (Finset.mem_range.mp hq)).2,
    smul_zero]

section Span

variable {π : Γ →* (W →ₗ[ZMod 2] W)} {θ : SL3 →* Γ} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {W₀ V : Submodule (ZMod 2) W}
  {τ : Γ →* Γ} {e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)}

theorem R3bHyp.beta_mul_τ (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {x : Γ} (hx : x ∈ D) :
    betaG e π (x * τ x) = deltaM (betaG e π x) := by
  rw [h.beta_mul hK hx (h.τD x hx), h.beta_τ he hK hx, deltaM, add_comm]

theorem R3bHyp.delta_d (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {d : ℕ → Γ} (hd : ∀ n < 4, d n ∈ D)
    (hdτ : ∀ n < 4, d n * τ (d n) = θ (gen3 (Fin.ofNat 12 n))) {n : ℕ} (hn : n < 4) :
    deltaM (betaG e π (d n)) = aM2 n := by
  rw [← h.beta_mul_τ he hK (hd n hn), hdτ n hn, beta_E hK hn]

theorem R3bHyp.exists_span (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {d : ℕ → Γ} (hd : ∀ n < 4, d n ∈ D)
    (hdτ : ∀ n < 4, d n * τ (d n) = θ (gen3 (Fin.ofNat 12 n))) {x : Γ} (hx : x ∈ D) :
    ∃ μ < 16, ∃ ν < 16, x = dProd d ν * eProdG θ μ := by
  obtain ⟨μ, hμ, hwμ⟩ := h.τfix _ (mul_mem hx (h.τD x hx)) (h.τ_fixed hx)
  have hdx : betaG e π (x * τ x) = msum8 4 μ aM2 := by rw [hwμ, h.beta_eProdG hK]
  rw [h.beta_mul_τ he hK hx] at hdx
  set x' := x * dProd d μ with hx'
  have hx'D : x' ∈ D := mul_mem hx (h.dProd_mem hd μ)
  have hβ : betaG e π x' = betaG e π x + msum8 4 μ fun n => betaG e π (d n) := by
    rw [hx', h.beta_mul hK hx (h.dProd_mem hd μ), h.beta_dProd hK hd]
  have hδ : deltaM (betaG e π x') = 0 := by
    rw [hβ, deltaM_add, hdx, deltaM_msum8]
    rw [msum8_eq_of_lt (f := deltaM ∘ fun n => betaG e π (d n)) (g := aM2)
      fun n hn => h.delta_d he hK hd hdτ hn]
    exact mat8_add_self' _
  have h1 : betaG e π (τ x' * x') = 0 := by
    rw [h.beta_mul hK (h.τD x' hx'D) hx'D, h.beta_τ he hK hx'D]
    exact hδ
  have h2 : τ x' * x' = 1 := h.beta_inj he hK (mul_mem (h.τD x' hx'D) hx'D) h1
  have h3 : τ x' = x' := by
    have := eq_inv_of_mul_eq_one_left h2
    rw [this, h.inv_eq hx'D]
  obtain ⟨μ', hμ', hx'μ'⟩ := h.τfix x' hx'D h3
  refine ⟨μ', hμ', μ, hμ, ?_⟩
  have hdinv : (dProd d μ)⁻¹ = dProd d μ := h.inv_eq (h.dProd_mem hd μ)
  calc x = x' * (dProd d μ)⁻¹ := by rw [hx', mul_inv_cancel_right]
    _ = eProdG θ μ' * dProd d μ := by rw [hx'μ', hdinv]
    _ = dProd d μ * eProdG θ μ' := h.D_comm _ (eProdG_mem h μ') _ (h.dProd_mem hd μ)

theorem R3bHyp.nu_rel (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {d : ℕ → Γ} (hd : ∀ n < 4, d n ∈ D)
    (hdτ : ∀ n < 4, d n * τ (d n) = θ (gen3 (Fin.ofNat 12 n))) {j m : ℕ} (hj : j < 4)
    (hm : m < 4) : ∃ μ < 16,
      θ (gen3 (nuS j)) * d m * (θ (gen3 (nuS j)))⁻¹ = dProd d (cMask2 j m) * eProdG θ μ ∧
      n0M2 j * betaG e π (d m) * n1M2 j + (msum8 4 (cMask2 j m) fun n => betaG e π (d n)) +
        msum8 4 μ aM2 = 0 := by
  have hxD := h.ν_norm j hj (d m) (hd m hm)
  obtain ⟨μ, hμ, ν, hν, hx⟩ := h.exists_span he hK hd hdτ hxD
  have hβ := congrArg (betaG e π) hx
  rw [h.beta_ν hK hj (hd m hm), h.beta_mul hK (h.dProd_mem hd ν) (eProdG_mem h μ),
    h.beta_dProd hK hd, h.beta_eProdG hK] at hβ
  have hδ := congrArg deltaM hβ
  rw [deltaM_conj hj, h.delta_d he hK hd hdτ hm, (aConj_spec hj hm).1, deltaM_add,
    deltaM_msum8, deltaM_msum8_a, add_zero,
    msum8_eq_of_lt (f := deltaM ∘ fun n => betaG e π (d n)) (g := aM2)
      fun n hn => h.delta_d he hK hd hdτ hn] at hδ
  have hc : cMask2 j m < 16 := by
    interval_cases j <;> interval_cases m <;> decide
  have hνc : ν = cMask2 j m := (eq_of_msum8_eq hν hc hδ.symm)
  subst hνc
  refine ⟨μ, hμ, hx, ?_⟩
  rw [hβ]
  rw [show ∀ A B : Mat8, A + B + A + B = (A + A) + (B + B) by intros; abel, mat8_add_self',
    mat8_add_self', add_zero]

end Span

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
