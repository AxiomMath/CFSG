module

public import CFSG.ClassicalInvolution.Phan.PhanQ10Pencil

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section Ffl

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem gram_comb (c d : V8 K) (α β γ δ : K) :
    gram D (α • c + β • d) (γ • c + δ • d) =
      ((α * δ - β * γ) * D.τ (α * δ - β * γ)) * gram D c d := by
  unfold gram
  simp only [her_add_left, her_add_right, her_smul_left, her_smul_right]
  simp only [map_sub, map_mul]
  ring

theorem gram_split (l₁ l₂ : K) {w p₁ p₂ : V8 K} (hw₁ : her D w p₁ = 0) (hw₁' : her D p₁ w = 0)
    (hw₂ : her D w p₂ = 0) (hw₂' : her D p₂ w = 0) (h12 : her D p₁ p₂ = 0)
    (h21 : her D p₂ p₁ = 0) :
    gram D (l₁ • w + p₁) (l₂ • w + p₂) =
      her D p₁ p₁ * her D p₂ p₂ +
        her D w w * (l₁ * D.τ l₁ * her D p₂ p₂ + l₂ * D.τ l₂ * her D p₁ p₁) := by
  unfold gram
  simp only [her_add_left, her_add_right, her_smul_left, her_smul_right, hw₁, hw₁', hw₂, hw₂',
    h12, h21]
  ring

theorem theta_ne_zero (hε : ε ≠ 0) : D.θ ≠ 0 := by
  intro h
  have h1 := D.theta_sq
  rw [h] at h1
  have h2 : algebraMap F K (-(1 / ε)) = 0 := by rw [← h1]; ring
  have h3 : -(1 / ε) = 0 := (map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective).1 h2
  have h4 : (1 : F) / ε = 0 := by linear_combination -h3
  exact one_div_ne_zero hε h4

theorem exists_tau0 (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {w u : V8 K} (hG : gram D u w ≠ 0) (T : K) :
    ∃ τ₀ : K, her D (w + τ₀ • u) (w + τ₀ • u) ≠ T := by
  by_contra hcon
  have hc : ∀ τ₀ : K, her D (w + τ₀ • u) (w + τ₀ • u) = T := fun τ₀ => by
    by_contra h
    exact hcon ⟨τ₀, h⟩
  have e : ∀ μ : K, her D (w + μ • u) (w + μ • u) = her D w w + D.τ μ * her D w u +
      μ * D.τ (her D w u) + μ * D.τ μ * her D u u := fun μ => her_pencil_self D w u μ
  have h0 := hc 0
  have h1 := hc 1
  have hm := hc (-1)
  have hθ := hc D.θ
  rw [e] at h0 h1 hm hθ
  simp only [map_zero, zero_mul, add_zero, map_one, one_mul, map_neg, neg_mul, mul_neg, mul_one,
    D.tau_theta] at h0 h1 hm hθ
  have hP : her D u u = 0 := by
    have : (2 : K) * her D u u = 0 := by linear_combination h1 + hm - 2 * h0
    exact (mul_eq_zero.1 this).resolve_left h2
  have hy1 : her D w u + D.τ (her D w u) = 0 := by linear_combination h1 - h0 - hP
  have hy2 : D.τ (her D w u) = her D w u := by
    have hθ0 := theta_ne_zero D hε
    have : D.θ * (D.τ (her D w u) - her D w u) = 0 := by
      rw [hP] at hθ
      linear_combination hθ - h0
    have := (mul_eq_zero.1 this).resolve_left hθ0
    linear_combination this
  have hy : her D w u = 0 := by
    have : (2 : K) * her D w u = 0 := by linear_combination hy1 - hy2
    exact (mul_eq_zero.1 this).resolve_left h2
  apply hG
  unfold gram
  rw [her_conj_symm D w u, hy, hP]
  simp

end Ffl

section PentK

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε) [Fintype K]
  [DecidableEq K]

theorem pentK (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {c d p₁ p₂ a : V8 K}
    (hc : ffK D c) (hd : ffK D d) (hcd : ColK D c d) (hp₁ : ffK D p₁) (hp₂ : ffK D p₂)
    (hB12 : B8 p₁ p₂ = 0) (hh12 : her D p₁ p₂ = 0)
    (hBc₁ : B8 c p₁ = 0) (hBc₂ : B8 c p₂ = 0) (hBd₁ : B8 d p₁ = 0) (hBd₂ : B8 d p₂ = 0)
    (hHc₁ : her D c p₁ = 0) (hHc₂ : her D c p₂ = 0) (hHd₁ : her D d p₁ = 0)
    (hHd₂ : her D d p₂ = 0) (ha : ffK D a) :
    ∃ f, ffK D f ∧ ColK D f c ∧ ColK D f d ∧ ColK D f a := by
  have hcc : B8 c c = 0 := by rw [B8_self, hc.1]; ring
  have hdd : B8 d d = 0 := by rw [B8_self, hd.1]; ring
  have hdc : B8 d c = 0 := by rw [B8_comm]; exact hcd.1
  by_cases h1 : B8 c a = 0 ∧ B8 d a = 0
  ·
    obtain ⟨μ, hff, hcol⟩ := exists_good_pencil D hq2 (m := 3) (by simpa using hq5)
      hc.1 hd.1 hcd.1 hcd.2 ![c, d, a] (fun i => by fin_cases i <;> simp [hc, hd, ha])
      (fun i => by fin_cases i <;> simp [hcc, hcd.1, h1.1])
      (fun i => by fin_cases i <;> simp [hdc, hdd, h1.2])
    exact ⟨c + μ • d, hff, hcol 0, hcol 1, hcol 2⟩
  ·
    obtain ⟨αw, βw, hw⟩ : ∃ αw βw : K, αw * B8 c a + βw * B8 d a = 1 := by
      rcases not_and_or.1 h1 with h | h
      · exact ⟨(B8 c a)⁻¹, 0, by rw [inv_mul_cancel₀ h]; ring⟩
      · exact ⟨0, (B8 d a)⁻¹, by rw [inv_mul_cancel₀ h]; ring⟩
    obtain ⟨w, hwdef⟩ : ∃ w : V8 K, w = αw • c + βw • d := ⟨_, rfl⟩
    obtain ⟨u₀, hu₀def⟩ : ∃ u₀ : V8 K, u₀ = B8 d a • c + (-(B8 c a)) • d := ⟨_, rfl⟩
    have hgram : gram D u₀ w ≠ 0 := by
      rw [hu₀def, hwdef, gram_comb]
      have : B8 d a * βw - -B8 c a * αw = 1 := by linear_combination hw
      rw [this]
      simpa using hcd.2
    obtain ⟨l₁, hl₁⟩ : ∃ l₁ : K, l₁ = -(B8 p₁ a) := ⟨_, rfl⟩
    obtain ⟨l₂, hl₂⟩ : ∃ l₂ : K, l₂ = -(B8 p₂ a) := ⟨_, rfl⟩
    have hh₁ : her D p₁ p₁ ≠ 0 := hp₁.2
    have hh₂ : her D p₂ p₂ ≠ 0 := hp₂.2
    obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : K, her D p₁ p₁ * her D p₂ p₂ +
        her D (w + τ₀ • u₀) (w + τ₀ • u₀) *
          (l₁ * D.τ l₁ * her D p₂ p₂ + l₂ * D.τ l₂ * her D p₁ p₁) ≠ 0 := by
      by_cases hγ : l₁ * D.τ l₁ * her D p₂ p₂ + l₂ * D.τ l₂ * her D p₁ p₁ = 0
      · exact ⟨0, by rw [hγ, mul_zero, add_zero]; exact mul_ne_zero hh₁ hh₂⟩
      · obtain ⟨τ₀, hτ₀⟩ := exists_tau0 D h2 hε hgram
          (-(her D p₁ p₁ * her D p₂ p₂) / (l₁ * D.τ l₁ * her D p₂ p₂ +
            l₂ * D.τ l₂ * her D p₁ p₁))
        refine ⟨τ₀, fun h0 => hτ₀ ?_⟩
        rw [eq_div_iff hγ]
        linear_combination h0
    obtain ⟨W, hWdef⟩ : ∃ W : V8 K, W = w + τ₀ • u₀ := ⟨_, rfl⟩
    obtain ⟨α', β', hWcomb⟩ : ∃ α' β' : K, W = α' • c + β' • d ∧
        α' * B8 c a + β' * B8 d a = 1 := by
      refine ⟨αw + τ₀ * B8 d a, βw + τ₀ * (-(B8 c a)), ?_, ?_⟩
      · rw [hWdef, hwdef, hu₀def]
        module
      · linear_combination hw
    obtain ⟨hWc, hWa'⟩ := hWcomb
    have hWB : ∀ z : V8 K, B8 c z = 0 → B8 d z = 0 → B8 W z = 0 := by
      intro z h1 h2
      rw [hWc, B8_lin_left, h1, h2]
      ring
    have hWa : B8 W a = 1 := by rw [hWc, B8_lin_left]; exact hWa'
    have hcW : B8 c W = 0 := by rw [hWc, B8_lin_right, hcc, hcd.1]; ring
    have hdW : B8 d W = 0 := by rw [hWc, B8_lin_right, hdc, hdd]; ring
    have hWW : B8 W W = 0 := hWB W hcW hdW
    have hWc0 : B8 W c = 0 := hWB c hcc hdc
    have hWd0 : B8 W d = 0 := hWB d hcd.1 hdd
    have hWp₁ : B8 W p₁ = 0 := hWB p₁ hBc₁ hBd₁
    have hWp₂ : B8 W p₂ = 0 := hWB p₂ hBc₂ hBd₂
    have hHW : ∀ z : V8 K, her D c z = 0 → her D d z = 0 → her D W z = 0 := by
      intro z h1 h2
      rw [hWc, her_add_left, her_smul_left, her_smul_left, h1, h2]
      ring
    have hHWp₁ : her D W p₁ = 0 := hHW p₁ hHc₁ hHd₁
    have hHWp₂ : her D W p₂ = 0 := hHW p₂ hHc₂ hHd₂
    have hHpW₁ : her D p₁ W = 0 := by rw [her_conj_symm D W p₁, hHWp₁, map_zero]
    have hHpW₂ : her D p₂ W = 0 := by rw [her_conj_symm D W p₂, hHWp₂, map_zero]
    have hh21 : her D p₂ p₁ = 0 := by rw [her_conj_symm D p₁ p₂, hh12, map_zero]
    have hp₁p₁ : B8 p₁ p₁ = 0 := by rw [B8_self, hp₁.1]; ring
    have hp₂p₂ : B8 p₂ p₂ = 0 := by rw [B8_self, hp₂.1]; ring
    have hp₁W : B8 p₁ W = 0 := by rw [B8_comm]; exact hWp₁
    have hp₂W : B8 p₂ W = 0 := by rw [B8_comm]; exact hWp₂
    have hp₁c : B8 p₁ c = 0 := by rw [B8_comm]; exact hBc₁
    have hp₁d : B8 p₁ d = 0 := by rw [B8_comm]; exact hBd₁
    have hp₂c : B8 p₂ c = 0 := by rw [B8_comm]; exact hBc₂
    have hp₂d : B8 p₂ d = 0 := by rw [B8_comm]; exact hBd₂
    obtain ⟨s, hsdef⟩ : ∃ s : V8 K, s = l₁ • W + p₁ := ⟨_, rfl⟩
    obtain ⟨t, htdef⟩ : ∃ t : V8 K, t = l₂ • W + p₂ := ⟨_, rfl⟩
    have hsB : ∀ z : V8 K, B8 s z = l₁ * B8 W z + B8 p₁ z := fun z => by
      rw [hsdef, B8_add_left, B8_smul_left]
    have htB : ∀ z : V8 K, B8 t z = l₂ * B8 W z + B8 p₂ z := fun z => by
      rw [htdef, B8_add_left, B8_smul_left]
    have hsc : B8 s c = 0 := by rw [hsB, hWc0, hp₁c]; ring
    have hsd : B8 s d = 0 := by rw [hsB, hWd0, hp₁d]; ring
    have hsa : B8 s a = 0 := by rw [hsB, hWa, hl₁]; ring
    have htc : B8 t c = 0 := by rw [htB, hWc0, hp₂c]; ring
    have htd : B8 t d = 0 := by rw [htB, hWd0, hp₂d]; ring
    have hta : B8 t a = 0 := by rw [htB, hWa, hl₂]; ring
    have hss : B8 s s = 0 := by
      rw [hsdef, B8_add_left, B8_smul_left, B8_add_right, B8_add_right, B8_smul_right,
        B8_smul_right, hWW, hWp₁, hp₁W, hp₁p₁]
      ring
    have htt : B8 t t = 0 := by
      rw [htdef, B8_add_left, B8_smul_left, B8_add_right, B8_add_right, B8_smul_right,
        B8_smul_right, hWW, hWp₂, hp₂W, hp₂p₂]
      ring
    have hst : B8 s t = 0 := by
      rw [hsdef, htdef, B8_add_left, B8_smul_left, B8_add_right, B8_add_right, B8_smul_right,
        B8_smul_right, hWW, hWp₂, hp₁W, hB12]
      ring
    have hQs : Q8 s = 0 := by
      have : (2 : K) * Q8 s = 0 := by rw [← B8_self]; exact hss
      exact (mul_eq_zero.1 this).resolve_left h2
    have hQt : Q8 t = 0 := by
      have : (2 : K) * Q8 t = 0 := by rw [← B8_self]; exact htt
      exact (mul_eq_zero.1 this).resolve_left h2
    have hG : gram D s t ≠ 0 := by
      rw [hsdef, htdef, gram_split D l₁ l₂ hHWp₁ hHpW₁ hHWp₂ hHpW₂ hh12 hh21]
      rw [← hWdef] at hτ₀
      exact hτ₀
    obtain ⟨μ, hff, hcol⟩ := exists_good_pencil D hq2 (m := 3) (by simpa using hq5) hQs hQt hst hG
      ![c, d, a] (fun i => by fin_cases i <;> simp [hc, hd, ha])
      (fun i => by fin_cases i <;> simp [hsc, hsd, hsa])
      (fun i => by fin_cases i <;> simp [htc, htd, hta])
    exact ⟨s + μ • t, hff, hcol 0, hcol 1, hcol 2⟩

end PentK

end CFSG.ClassicalInvolution.PhanQ
