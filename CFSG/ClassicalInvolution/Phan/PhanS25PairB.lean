module

public import CFSG.ClassicalInvolution.Phan.PhanS25Pair

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K]

theorem PairData.rot {M : Model K} {a c : Vec K} {γ η : K} (h : PairData M a c γ η) {ℓ : K}
    (hℓ : ℓ * M.τ ℓ = 1) : PairData M (ℓ • a) (ℓ⁻¹ • c) γ (ℓ * ℓ * η) := by
  have hℓ0 : ℓ ≠ 0 := left_ne_zero_of_mul_eq_one hℓ
  have hτ : M.τ ℓ = ℓ⁻¹ := eq_inv_of_mul_eq_one_right hℓ
  have hτ' : M.τ ℓ⁻¹ = ℓ := by rw [map_inv₀, hτ, inv_inv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bf_smul_left, bf_smul_right, h.ffa, mul_zero, mul_zero]
  · rw [bf_smul_left, bf_smul_right, h.ffc, mul_zero, mul_zero]
  · rw [bf_smul_left, bf_smul_right, h.bac]
    field_simp
  · rw [her_smul_left, her_smul_right, h.haa, hτ]
    field_simp
  · rw [her_smul_left, her_smul_right, h.hcc, hτ']
    field_simp
  · rw [her_smul_left, her_smul_right, h.hac, hτ']
    ring

theorem PairData.of_ff {M : Model K} {a c : Vec K} (ha : bf M a a = 0) (hc : bf M c c = 0)
    (hac : bf M a c ≠ 0) {s : K} (hs : s * M.τ s * her M a a = 1) :
    ∃ s' t' : K, s' ≠ 0 ∧ t' ≠ 0 ∧
      PairData M (s' • a) (t' • c) (her M (t' • c) (t' • c)) (her M (s' • a) (t' • c)) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hb : bf M (s • a) c ≠ 0 := by
    rw [bf_smul_left]
    exact mul_ne_zero hs0 hac
  refine ⟨s, (bf M (s • a) c)⁻¹, hs0, inv_ne_zero hb, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · rw [bf_smul_left, bf_smul_right, ha, mul_zero, mul_zero]
  · rw [bf_smul_left, bf_smul_right, hc, mul_zero, mul_zero]
  · rw [bf_smul_right]
    exact inv_mul_cancel₀ hb
  · rw [her_smul_left, her_smul_right, ← mul_assoc]
    exact hs

theorem rel_iff_of_regular {M : Model K} {a c a' c' : Vec K} {γ η : K}
    (hΔ : pairDisc γ η (M.τ η) ≠ 0) (hp : PairData M a c γ η) (hp' : PairData M a' c' γ η)
    (μ₁ μ₂ μ₃ μ₄ : K) : Rel M a c μ₁ μ₂ μ₃ μ₄ ↔ Rel M a' c' μ₁ μ₂ μ₃ μ₄ := by
  have key : ∀ {a c : Vec K}, PairData M a c γ η → (Rel M a c μ₁ μ₂ μ₃ μ₄ →
      μ₁ = 0 ∧ μ₂ = 0 ∧ μ₃ = 0 ∧ μ₄ = 0) := fun hp hr => by
    obtain ⟨e1, e2, e3, e4⟩ := hp.ker hr
    exact ker_zero_of_disc hΔ e1 e2 e3 e4
  have zero : (μ₁ = 0 ∧ μ₂ = 0 ∧ μ₃ = 0 ∧ μ₄ = 0) → ∀ a c : Vec K, Rel M a c μ₁ μ₂ μ₃ μ₄ := by
    rintro ⟨rfl, rfl, rfl, rfl⟩ a c
    exact Rel.zero M a c
  exact ⟨fun hr => zero (key hp hr) a' c', fun hr => zero (key hp' hr) a c⟩

@[expose] def Nvec (M : Model K) (γ η : K) (a c : Vec K) : Vec K :=
  (-(M.τ η * (γ - 1 - η * M.τ η + 2))) • a + (γ - 1 - η * M.τ η) • c +
    (-(γ - 1 - η * M.τ η + 2 * (η * M.τ η))) • tauV M a + (2 * M.τ η) • tauV M c

theorem rel_scaled_iff (M : Model K) (γ η : K) (a c : Vec K) (t : K) :
    Rel M a c (t * (-(M.τ η * (γ - 1 - η * M.τ η + 2)))) (t * (γ - 1 - η * M.τ η))
      (t * (-(γ - 1 - η * M.τ η + 2 * (η * M.τ η)))) (t * (2 * M.τ η)) ↔
        t • Nvec M γ η a c = 0 := by
  unfold Rel Nvec
  simp only [mul_smul, smul_add]

theorem rel_imp_of_line {M : Model K} {a c a' c' : Vec K} {γ η : K} (h2 : (2 : K) ≠ 0)
    (hη' : M.τ η ≠ 0) (hp : PairData M a c γ η)
    (hN : Nvec M γ η a c = 0 → Nvec M γ η a' c' = 0) {μ₁ μ₂ μ₃ μ₄ : K}
    (hr : Rel M a c μ₁ μ₂ μ₃ μ₄) : Rel M a' c' μ₁ μ₂ μ₃ μ₄ := by
  obtain ⟨e1, e2, e3, e4⟩ := hp.ker hr
  obtain ⟨t, h1, h2', h3, h4⟩ := ker_line h2 hη' e1 e2 e3
  subst h1 h2' h3 h4
  rw [rel_scaled_iff] at hr ⊢
  by_cases ht : t = 0
  · rw [ht, zero_smul]
  · have h0 : Nvec M γ η a c = 0 := (smul_eq_zero.mp hr).resolve_left ht
    rw [hN h0, smul_zero]

theorem rel_iff_of_line {M : Model K} {a c a' c' : Vec K} {γ η : K} (h2 : (2 : K) ≠ 0)
    (hη' : M.τ η ≠ 0) (hp : PairData M a c γ η) (hp' : PairData M a' c' γ η)
    (hN : Nvec M γ η a c = 0 ↔ Nvec M γ η a' c' = 0) (μ₁ μ₂ μ₃ μ₄ : K) :
    Rel M a c μ₁ μ₂ μ₃ μ₄ ↔ Rel M a' c' μ₁ μ₂ μ₃ μ₄ :=
  ⟨rel_imp_of_line h2 hη' hp hN.1, rel_imp_of_line h2 hη' hp' hN.2⟩

theorem disc_eq_zero_of_N {M : Model K} {a c : Vec K} {γ η : K} (h2 : (2 : K) ≠ 0)
    (hη' : M.τ η ≠ 0) (hp : PairData M a c γ η) (hN : Nvec M γ η a c = 0) :
    pairDisc γ η (M.τ η) = 0 := by
  have hr : Rel M a c (1 * (-(M.τ η * (γ - 1 - η * M.τ η + 2)))) (1 * (γ - 1 - η * M.τ η))
      (1 * (-(γ - 1 - η * M.τ η + 2 * (η * M.τ η)))) (1 * (2 * M.τ η)) := by
    rw [rel_scaled_iff, hN, smul_zero]
  obtain ⟨e1, e2, e3, e4⟩ := hp.ker hr
  have h4 := disc_mul_mu4 e1 e2 e3 e4
  exact (mul_eq_zero.mp h4).resolve_right (by simpa using mul_ne_zero h2 hη')

@[expose] def pvec (M : Model K) (a c : Vec K) : Vec K := a - tauV M c

theorem rel_special_iff {M : Model K} {a c : Vec K} (hp : PairData M a c 1 0)
    (μ₁ μ₂ μ₃ μ₄ : K) : Rel M a c μ₁ μ₂ μ₃ μ₄ ↔
      μ₃ = -μ₂ ∧ μ₄ = -μ₁ ∧ μ₁ • pvec M a c - μ₂ • tauV M (pvec M a c) = 0 := by
  have hσ : tauV M (pvec M a c) = tauV M a - c := by
    rw [pvec, pr_tauV_sub, tauV_tauV]
  constructor
  · intro hr
    obtain ⟨e1, e2, e3, e4⟩ := hp.ker hr
    have e1' : μ₂ + μ₃ + (0 : K) * μ₄ = 0 := by simpa using e1
    have e2' : μ₁ + (0 : K) * μ₃ + 1 * μ₄ = 0 := by simpa using e2
    obtain ⟨h3, h4⟩ := ker_special (γ := 1) (η := 0) rfl rfl e1' e2'
    refine ⟨h3, h4, ?_⟩
    rw [hσ, pvec]
    unfold Rel at hr
    rw [h3, h4] at hr
    rw [← hr]
    module
  · rintro ⟨h3, h4, h⟩
    unfold Rel
    rw [h3, h4]
    rw [hσ, pvec] at h
    rw [← h]
    module

theorem rel_iff_special {M : Model K} {a c a' c' : Vec K} (hp : PairData M a c 1 0)
    (hp' : PairData M a' c' 1 0)
    (h : ∀ s t : K, s • pvec M a c - t • tauV M (pvec M a c) = 0 ↔
      s • pvec M a' c' - t • tauV M (pvec M a' c') = 0) (μ₁ μ₂ μ₃ μ₄ : K) :
    Rel M a c μ₁ μ₂ μ₃ μ₄ ↔ Rel M a' c' μ₁ μ₂ μ₃ μ₄ := by
  rw [rel_special_iff hp, rel_special_iff hp', h]

theorem special_h_zero {M : Model K} {a c a' c' : Vec K} (h0 : pvec M a c = 0)
    (h0' : pvec M a' c' = 0) (s t : K) :
    s • pvec M a c - t • tauV M (pvec M a c) = 0 ↔
      s • pvec M a' c' - t • tauV M (pvec M a' c') = 0 := by
  simp [h0, h0', pr_tauV_zero]

theorem special_h_eigen {M : Model K} {a c a' c' : Vec K} {ν : K} (h0 : pvec M a c ≠ 0)
    (hσ : tauV M (pvec M a c) = ν • pvec M a c) (h0' : pvec M a' c' ≠ 0)
    (hσ' : tauV M (pvec M a' c') = ν • pvec M a' c') (s t : K) :
    s • pvec M a c - t • tauV M (pvec M a c) = 0 ↔
      s • pvec M a' c' - t • tauV M (pvec M a' c') = 0 := by
  have key : ∀ p : Vec K, p ≠ 0 → (s • p - t • (ν • p) = 0 ↔ s - t * ν = 0) := fun p hp => by
    have : s • p - t • (ν • p) = (s - t * ν) • p := by module
    rw [this, smul_eq_zero]
    simp [hp]
  rw [hσ, hσ', key _ h0, key _ h0']

theorem special_h_indep {M : Model K} {a c a' c' : Vec K}
    (hi : ∀ s t : K, s • pvec M a c - t • tauV M (pvec M a c) = 0 → s = 0 ∧ t = 0)
    (hi' : ∀ s t : K, s • pvec M a' c' - t • tauV M (pvec M a' c') = 0 → s = 0 ∧ t = 0)
    (s t : K) : s • pvec M a c - t • tauV M (pvec M a c) = 0 ↔
      s • pvec M a' c' - t • tauV M (pvec M a' c') = 0 := by
  constructor
  · intro h
    obtain ⟨rfl, rfl⟩ := hi s t h
    simp
  · intro h
    obtain ⟨rfl, rfl⟩ := hi' s t h
    simp

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
