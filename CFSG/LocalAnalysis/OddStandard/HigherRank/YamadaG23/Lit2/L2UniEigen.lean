module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF

public section

open scoped Matrix

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem l2_uni_eigen {K : Type} [Field K] (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (hK : (2 : K) ≠ 0) {n : ℕ} (hn : 0 < n) (a₁ a₂ : Matrix (Fin n) (Fin n) K)
    (ha₁ : a₁ * a₁ = 1) (ha₂ : a₂ * a₂ = 1) (hh₁ : (a₁.map σ)ᵀ = a₁) (hh₂ : (a₂.map σ)ᵀ = a₂)
    (h₁₂ : a₁ * a₂ = a₂ * a₁) :
    ∃ (e₁ e₂ c : K) (w : Fin n → K), e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ σ c = c ∧
      Matrix.mulVec a₁ w = e₁ • w ∧ Matrix.mulVec a₂ w = e₂ • w ∧
      Matrix.vecMul (c • (σ ∘ w)) a₁ = e₁ • (c • (σ ∘ w)) ∧
      Matrix.vecMul (c • (σ ∘ w)) a₂ = e₂ • (c • (σ ∘ w)) ∧
      dotProduct (c • (σ ∘ w)) w = 1 := by
  classical
  have h4 : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by ring
    rw [h]
    exact mul_ne_zero hK hK
  have hone : (1 : K) * 1 = 1 := by ring
  have hneg : (-1 : K) * (-1) = 1 := by ring
  have hσsign : ∀ s : K, s * s = 1 → σ s = s := by
    intro s hs
    rcases mul_self_eq_one_iff.mp hs with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
  have hGmul : ∀ (s : K) (a : Matrix (Fin n) (Fin n) K), a * a = 1 → s * s = 1 →
      (1 + s • a) * a = s • (1 + s • a) := by
    intro s a ha hs
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, ha, smul_add,
      smul_smul, hs, one_smul]
    abel
  have hGmul' : ∀ (s : K) (a : Matrix (Fin n) (Fin n) K), a * a = 1 → s * s = 1 →
      a * (1 + s • a) = s • (1 + s • a) := by
    intro s a ha hs
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ha, smul_add,
      smul_smul, hs, one_smul]
    abel
  have hGsq : ∀ (s : K) (a : Matrix (Fin n) (Fin n) K), a * a = 1 → s * s = 1 →
      (1 + s • a) * (1 + s • a) = (2 : K) • (1 + s • a) := by
    intro s a ha hs
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ha, hs, one_smul, two_smul]
    abel
  have hcommA1 : ∀ s : K, a₁ * (1 + s • a₂) = (1 + s • a₂) * a₁ := by
    intro s
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, h₁₂, Matrix.add_mul, Matrix.one_mul,
      Matrix.smul_mul]
  have hcommA2 : ∀ s : K, a₂ * (1 + s • a₁) = (1 + s • a₁) * a₂ := by
    intro s
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_mul, Matrix.one_mul,
      Matrix.smul_mul, h₁₂]
  let F : K → K → Matrix (Fin n) (Fin n) K := fun s1 s2 => (1 + s1 • a₁) * (1 + s2 • a₂)
  have hexpand : ∀ s1 s2 : K,
      (1 + s1 • a₁) * (1 + s2 • a₂)
        = 1 + s2 • a₂ + s1 • a₁ + (s1 * s2) • (a₁ * a₂) := by
    intro s1 s2
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    abel
  have hexpand₂ : ∀ s1 s2 : K,
      (1 + s2 • a₂) * (1 + s1 • a₁)
        = 1 + s1 • a₁ + s2 • a₂ + (s2 * s1) • (a₂ * a₁) := by
    intro s1 s2
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    abel
  have hG12 : ∀ s1 s2 : K, F s1 s2 = (1 + s2 • a₂) * (1 + s1 • a₁) := by
    intro s1 s2
    show (1 + s1 • a₁) * (1 + s2 • a₂) = (1 + s2 • a₂) * (1 + s1 • a₁)
    rw [hexpand s1 s2, hexpand₂ s1 s2, h₁₂, mul_comm s1 s2]
    abel
  have hmul4 : ∀ (G1 G2 : Matrix (Fin n) (Fin n) K), G1 * G2 = G2 * G1 →
      (G1 * G2) * (G1 * G2) = (G1 * G1) * (G2 * G2) := by
    intro G1 G2 h
    calc (G1 * G2) * (G1 * G2)
        = G1 * (G2 * (G1 * G2)) := by rw [Matrix.mul_assoc]
      _ = G1 * ((G2 * G1) * G2) := by
            congr 1
            exact (Matrix.mul_assoc G2 G1 G2).symm
      _ = G1 * ((G1 * G2) * G2) := by rw [h]
      _ = G1 * (G1 * (G2 * G2)) := by
            congr 1
            exact Matrix.mul_assoc G1 G2 G2
      _ = (G1 * G1) * (G2 * G2) := by rw [Matrix.mul_assoc]
  have hFsq : ∀ s1 s2, s1 * s1 = 1 → s2 * s2 = 1 →
      F s1 s2 * F s1 s2 = (4 : K) • F s1 s2 := by
    intro s1 s2 hs1 hs2
    have h1 := hGsq s1 a₁ ha₁ hs1
    have h2 := hGsq s2 a₂ ha₂ hs2
    have hc := hG12 s1 s2
    show ((1 + s1 • a₁) * (1 + s2 • a₂)) * ((1 + s1 • a₁) * (1 + s2 • a₂))
        = (4 : K) • ((1 + s1 • a₁) * (1 + s2 • a₂))
    rw [hmul4 (1 + s1 • a₁) (1 + s2 • a₂) hc, h1, h2, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, show (2 : K) * 2 = 4 by ring]
  have hFa1 : ∀ s1 s2, s1 * s1 = 1 → s2 * s2 = 1 →
      a₁ * F s1 s2 = s1 • F s1 s2 := by
    intro s1 s2 hs1 hs2
    show a₁ * ((1 + s1 • a₁) * (1 + s2 • a₂)) = s1 • ((1 + s1 • a₁) * (1 + s2 • a₂))
    rw [← Matrix.mul_assoc, hGmul' s1 a₁ ha₁ hs1, Matrix.smul_mul]
  have hFa2 : ∀ s1 s2, s1 * s1 = 1 → s2 * s2 = 1 →
      a₂ * F s1 s2 = s2 • F s1 s2 := by
    intro s1 s2 hs1 hs2
    show a₂ * ((1 + s1 • a₁) * (1 + s2 • a₂)) = s2 • ((1 + s1 • a₁) * (1 + s2 • a₂))
    rw [← Matrix.mul_assoc, hcommA2 s1, Matrix.mul_assoc, hGmul' s2 a₂ ha₂ hs2,
      Matrix.mul_smul]
  have hA2 : (1 : Matrix (Fin n) (Fin n) K) + a₂ + (1 + -a₂) = (2 : K) • 1 := by
    rw [two_smul]
    abel
  have hA1 : (1 : Matrix (Fin n) (Fin n) K) + a₁ + (1 + -a₁) = (2 : K) • 1 := by
    rw [two_smul]
    abel
  have hsum : F 1 1 + F 1 (-1) + F (-1) 1 + F (-1) (-1) = (4 : K) • 1 := by
    have htop : F 1 1 + F 1 (-1) = (2 : K) • (1 + a₁) := by
      dsimp only [F]
      simp only [one_smul, neg_one_smul]
      rw [← Matrix.mul_add, hA2, Matrix.mul_smul, Matrix.mul_one]
    have hbot : F (-1) 1 + F (-1) (-1) = (2 : K) • (1 + -a₁) := by
      dsimp only [F]
      simp only [one_smul, neg_one_smul]
      rw [← Matrix.mul_add, hA2, Matrix.mul_smul, Matrix.mul_one]
    have hgroup : F 1 1 + F 1 (-1) + F (-1) 1 + F (-1) (-1)
        = (F 1 1 + F 1 (-1)) + (F (-1) 1 + F (-1) (-1)) := by abel
    rw [hgroup, htop, hbot, ← smul_add, hA1, smul_smul, show (2 : K) * 2 = 4 by ring]
  have hFherm : ∀ s1 s2, σ s1 = s1 → σ s2 = s2 →
      ((F s1 s2).map σ)ᵀ = F s1 s2 := by
    intro s1 s2 hs1 hs2
    have hm1 : (((1 : Matrix (Fin n) (Fin n) K) + s1 • a₁).map σ)ᵀ = 1 + s1 • a₁ := by
      rw [Matrix.map_add σ σ.map_add, Matrix.map_one σ σ.map_zero σ.map_one,
        Matrix.map_smul' σ s1 a₁ σ.map_mul, hs1,
        Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hh₁]
    have hm2 : (((1 : Matrix (Fin n) (Fin n) K) + s2 • a₂).map σ)ᵀ = 1 + s2 • a₂ := by
      rw [Matrix.map_add σ σ.map_add, Matrix.map_one σ σ.map_zero σ.map_one,
        Matrix.map_smul' σ s2 a₂ σ.map_mul, hs2,
        Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hh₂]
    show ((((1 + s1 • a₁) * (1 + s2 • a₂)).map σ)ᵀ = (1 + s1 • a₁) * (1 + s2 • a₂))
    rw [Matrix.map_mul, Matrix.transpose_mul, hm2, hm1]
    exact (hG12 s1 s2).symm
  have herm_vecMul : ∀ (a : Matrix (Fin n) (Fin n) K), (a.map σ)ᵀ = a → ∀ w : Fin n → K,
      (σ ∘ w) ᵥ* a = σ ∘ (a *ᵥ w) := by
    intro a ha w
    ext j
    simp only [Function.comp_apply, Matrix.mulVec_apply_eq_sum, Matrix.vecMul_apply_eq_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [map_mul]
    have hEt : σ (a j t) = a t j := by
      have h := congrFun (congrFun ha t) j
      simpa [Matrix.transpose_apply, Matrix.map_apply] using h
    rw [hEt, mul_comm]
  have smul_comp : ∀ (s : K) (w : Fin n → K), σ s = s → σ ∘ (s • w) = s • (σ ∘ w) := by
    intro s w hs
    ext i
    simp [Function.comp_apply, hs]
  let E : K → K → Matrix (Fin n) (Fin n) K := fun s1 s2 => ((4 : K)⁻¹) • F s1 s2
  have hEa1 : ∀ s1 s2, s1 * s1 = 1 → s2 * s2 = 1 → a₁ * E s1 s2 = s1 • E s1 s2 := by
    intro s1 s2 hs1 hs2
    show a₁ * (((4 : K)⁻¹) • F s1 s2) = s1 • (((4 : K)⁻¹) • F s1 s2)
    rw [Matrix.mul_smul, hFa1 s1 s2 hs1 hs2, smul_smul, smul_smul, mul_comm]
  have hEa2 : ∀ s1 s2, s1 * s1 = 1 → s2 * s2 = 1 → a₂ * E s1 s2 = s2 • E s1 s2 := by
    intro s1 s2 hs1 hs2
    show a₂ * (((4 : K)⁻¹) • F s1 s2) = s2 • (((4 : K)⁻¹) • F s1 s2)
    rw [Matrix.mul_smul, hFa2 s1 s2 hs1 hs2, smul_smul, smul_smul, mul_comm]
  have hEsq : ∀ s1 s2, s1 * s1 = 1 → s2 * s2 = 1 → E s1 s2 * E s1 s2 = E s1 s2 := by
    intro s1 s2 hs1 hs2
    show (((4 : K)⁻¹) • F s1 s2) * (((4 : K)⁻¹) • F s1 s2) = ((4 : K)⁻¹) • F s1 s2
    rw [Matrix.smul_mul, Matrix.mul_smul, hFsq s1 s2 hs1 hs2, smul_smul, smul_smul,
      show (4 : K)⁻¹ * (4 : K)⁻¹ * 4 = (4 : K)⁻¹ by
        rw [mul_assoc, inv_mul_cancel₀ h4, mul_one]]
  have hEherm : ∀ s1 s2, σ s1 = s1 → σ s2 = s2 → ((E s1 s2).map σ)ᵀ = E s1 s2 := by
    intro s1 s2 hs1 hs2
    show (((((4 : K)⁻¹) • F s1 s2).map σ)ᵀ = ((4 : K)⁻¹) • F s1 s2)
    rw [Matrix.map_smul' σ ((4 : K)⁻¹) (F s1 s2) σ.map_mul, Matrix.transpose_smul,
      hFherm s1 s2 hs1 hs2,
      show σ ((4 : K)⁻¹) = (4 : K)⁻¹ by rw [map_inv₀, map_ofNat σ 4]]
  have hsumE : E 1 1 + E 1 (-1) + E (-1) 1 + E (-1) (-1) = 1 := by
    show ((4 : K)⁻¹) • F 1 1 + ((4 : K)⁻¹) • F 1 (-1)
        + ((4 : K)⁻¹) • F (-1) 1 + ((4 : K)⁻¹) • F (-1) (-1) = 1
    rw [← smul_add, ← smul_add, ← smul_add, hsum, smul_smul, inv_mul_cancel₀ h4, one_smul]
  have hermitian_key : ∀ (H : Matrix (Fin n) (Fin n) K), H * H = H → ((H.map σ)ᵀ = H) →
      ∀ v : Fin n → K,
        dotProduct (σ ∘ (H *ᵥ v)) (H *ᵥ v) = dotProduct (σ ∘ v) (H *ᵥ v) := by
    intro H hHsq hHherm v
    have h1 : σ ∘ (H *ᵥ v) = (σ ∘ v) ᵥ* H := by
      ext s
      simp only [Function.comp_apply, Matrix.mulVec_apply_eq_sum, Matrix.vecMul_apply_eq_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [map_mul]
      have hEt : σ (H s t) = H t s := by
        have h := congrFun (congrFun hHherm t) s
        simpa [Matrix.transpose_apply, Matrix.map_apply] using h
      rw [hEt, mul_comm]
    rw [h1, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hHsq]
  let i0 : Fin n := ⟨0, hn⟩
  let v : Fin n → K := Pi.single i0 1
  have hv : dotProduct (σ ∘ v) v = 1 := by
    have hcomp : σ ∘ v = v := by
      ext i
      by_cases hi : i = i0
      · subst hi
        simp [v]
      · simp [Function.comp_apply, v, Pi.single_eq_of_ne, hi]
    rw [hcomp]
    show dotProduct (Pi.single i0 (1 : K)) (Pi.single i0 (1 : K)) = 1
    rw [single_dotProduct, Pi.single_eq_same, mul_one]
  have hsumN : dotProduct (σ ∘ (E 1 1 *ᵥ v)) (E 1 1 *ᵥ v)
      + dotProduct (σ ∘ (E 1 (-1) *ᵥ v)) (E 1 (-1) *ᵥ v)
      + dotProduct (σ ∘ (E (-1) 1 *ᵥ v)) (E (-1) 1 *ᵥ v)
      + dotProduct (σ ∘ (E (-1) (-1) *ᵥ v)) (E (-1) (-1) *ᵥ v) = 1 := by
    have h11 := hermitian_key (E 1 1) (hEsq 1 1 hone hone)
      (hEherm 1 1 (hσsign 1 hone) (hσsign 1 hone)) v
    have h1m := hermitian_key (E 1 (-1)) (hEsq 1 (-1) hone hneg)
      (hEherm 1 (-1) (hσsign 1 hone) (hσsign (-1) hneg)) v
    have hm1 := hermitian_key (E (-1) 1) (hEsq (-1) 1 hneg hone)
      (hEherm (-1) 1 (hσsign (-1) hneg) (hσsign 1 hone)) v
    have hmm := hermitian_key (E (-1) (-1)) (hEsq (-1) (-1) hneg hneg)
      (hEherm (-1) (-1) (hσsign (-1) hneg) (hσsign (-1) hneg)) v
    rw [h11, h1m, hm1, hmm, ← dotProduct_add, ← dotProduct_add, ← dotProduct_add,
      ← Matrix.add_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec, hsumE, Matrix.one_mulVec, hv]
  have hex : dotProduct (σ ∘ (E 1 1 *ᵥ v)) (E 1 1 *ᵥ v) ≠ 0
      ∨ dotProduct (σ ∘ (E 1 (-1) *ᵥ v)) (E 1 (-1) *ᵥ v) ≠ 0
      ∨ dotProduct (σ ∘ (E (-1) 1 *ᵥ v)) (E (-1) 1 *ᵥ v) ≠ 0
      ∨ dotProduct (σ ∘ (E (-1) (-1) *ᵥ v)) (E (-1) (-1) *ᵥ v) ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    have hz : dotProduct (σ ∘ (E 1 1 *ᵥ v)) (E 1 1 *ᵥ v)
        + dotProduct (σ ∘ (E 1 (-1) *ᵥ v)) (E 1 (-1) *ᵥ v)
        + dotProduct (σ ∘ (E (-1) 1 *ᵥ v)) (E (-1) 1 *ᵥ v)
        + dotProduct (σ ∘ (E (-1) (-1) *ᵥ v)) (E (-1) (-1) *ᵥ v) = 0 := by
      rw [h.1, h.2.1, h.2.2.1, h.2.2.2, add_zero, add_zero, add_zero]
    rw [hsumN] at hz
    exact one_ne_zero hz
  have finish : ∀ (e₁ e₂ : K), e₁ * e₁ = 1 → e₂ * e₂ = 1 →
      dotProduct (σ ∘ (E e₁ e₂ *ᵥ v)) (E e₁ e₂ *ᵥ v) ≠ 0 →
      ∃ (c : K) (w : Fin n → K), σ c = c ∧
        Matrix.mulVec a₁ w = e₁ • w ∧ Matrix.mulVec a₂ w = e₂ • w ∧
        Matrix.vecMul (c • (σ ∘ w)) a₁ = e₁ • (c • (σ ∘ w)) ∧
        Matrix.vecMul (c • (σ ∘ w)) a₂ = e₂ • (c • (σ ∘ w)) ∧
        dotProduct (c • (σ ∘ w)) w = 1 := by
    intro e₁ e₂ he1 he2 hN
    let w : Fin n → K := E e₁ e₂ *ᵥ v
    have hNw : dotProduct (σ ∘ w) w ≠ 0 := by
      show dotProduct (σ ∘ (E e₁ e₂ *ᵥ v)) (E e₁ e₂ *ᵥ v) ≠ 0
      exact hN
    have hσN : σ (dotProduct (σ ∘ w) w) = dotProduct (σ ∘ w) w := by
      simp only [dotProduct, Function.comp_apply]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, hσ, mul_comm]
    have haw1 : Matrix.mulVec a₁ w = e₁ • w := by
      show Matrix.mulVec a₁ (E e₁ e₂ *ᵥ v) = e₁ • (E e₁ e₂ *ᵥ v)
      rw [Matrix.mulVec_mulVec, hEa1 e₁ e₂ he1 he2, Matrix.smul_mulVec]
    have haw2 : Matrix.mulVec a₂ w = e₂ • w := by
      show Matrix.mulVec a₂ (E e₁ e₂ *ᵥ v) = e₂ • (E e₁ e₂ *ᵥ v)
      rw [Matrix.mulVec_mulVec, hEa2 e₁ e₂ he1 he2, Matrix.smul_mulVec]
    have hψ1 : (σ ∘ w) ᵥ* a₁ = e₁ • (σ ∘ w) := by
      rw [herm_vecMul a₁ hh₁ w, haw1, smul_comp e₁ w (hσsign e₁ he1)]
    have hψ2 : (σ ∘ w) ᵥ* a₂ = e₂ • (σ ∘ w) := by
      rw [herm_vecMul a₂ hh₂ w, haw2, smul_comp e₂ w (hσsign e₂ he2)]
    refine ⟨(dotProduct (σ ∘ w) w)⁻¹, w, ?_, haw1, haw2, ?_, ?_, ?_⟩
    · rw [map_inv₀, hσN]
    · rw [Matrix.smul_vecMul, hψ1, smul_smul, smul_smul, mul_comm]
    · rw [Matrix.smul_vecMul, hψ2, smul_smul, smul_smul, mul_comm]
    · rw [smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hNw]
  rcases hex with h11 | h1m | hm1 | hmm
  · obtain ⟨c, w, hσc, hw1, hw2, hψ1, hψ2, hψw⟩ := finish 1 1 hone hone h11
    exact ⟨1, 1, c, w, hone, hone, hσc, hw1, hw2, hψ1, hψ2, hψw⟩
  · obtain ⟨c, w, hσc, hw1, hw2, hψ1, hψ2, hψw⟩ := finish 1 (-1) hone hneg h1m
    exact ⟨1, -1, c, w, hone, hneg, hσc, hw1, hw2, hψ1, hψ2, hψw⟩
  · obtain ⟨c, w, hσc, hw1, hw2, hψ1, hψ2, hψw⟩ := finish (-1) 1 hneg hone hm1
    exact ⟨-1, 1, c, w, hneg, hone, hσc, hw1, hw2, hψ1, hψ2, hψw⟩
  · obtain ⟨c, w, hσc, hw1, hw2, hψ1, hψ2, hψw⟩ := finish (-1) (-1) hneg hneg hmm
    exact ⟨-1, -1, c, w, hneg, hneg, hσc, hw1, hw2, hψ1, hψ2, hψw⟩

end CFSG.OddStandard.HigherRank.YamadaG23
