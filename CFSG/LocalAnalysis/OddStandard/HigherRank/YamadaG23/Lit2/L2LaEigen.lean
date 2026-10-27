module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF

public section

open scoped Matrix

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem l2_la_eigen {K : Type} [Field K] (hK : (2 : K) ≠ 0) {n : ℕ} (hn : 0 < n)
    (a₁ a₂ : Matrix (Fin n) (Fin n) K) (ha₁ : a₁ * a₁ = 1) (ha₂ : a₂ * a₂ = 1)
    (h₁₂ : a₁ * a₂ = a₂ * a₁) :
    ∃ (e₁ e₂ : K) (w ψ : Fin n → K), e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧
      Matrix.mulVec a₁ w = e₁ • w ∧ Matrix.mulVec a₂ w = e₂ • w ∧
      Matrix.vecMul ψ a₁ = e₁ • ψ ∧ Matrix.vecMul ψ a₂ = e₂ • ψ ∧ dotProduct ψ w = 1 := by
  classical
  have h4 : (4 : K) ≠ 0 := by
    have h : (4 : K) = 2 * 2 := by ring
    rw [h]
    exact mul_ne_zero hK hK
  have hone : (1 : K) * 1 = 1 := by ring
  have hneg : (-1 : K) * (-1) = 1 := by ring
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
  have hFa1' : ∀ s1 s2, s1 * s1 = 1 → s2 * s2 = 1 →
      F s1 s2 * a₁ = s1 • F s1 s2 := by
    intro s1 s2 hs1 hs2
    show ((1 + s1 • a₁) * (1 + s2 • a₂)) * a₁ = s1 • ((1 + s1 • a₁) * (1 + s2 • a₂))
    rw [Matrix.mul_assoc, ← hcommA1 s2, ← Matrix.mul_assoc, hGmul s1 a₁ ha₁ hs1,
      Matrix.smul_mul]
  have hFa2 : ∀ s1 s2, s1 * s1 = 1 → s2 * s2 = 1 →
      a₂ * F s1 s2 = s2 • F s1 s2 := by
    intro s1 s2 hs1 hs2
    show a₂ * ((1 + s1 • a₁) * (1 + s2 • a₂)) = s2 • ((1 + s1 • a₁) * (1 + s2 • a₂))
    rw [← Matrix.mul_assoc, hcommA2 s1, Matrix.mul_assoc, hGmul' s2 a₂ ha₂ hs2,
      Matrix.mul_smul]
  have hFa2' : ∀ s1 s2, s1 * s1 = 1 → s2 * s2 = 1 →
      F s1 s2 * a₂ = s2 • F s1 s2 := by
    intro s1 s2 hs1 hs2
    show ((1 + s1 • a₁) * (1 + s2 • a₂)) * a₂ = s2 • ((1 + s1 • a₁) * (1 + s2 • a₂))
    rw [Matrix.mul_assoc, hGmul s2 a₂ ha₂ hs2, Matrix.mul_smul]
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
  have h1ne : (1 : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    intro h
    apply one_ne_zero (α := K)
    have h00 := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
    simpa using h00
  have hex : F 1 1 ≠ 0 ∨ F 1 (-1) ≠ 0 ∨ F (-1) 1 ≠ 0 ∨ F (-1) (-1) ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    have hz : F 1 1 + F 1 (-1) + F (-1) 1 + F (-1) (-1) = 0 := by
      rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
      simp
    rw [hsum] at hz
    have h00 : ((4 : K) • (1 : Matrix (Fin n) (Fin n) K)) ⟨0, hn⟩ ⟨0, hn⟩ = 0 := by
      rw [hz]
      rfl
    have h40 : (4 : K) = 0 := by
      simpa [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] using h00
    exact h4 h40
  have finish : ∀ (e₁ e₂ : K), e₁ * e₁ = 1 → e₂ * e₂ = 1 → F e₁ e₂ ≠ 0 →
      ∃ (w ψ : Fin n → K), Matrix.mulVec a₁ w = e₁ • w ∧ Matrix.mulVec a₂ w = e₂ • w ∧
        Matrix.vecMul ψ a₁ = e₁ • ψ ∧ Matrix.vecMul ψ a₂ = e₂ • ψ ∧ dotProduct ψ w = 1 := by
    intro e₁ e₂ he1 he2 hFne
    have hentry : ∃ i j, F e₁ e₂ i j ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hFne (by ext i j; exact h i j)
    obtain ⟨i0, j0, hij⟩ := hentry
    let w : Fin n → K := F e₁ e₂ *ᵥ Pi.single j0 1
    have hwi0 : w i0 ≠ 0 := by
      show (F e₁ e₂ *ᵥ Pi.single j0 1) i0 ≠ 0
      rw [Matrix.mulVec_single_one]
      simpa [Matrix.col_apply] using hij
    have hwne : w ≠ 0 := fun h => hwi0 (by rw [h]; rfl)
    have hFw : F e₁ e₂ *ᵥ w = (4 : K) • w := by
      show F e₁ e₂ *ᵥ (F e₁ e₂ *ᵥ Pi.single j0 1)
          = (4 : K) • (F e₁ e₂ *ᵥ Pi.single j0 1)
      rw [Matrix.mulVec_mulVec, hFsq e₁ e₂ he1 he2, Matrix.smul_mulVec]
    have hFwne : F e₁ e₂ *ᵥ w ≠ 0 := by
      rw [hFw]
      intro h
      have h0 : (4 : K) * w i0 = 0 := by
        have hh := congrFun h i0
        simpa using hh
      exact (mul_ne_zero h4 hwi0) h0
    have hpsi0 : ∃ p, (F e₁ e₂ *ᵥ w) p ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hFwne (funext h)
    obtain ⟨p, hp⟩ := hpsi0
    let ψ : Fin n → K := Pi.single p ((F e₁ e₂ *ᵥ w) p)⁻¹ ᵥ* F e₁ e₂
    refine ⟨w, ψ, ?_, ?_, ?_, ?_, ?_⟩
    · show a₁ *ᵥ w = e₁ • w
      dsimp only [w]
      rw [Matrix.mulVec_mulVec, hFa1 e₁ e₂ he1 he2, Matrix.smul_mulVec]
    · show a₂ *ᵥ w = e₂ • w
      dsimp only [w]
      rw [Matrix.mulVec_mulVec, hFa2 e₁ e₂ he1 he2, Matrix.smul_mulVec]
    · show ψ ᵥ* a₁ = e₁ • ψ
      dsimp only [w, ψ]
      rw [Matrix.vecMul_vecMul, hFa1' e₁ e₂ he1 he2, Matrix.vecMul_smul]
    · show ψ ᵥ* a₂ = e₂ • ψ
      dsimp only [w, ψ]
      rw [Matrix.vecMul_vecMul, hFa2' e₁ e₂ he1 he2, Matrix.vecMul_smul]
    · show ψ ⬝ᵥ w = 1
      dsimp only [w, ψ]
      rw [← Matrix.dotProduct_mulVec, single_dotProduct, inv_mul_cancel₀ hp]
  rcases hex with h11 | h1m | hm1 | hmm
  · obtain ⟨w, ψ, hw1, hw2, hψ1, hψ2, hψw⟩ := finish 1 1 hone hone h11
    exact ⟨1, 1, w, ψ, hone, hone, hw1, hw2, hψ1, hψ2, hψw⟩
  · obtain ⟨w, ψ, hw1, hw2, hψ1, hψ2, hψw⟩ := finish 1 (-1) hone hneg h1m
    exact ⟨1, -1, w, ψ, hone, hneg, hw1, hw2, hψ1, hψ2, hψw⟩
  · obtain ⟨w, ψ, hw1, hw2, hψ1, hψ2, hψw⟩ := finish (-1) 1 hneg hone hm1
    exact ⟨-1, 1, w, ψ, hneg, hone, hw1, hw2, hψ1, hψ2, hψw⟩
  · obtain ⟨w, ψ, hw1, hw2, hψ1, hψ2, hψw⟩ := finish (-1) (-1) hneg hneg hmm
    exact ⟨-1, -1, w, ψ, hneg, hneg, hw1, hw2, hψ1, hψ2, hψw⟩

end CFSG.OddStandard.HigherRank.YamadaG23
