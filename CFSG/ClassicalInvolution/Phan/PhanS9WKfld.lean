module

public import CFSG.ClassicalInvolution.Phan.PhanS7Ctx

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

theorem emb_add (a b : W7 F) : emb (K := K) (a + b) = emb a + emb b := by
  funext s
  simp [emb]

theorem emb_sub (a b : W7 F) : emb (K := K) (a - b) = emb a - emb b := by
  funext s
  simp [emb]

theorem emb_neg (a : W7 F) : emb (K := K) (-a) = -emb a := by
  funext s
  simp [emb]

theorem emb_smul (c : F) (a : W7 F) : emb (K := K) (c • a) = algebraMap F K c • emb a := by
  funext s
  simp [emb]

theorem conjV_emb (a : W7 F) : conjV D (emb a) = emb a := by
  funext s
  simp [conjV_apply, emb, D.tau_alg]

theorem quad_emb (a : W7 F) :
    quadOdd 3 K (emb a) = algebraMap F K (quadOdd 3 F a) := by
  simp only [quadOdd_apply, emb, map_add, map_mul, map_sum, map_pow]

theorem theta_mul_self : D.θ * D.θ = -1 := by
  rw [← _root_.sq]
  exact D.theta_sq

theorem kdat_theta_ne_zero : D.θ ≠ 0 := by
  intro h
  have := D.theta_sq
  rw [h] at this
  simp at this

theorem theta_indep (h2 : (2 : K) ≠ 0) {u v : F}
    (h : algebraMap F K u + D.θ * algebraMap F K v = 0) : u = 0 ∧ v = 0 := by
  have h' := congrArg D.τ h
  rw [map_add, map_mul, D.tau_alg, D.tau_alg, D.tau_theta, map_zero] at h'
  have h3 : (2 : K) * (D.θ * algebraMap F K v) = 0 := by linear_combination h - h'
  have h4 : algebraMap F K v = 0 := by
    rcases mul_eq_zero.1 h3 with h5 | h5
    · exact absurd h5 h2
    · rcases mul_eq_zero.1 h5 with h6 | h6
      · exact absurd h6 (kdat_theta_ne_zero D)
      · exact h6
  have hv : v = 0 := (map_eq_zero_iff _ (algebraMap F K).injective).1 h4
  refine ⟨?_, hv⟩
  rw [hv, map_zero, mul_zero, add_zero] at h
  exact (map_eq_zero_iff _ (algebraMap F K).injective).1 h

theorem exists_re_im (h2 : (2 : K) ≠ 0) (μ : K) :
    ∃ m₁ m₂ : F, μ = algebraMap F K m₁ + D.θ * algebraMap F K m₂ := by
  have hθ := kdat_theta_ne_zero D
  have h2τ : D.τ (2 : K) = 2 := map_ofNat D.τ 2
  obtain ⟨m₁, hm₁⟩ := D.fixed ((μ + D.τ μ) / 2) (by
    rw [map_div₀, map_add, D.tau_tau, h2τ, add_comm])
  obtain ⟨m₂, hm₂⟩ := D.fixed ((μ - D.τ μ) / (2 * D.θ)) (by
    rw [map_div₀, map_sub, map_mul, D.tau_tau, h2τ, D.tau_theta]
    have : (2 * -D.θ : K) = -(2 * D.θ) := by ring
    rw [this, div_neg, ← neg_div, neg_sub])
  refine ⟨m₁, m₂, ?_⟩
  rw [hm₁, hm₂]
  field_simp
  ring

theorem exists_re_im_vec (h2 : (2 : K) ≠ 0) (x : W7 K) :
    ∃ a b : W7 F, x = emb a + D.θ • emb b := by
  choose m₁ m₂ hm using fun s => exists_re_im D h2 (x s)
  refine ⟨m₁, m₂, ?_⟩
  funext s
  simp only [Pi.add_apply, Pi.smul_apply, emb, smul_eq_mul]
  exact hm s

theorem conjV_re_im (a b : W7 F) :
    conjV D (emb a + D.θ • emb b) = emb a - D.θ • emb b := by
  rw [conjV_add, conjV_smul, conjV_emb, conjV_emb, D.tau_theta, neg_smul, sub_eq_add_neg]

theorem quad_re_im (a b : W7 F) :
    quadOdd 3 K (emb a + D.θ • emb b) =
      algebraMap F K (quadOdd 3 F a - quadOdd 3 F b) +
        D.θ * algebraMap F K (polar (quadOdd 3 F) a b) := by
  rw [QuadraticMap.map_add (⇑(quadOdd 3 K)), QuadraticMap.map_smul, polar_smul_right, quad_emb,
    quad_emb,
    ← polar_emb, smul_eq_mul, smul_eq_mul, map_sub]
  have := D.theta_sq
  linear_combination (algebraMap F K (quadOdd 3 F b)) * this

theorem polar_re_im_emb (a b r : W7 F) :
    polar (quadOdd 3 K) (emb a + D.θ • emb b) (emb r) =
      algebraMap F K (polar (quadOdd 3 F) a r) +
        D.θ * algebraMap F K (polar (quadOdd 3 F) b r) := by
  rw [polar_add_left, polar_smul_left, polar_emb, polar_emb, smul_eq_mul]

theorem hrm_re_im (a b : W7 F) :
    hrm D (emb a + D.θ • emb b) (emb a + D.θ • emb b) =
      algebraMap F K (polar (quadOdd 3 F) a a + polar (quadOdd 3 F) b b) := by
  rw [hrm, conjV_re_im, sub_eq_add_neg, ← neg_smul, polar_add_left, polar_add_right,
    polar_add_right, polar_smul_left, polar_smul_left, polar_smul_right, polar_smul_right,
    polar_emb, polar_emb, polar_emb, polar_emb, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, map_add, QuadraticMap.polar_comm (quadOdd 3 F) b a]
  have := D.theta_sq
  linear_combination (-(algebraMap F K (polar (quadOdd 3 F) b b))) * this

theorem ff_parts (h2 : (2 : K) ≠ 0) {a b : W7 F} (hx : IsFF7 D (emb a + D.θ • emb b)) :
    quadOdd 3 F a = quadOdd 3 F b ∧ polar (quadOdd 3 F) a b = 0 ∧ quadOdd 3 F a ≠ 0 := by
  have h1 := hx.1
  rw [quad_re_im] at h1
  obtain ⟨hab, hp⟩ := theta_indep D h2 h1
  have hq : quadOdd 3 F a = quadOdd 3 F b := sub_eq_zero.1 hab
  refine ⟨hq, hp, fun h0 => hx.2 ?_⟩
  rw [hrm_re_im, QuadraticMap.polar_self, QuadraticMap.polar_self, ← hq, h0]
  simp

theorem polar_re_im_eq_zero (h2 : (2 : K) ≠ 0) {a b r : W7 F}
    (h : polar (quadOdd 3 K) (emb a + D.θ • emb b) (emb r) = 0) :
    polar (quadOdd 3 F) a r = 0 ∧ polar (quadOdd 3 F) b r = 0 := by
  rw [polar_re_im_emb] at h
  exact theta_indep D h2 h

end CFSG.ClassicalInvolution.PhanB3.S
