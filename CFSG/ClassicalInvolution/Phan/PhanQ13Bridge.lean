module

public import CFSG.ClassicalInvolution.Phan.PhanQ11Pent

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section Ext

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

@[expose] def extV (K : Type) [Field K] [Algebra F K] (v : V8 F) : V8 K :=
  fun i => algebraMap F K (v i)

theorem B8_extV (u v : V8 F) :
    B8 (extV K u) (extV K v) = algebraMap F K (B8 u v) := by
  rw [B8_eq_sum, B8_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [extV]

theorem Q8_extV (v : V8 F) : Q8 (extV K v) = algebraMap F K (Q8 v) := by
  rw [Q8_eq_sum, Q8_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [extV]

theorem conj_comb (a b : K) (u v : V8 F) :
    conj D (a • extV K u + b • extV K v) = D.τ a • extV K u + D.τ b • extV K v := by
  ext i
  simp [conj, extV, D.tau_alg]

theorem B8_comb (a b a' b' : K) (u v u' v' : V8 F) :
    B8 (a • extV K u + b • extV K v) (a' • extV K u' + b' • extV K v') =
      a * a' * algebraMap F K (B8 u u') + a * b' * algebraMap F K (B8 u v') +
        b * a' * algebraMap F K (B8 v u') + b * b' * algebraMap F K (B8 v v') := by
  simp only [B8_add_left, B8_add_right, B8_smul_left, B8_smul_right, B8_extV]
  ring

theorem her_comb (a b a' b' : K) (u v u' v' : V8 F) :
    her D (a • extV K u + b • extV K v) (a' • extV K u' + b' • extV K v') =
      a * D.τ a' * algebraMap F K (B8 u u') + a * D.τ b' * algebraMap F K (B8 u v') +
        b * D.τ a' * algebraMap F K (B8 v u') + b * D.τ b' * algebraMap F K (B8 v v') := by
  rw [her, conj_comb, B8_comb]

theorem Q8_comb (a b : K) (u v : V8 F) :
    Q8 (a • extV K u + b • extV K v) =
      a ^ 2 * algebraMap F K (Q8 u) + b ^ 2 * algebraMap F K (Q8 v) +
        a * b * algebraMap F K (B8 u v) := by
  rw [Q8_lin, Q8_extV, Q8_extV, B8_extV]

@[expose] def vecK (z : NPair ε) : V8 K := (1 : K) • extV K z.x + D.θ • extV K z.y

end Ext

section Basic

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem two_ne_zero_of_algebra (h2 : (2 : K) ≠ 0) : (2 : F) ≠ 0 := fun h => by
  have := congrArg (algebraMap F K) h
  rw [map_ofNat, map_zero] at this
  exact h2 this

theorem four_ne_zero_of_algebra (h2 : (2 : K) ≠ 0) : (4 : F) ≠ 0 := by
  have : (4 : F) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero (two_ne_zero_of_algebra h2) (two_ne_zero_of_algebra h2)

theorem theta_indep (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {α β : F}
    (h : algebraMap F K α + D.θ * algebraMap F K β = 0) : α = 0 ∧ β = 0 := by
  have h' := congrArg D.τ h
  rw [map_add, map_mul, map_zero, D.tau_alg, D.tau_alg, D.tau_theta] at h'
  have h1 : (2 : K) * algebraMap F K α = 0 := by linear_combination h + h'
  have hα : algebraMap F K α = 0 := (mul_eq_zero.1 h1).resolve_left h2
  have hα' : α = 0 := (map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective).1 hα
  refine ⟨hα', ?_⟩
  rw [hα, zero_add] at h
  have hβ : algebraMap F K β = 0 := (mul_eq_zero.1 h).resolve_left (theta_ne_zero D hε)
  exact (map_eq_zero_iff (algebraMap F K) (algebraMap F K).injective).1 hβ

theorem theta_mul_theta : D.θ * D.θ = -algebraMap F K (1 / ε) := by
  rw [← _root_.sq, D.theta_sq, map_neg]

theorem B8_vecK (z w : NPair ε) :
    B8 (vecK D z) (vecK D w) = algebraMap F K (B8 z.x w.x + (-(1 / ε)) * B8 z.y w.y) +
      D.θ * algebraMap F K (B8 z.x w.y + B8 z.y w.x) := by
  unfold vecK
  rw [B8_comb]
  have h := theta_mul_theta D
  simp only [map_add, map_mul, map_neg, one_mul]
  linear_combination (algebraMap F K (B8 z.y w.y)) * h

theorem her_vecK (z w : NPair ε) :
    her D (vecK D z) (vecK D w) = algebraMap F K (B8 z.x w.x + (1 / ε) * B8 z.y w.y) +
      D.θ * algebraMap F K (B8 z.y w.x - B8 z.x w.y) := by
  unfold vecK
  rw [her_comb, D.tau_theta, map_one]
  have h := theta_mul_theta D
  simp only [map_add, map_mul, map_sub, one_mul, mul_one]
  linear_combination (-(algebraMap F K (B8 z.y w.y))) * h

theorem her_vecK_self (hε : ε ≠ 0) (z : NPair ε) :
    her D (vecK D z) (vecK D z) = algebraMap F K 4 := by
  rw [her_vecK]
  have e1 : B8 z.x z.x = 2 := by rw [B8_self, z.hx]; ring
  have e2 : B8 z.y z.y = 2 * ε := by rw [B8_self, z.hy]
  have e3 : B8 z.y z.x = 0 := by rw [B8_comm]; exact z.hxy
  have e4 : B8 z.x z.y = 0 := z.hxy
  rw [e1, e2, e3, e4, sub_zero, map_zero, mul_zero, add_zero]
  congr 1
  field_simp
  norm_num

theorem gram_vecK (hε : ε ≠ 0) (z w : NPair ε) :
    gram D (vecK D z) (vecK D w) = algebraMap F K (16 - (B8 z.x w.x + (1 / ε) * B8 z.y w.y) ^ 2 -
      (1 / ε) * (B8 z.y w.x - B8 z.x w.y) ^ 2) := by
  unfold gram
  rw [her_vecK_self D hε, her_vecK_self D hε, her_conj_symm D (vecK D z) (vecK D w), her_vecK]
  have h := theta_mul_theta D
  generalize B8 z.x w.x + (1 / ε) * B8 z.y w.y = P0
  generalize B8 z.y w.x - B8 z.x w.y = Q0
  simp only [map_add, map_mul, D.tau_alg, D.tau_theta, map_sub, map_pow, map_ofNat]
  linear_combination (algebraMap F K Q0) ^ 2 * h

theorem colP_arith (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) (b1 b2 b3 b4 : F) (e1 : b4 = ε * b1)
    (e2 : b2 = -b3) :
    (16 - (b1 + (1 / ε) * b4) ^ 2 - (1 / ε) * (b3 - b2) ^ 2 = 0) ↔ (b1 ^ 2 + b3 ^ 2 / ε = 4) := by
  subst e1 e2
  have key : 16 - (b1 + (1 / ε) * (ε * b1)) ^ 2 - (1 / ε) * (b3 - -b3) ^ 2 =
      4 * (4 - (b1 ^ 2 + b3 ^ 2 / ε)) := by
    field_simp
    ring
  rw [key]
  constructor
  · intro h
    have := (mul_eq_zero.1 h).resolve_left h4
    linear_combination -this
  · intro h
    rw [h]
    ring

theorem colK_vecK_iff (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {z w : NPair ε} :
    ColK D (vecK D z) (vecK D w) ↔ ColP ε z w := by
  have h4F : (4 : F) ≠ 0 := four_ne_zero_of_algebra (F := F) h2
  unfold ColK ColP
  rw [B8_vecK, gram_vecK D hε]
  constructor
  · rintro ⟨hB, hG⟩
    obtain ⟨h1, h2'⟩ := theta_indep D h2 hε hB
    have e1 : B8 z.y w.y = ε * B8 z.x w.x := by
      field_simp at h1
      linear_combination -h1
    have e2 : B8 z.x w.y = -B8 z.y w.x := by linear_combination h2'
    refine ⟨e1, h2', fun h4 => hG ?_⟩
    rw [map_eq_zero_iff _ (algebraMap F K).injective]
    exact (colP_arith hε h4F _ _ _ _ e1 e2).2 h4
  · rintro ⟨e1, e2, h4⟩
    have e3 : B8 z.x w.y = -B8 z.y w.x := by linear_combination e2
    refine ⟨?_, fun hG => h4 ?_⟩
    · have e1' : B8 z.x w.x + -(1 / ε) * B8 z.y w.y = 0 := by
        rw [e1]
        field_simp
        ring
      rw [e1', e2, map_zero, mul_zero, add_zero]
    · rw [map_eq_zero_iff _ (algebraMap F K).injective] at hG
      exact (colP_arith hε h4F _ _ _ _ e1 e3).1 hG

theorem ffK_vecK (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) (z : NPair ε) : ffK D (vecK D z) := by
  refine ⟨?_, ?_⟩
  · unfold vecK
    rw [Q8_comb, z.hx, z.hy, z.hxy, D.theta_sq]
    simp only [map_one, map_zero, mul_zero, add_zero, one_pow, one_mul]
    rw [← map_mul]
    have : -(1 / ε) * ε = -1 := by field_simp
    rw [this, map_neg, map_one]
    ring
  · rw [her_vecK_self D hε]
    exact (map_ne_zero _).2 (four_ne_zero_of_algebra (F := F) h2)

theorem exists_decomp (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) (k : K) :
    ∃ α β : F, k = algebraMap F K α + D.θ * algebraMap F K β := by
  have hθ := theta_ne_zero D hε
  obtain ⟨α, hα⟩ := D.fixed ((k + D.τ k) / 2)
    (by rw [map_div₀, map_add, D.tau_tau, map_ofNat, add_comm])
  obtain ⟨β, hβ⟩ := D.fixed ((k - D.τ k) / (2 * D.θ)) (by
    rw [map_div₀, map_sub, D.tau_tau, map_mul, map_ofNat, D.tau_theta]
    field_simp
    ring)
  refine ⟨α, β, ?_⟩
  rw [hα, hβ]
  field_simp
  ring

theorem exists_npair_of_ffK [Finite F] (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0)
    (hε : ε ≠ 0) {v : V8 K} (hv : ffK D v) :
    ∃ κ : K, κ ≠ 0 ∧ ∃ z : NPair ε, v = κ • vecK D z := by
  choose α β hαβ using fun i => exists_decomp D h2 hε (v i)
  have hv' : v = (1 : K) • extV K α + D.θ • extV K β := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, extV, smul_eq_mul, one_mul]
    exact hαβ i
  obtain ⟨hQ, hH⟩ := hv
  rw [hv', Q8_comb] at hQ
  rw [hv', her_comb] at hH
  have hQ' : algebraMap F K (Q8 α + (-(1 / ε)) * Q8 β) + D.θ * algebraMap F K (B8 α β) = 0 := by
    rw [map_add, map_mul, ← D.theta_sq]
    linear_combination hQ
  obtain ⟨hq1, hb⟩ := theta_indep D h2 hε hQ'
  have hq2 : Q8 β = ε * Q8 α := by
    field_simp at hq1
    linear_combination -hq1
  have hbb : B8 β α = 0 := by rw [B8_comm]; exact hb
  have hα2 : B8 α α = 2 * Q8 α := B8_self α
  have hβ2 : B8 β β = 2 * Q8 β := B8_self β
  have hq : Q8 α ≠ 0 := by
    intro h0
    apply hH
    simp [D.tau_theta, hb, hbb, hα2, hβ2, hq2, h0]
  obtain ⟨s, t, hst⟩ := exists_norm_eq hodd hε (Q8 α)⁻¹
  obtain ⟨n1, n2, n3⟩ := scale_pair_norms hε s t (ν := Q8 α) rfl hq2 hb
  let z : NPair ε := ⟨s • α + (-(t / ε)) • β, t • α + s • β,
    by rw [n1, hst, inv_mul_cancel₀ hq], by rw [n2, hst, inv_mul_cancel₀ hq, mul_one], n3⟩
  have ht : algebraMap F K (t / ε) = -(D.θ * D.θ) * algebraMap F K t := by
    rw [theta_mul_theta D, neg_neg, ← map_mul]
    congr 1
    ring
  have hz : vecK D z = (algebraMap F K s + D.θ * algebraMap F K t) • v := by
    ext i
    have hi := hαβ i
    show 1 * algebraMap F K (s * α i + (-(t / ε)) * β i) +
      D.θ * algebraMap F K (t * α i + s * β i) =
      (algebraMap F K s + D.θ * algebraMap F K t) * v i
    rw [hi]
    simp only [map_add, map_mul, map_neg, ht]
    ring
  have hne : algebraMap F K s + D.θ * algebraMap F K t ≠ 0 := by
    intro h0
    have := her_vecK_self D hε z
    rw [hz, h0, her_smul_left] at this
    have h4 : algebraMap F K 4 ≠ 0 := (map_ne_zero _).2 (four_ne_zero_of_algebra (F := F) h2)
    exact h4 (by rw [← this]; ring)
  refine ⟨(algebraMap F K s + D.θ * algebraMap F K t)⁻¹, inv_ne_zero hne, z, ?_⟩
  rw [hz, smul_smul, inv_mul_cancel₀ hne, one_smul]

end Basic

end CFSG.ClassicalInvolution.PhanQ
