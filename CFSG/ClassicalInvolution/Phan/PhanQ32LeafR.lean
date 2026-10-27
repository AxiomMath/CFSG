module

public import CFSG.ClassicalInvolution.Phan.PhanQ31Hyp
public import CFSG.ClassicalInvolution.Phan.PhanQ23Generic
public import CFSG.ClassicalInvolution.Phan.PhanQ27Move

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

section LeafR

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} {D : KData F K ε}

theorem HypBasis.B8_vec_r {r r' s s' : V8 K} (H : HypBasis D r r' s s') (x1 x2 x3 x4 : K) :
    B8 (HypBasis.vec r r' s s' x1 x2 x3 x4) r = x2 := by
  have h := H.B8_vec x1 x2 x3 x4 1 0 0 0
  have e : HypBasis.vec r r' s s' 1 0 0 0 = r := by simp [HypBasis.vec]
  rw [e] at h
  rw [h]
  ring

theorem HypBasis.her_vec_vec {r r' s s' : V8 K} (H : HypBasis D r r' s s') (x1 x2 x3 x4 : K) :
    her D (HypBasis.vec r r' s s' x1 x2 x3 x4) (HypBasis.vec r r' s s' x1 x2 x3 x4) =
      x1 * D.τ x2 + x2 * D.τ x1 + x3 * D.τ x4 + x4 * D.τ x3 := by
  rw [her, H.conj_vec, H.B8_vec]

theorem HypBasis.exists_coord_ne {r r' s s' : V8 K} (H : HypBasis D r r' s s') :
    ∃ k, wc r k ≠ 0 := by
  by_contra h
  push Not at h
  have e : r = 0 := eq_of_wc_eq H.wr (fun i _ => ⟨rfl, rfl⟩) fun k => by
    rw [h k]
    fin_cases k <;> rfl
  have := H.rr'
  rw [e] at this
  simp [B8] at this

variable (D) [Fintype K] [DecidableEq K]

theorem resolved_R_core (h2 : (2 : K) ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {a b c d r : V8 K} (Fr : QFrame D a b c d)
    {ρc ρd : K} (hr : InW2 r) (hrr : B8 r r = 0) (hc : ∀ k, wc c k = ρc * wc r k)
    (hd : ∀ k, wc d k = ρd * wc r k) (hρd : ρd ≠ 0) (hrnz : ∃ k, wc r k ≠ 0) {t0 y : V8 K}
    (ht0W : InW0 t0) (hQt0 : Q8 t0 = 0) (hBt0b : B8 t0 b = 0) (hBt0c : B8 t0 c = -ρc)
    (hBt0d : B8 t0 d = -ρd) (hyW : InW2 y) (hyQ : Q8 y = 0) (hyr : B8 y r = 1)
    (hG : gram D c (t0 + y) ≠ 0) : Resolved D a b c d := by
  have hBty : B8 t0 y = 0 := B8_eq_zero_of_support ht0W hyW
  have hyc : B8 y c = ρc := by
    rw [B8_W2_of_coord hyW ρc hc, hyr, mul_one]
  have hyd : B8 y d = ρd := by
    rw [B8_W2_of_coord hyW ρd hd, hyr, mul_one]
  refine resolved_of_move D h2 hq2 hq5 Fr (t := t0 + y) ?_ ?_ ?_ ?_ hG ?_
  · rw [Q8_add', hQt0, hyQ, hBty]
    ring
  · rw [B8_add_right, B8_comm c t0, hBt0c, B8_comm c y, hyc]
    ring
  · rw [B8_add_left, hBt0b, B8_zero_of_W2_W0 hyW Fr.hb]
    ring
  · rw [B8_add_left, hBt0d, hyd]
    ring
  · intro μ hμ
    by_contra hcon
    push Not at hcon
    obtain ⟨l, m, hlm, hrel⟩ := exists_parallel_of_wedge_zero
      (X := wc (c + μ • (t0 + y))) (Y := wc d) (fun i j => hcon i j)
    have hl : l ≠ 0 := by
      intro hl0
      have hm : m ≠ 0 := by
        rcases hlm with h | h
        · exact absurd hl0 h
        · exact h
      obtain ⟨k, hk⟩ := hrnz
      have := hrel k
      rw [hl0, zero_mul, zero_add, hd k] at this
      have h3 : m * (ρd * wc r k) = 0 := this
      rcases mul_eq_zero.1 h3 with h | h
      · exact hm h
      · rcases mul_eq_zero.1 h with h' | h'
        · exact hρd h'
        · exact hk h'
    have hwy : ∀ k, wc y k = (-(l * ρc + m * ρd) / (l * μ)) * wc r k := by
      intro k
      have := hrel k
      rw [wc_add, wc_smul, wc_add, wc_of_inW0 ht0W, hc k, hd k] at this
      field_simp
      linear_combination this
    have hyeq : y = (-(l * ρc + m * ρd) / (l * μ)) • r :=
      eq_of_wc_eq hyW (inW2_smul' _ hr) fun k => by rw [wc_smul, hwy k]
    rw [hyeq, B8_smul_left, hrr, mul_zero] at hyr
    exact zero_ne_one hyr

theorem leaf_R (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) (hq2 : 2 ≤ Nat.card F)
    (hq5 : 4 * (Nat.card F + 1) < Nat.card F ^ 2) {a b c d r r' s s' : V8 K}
    (Fr : QFrame D a b c d) (H : HypBasis D r r' s s') {ρc ρd : K}
    (hc : ∀ k, wc c k = ρc * wc r k) (hd : ∀ k, wc d k = ρd * wc r k) (hρd : ρd ≠ 0)
    (hα : B8 a c ≠ 0) (hβ : B8 b d ≠ 0) : Resolved D a b c d := by
  have hrr : B8 r r = 0 := B8_zero_self H.qr
  have hrnz := H.exists_coord_ne
  obtain ⟨lam, hlam⟩ : ∃ lam : K, lam = -ρc / B8 a c := ⟨_, rfl⟩
  obtain ⟨mu, hmu⟩ : ∃ mu : K, mu = -ρd / B8 b d := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ : ∃ t0 : V8 K, t0 = lam • a + mu • b := ⟨_, rfl⟩
  have ht0W : InW0 t0 := by
    rw [ht0]
    exact inW0_add' (inW0_smul' lam Fr.ha) (inW0_smul' mu Fr.hb)
  have hbb : B8 b b = 0 := B8_zero_self Fr.hbf.1
  have hQt0 : Q8 t0 = 0 := by
    rw [ht0, Q8_lin, Fr.haf.1, Fr.hbf.1, Fr.hab.1]
    ring
  have hBt0b : B8 t0 b = 0 := by
    rw [ht0, B8_lin_left, Fr.hab.1, hbb]
    ring
  have hBt0c : B8 t0 c = -ρc := by
    rw [ht0, B8_lin_left, Fr.hbc.1, hlam]
    field_simp
    ring
  have hBad : B8 a d = 0 := by
    rw [B8_comm]
    exact Fr.hda.1
  have hBt0d : B8 t0 d = -ρd := by
    rw [ht0, B8_lin_left, hBad, hmu]
    field_simp
    ring
  obtain ⟨H0, hH0⟩ : ∃ H0 : K, H0 = her D t0 t0 := ⟨_, rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ G0 : K, G0 = her D c t0 + ρc := ⟨_, rfl⟩
  have gramR : ∀ y : V8 K, InW2 y → B8 (conj D y) r = 1 →
      gram D c (t0 + y) = her D c c * (H0 + her D y y) - G0 * D.τ G0 := by
    intro y hyW hyr'
    have hcy : her D c y = ρc := by
      rw [her, B8_comm, B8_W2_of_coord (inW2_conj D hyW) ρc hc, hyr', mul_one]
    have e1 : her D (t0 + y) (t0 + y) = H0 + her D y y := by
      rw [her_add_left, her_add_right, her_add_right, her_zero_of_W0_W2 D ht0W hyW,
        her_zero_of_W2_W0 D hyW ht0W, hH0]
      ring
    have e2 : her D c (t0 + y) = G0 := by
      rw [her_add_right, hcy, hG0]
    have e3 : her D (t0 + y) c = D.τ G0 := by
      rw [her_conj_symm D c (t0 + y), e2]
    unfold gram
    rw [e1, e2, e3]
  have hcc : her D c c ≠ 0 := Fr.hcf.2
  have hθ : D.θ ≠ 0 := theta_ne_zero D hε
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  by_cases hg : her D c c * (H0 + 0) - G0 * D.τ G0 = 0
  · have hy₂W := H.inW2_vec (-(D.θ * D.θ)) 1 D.θ D.θ
    have hy₂Q : Q8 (HypBasis.vec r r' s s' (-(D.θ * D.θ)) 1 D.θ D.θ) = 0 := by
      rw [H.Q8_vec h2]
      ring
    have hy₂r : B8 (HypBasis.vec r r' s s' (-(D.θ * D.θ)) 1 D.θ D.θ) r = 1 := by
      rw [H.B8_vec_r]
    have hy₂r' : B8 (conj D (HypBasis.vec r r' s s' (-(D.θ * D.θ)) 1 D.θ D.θ)) r = 1 := by
      rw [H.conj_vec, H.B8_vec_r, map_one]
    have hhy : her D (HypBasis.vec r r' s s' (-(D.θ * D.θ)) 1 D.θ D.θ)
        (HypBasis.vec r r' s s' (-(D.θ * D.θ)) 1 D.θ D.θ) = -(4 * D.θ ^ 2) := by
      rw [H.her_vec_vec]
      simp only [map_neg, map_mul, map_one, D.tau_theta]
      ring
    refine resolved_R_core D h2 hq2 hq5 Fr H.wr hrr hc hd hρd hrnz ht0W hQt0 hBt0b hBt0c hBt0d
      hy₂W hy₂Q hy₂r ?_
    rw [gramR _ hy₂W hy₂r', hhy]
    have e : her D c c * (H0 + -(4 * D.θ ^ 2)) - G0 * D.τ G0 = her D c c * (-(4 * D.θ ^ 2)) := by
      linear_combination hg
    rw [e]
    exact mul_ne_zero hcc (neg_ne_zero.2 (mul_ne_zero h4 (pow_ne_zero 2 hθ)))
  · have hy₁W := H.inW2_vec 0 1 0 0
    have hy₁Q : Q8 (HypBasis.vec r r' s s' 0 1 0 0) = 0 := by
      rw [H.Q8_vec h2]
      ring
    have hy₁r : B8 (HypBasis.vec r r' s s' 0 1 0 0) r = 1 := by
      rw [H.B8_vec_r]
    have hy₁r' : B8 (conj D (HypBasis.vec r r' s s' 0 1 0 0)) r = 1 := by
      rw [H.conj_vec, H.B8_vec_r, map_one]
    have hhy : her D (HypBasis.vec r r' s s' 0 1 0 0) (HypBasis.vec r r' s s' 0 1 0 0) = 0 := by
      rw [H.her_vec_vec]
      simp
    refine resolved_R_core D h2 hq2 hq5 Fr H.wr hrr hc hd hρd hrnz ht0W hQt0 hBt0b hBt0c hBt0d
      hy₁W hy₁Q hy₁r ?_
    rw [gramR _ hy₁W hy₁r', hhy]
    exact hg

end LeafR

end CFSG.ClassicalInvolution.PhanQ
