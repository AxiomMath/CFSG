module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2Phi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy2Cos

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {t rho : G} {Z E W Q : Subgroup G}

private theorem fzc_sy2_rho_ne_mem (hs : FzCSy2Str t rho Z E W Q) {x : G} (hxW : x ∉ W) :
    rho * x * rho⁻¹ ∉ W := by
  intro h
  apply hxW
  have h1 : rho * (rho * x * rho⁻¹) * rho⁻¹ ∈ W := hs.rho_nrm_W _ h
  have h2 : rho * (rho * (rho * x * rho⁻¹) * rho⁻¹) * rho⁻¹ ∈ W := hs.rho_nrm_W _ h1
  rwa [hs.rho_conj3 x] at h2

theorem fzc_sy2_sq_coset (hs : FzCSy2Str t rho Z E W Q) {x : G} (hx : x ∈ Q) (hxW : x ∉ W)
    (hxZ : x ^ 2 ∈ Z) {w : G} (hw : w ∈ W) : (w * x) ^ 2 ∈ Z := by
  set w' : G := x * w * x⁻¹ with hw'def
  have hw' : w' ∈ W := by rw [hw'def]; exact hs.W_nrm x hx w hw
  set c : G := w' * w⁻¹ with hcdef
  have hcW : c ∈ W := by rw [hcdef]; exact W.mul_mem hw' (W.inv_mem hw)
  have hcw : Commute w w' := hs.W_comm w hw w' hw'
  have hc2 : c ^ 2 = 1 := by
    have hw'2 : w' ^ 2 = w ^ 2 := by
      rw [hw'def, conj_pow]
      exact hs.Q_Z x hx (w ^ 2) (hs.W_sq w hw)
    calc c ^ 2 = w' ^ 2 * (w⁻¹) ^ 2 := by
          rw [hcdef]
          exact (hcw.symm.inv_right).mul_pow 2
      _ = w ^ 2 * (w ^ 2)⁻¹ := by rw [hw'2, inv_pow]
      _ = 1 := by group
  have hww' : w * w' = c * w ^ 2 := by
    rw [hcdef]
    calc w * w' = w' * w := hs.W_comm w hw w' hw'
      _ = w' * w⁻¹ * (w * w) := by group
      _ = w' * w⁻¹ * w ^ 2 := by rw [pow_two]
  have hwx2 : (w * x) ^ 2 = c * w ^ 2 * x ^ 2 := by
    calc (w * x) ^ 2 = w * w' * x ^ 2 := by
          rw [pow_two, hw'def]; group
      _ = c * w ^ 2 * x ^ 2 := by rw [hww']
  rcases hs.W_invol c hcW hc2 with hcZ | htcZ
  · rw [hwx2]
    exact Z.mul_mem (Z.mul_mem hcZ (hs.W_sq w hw)) hxZ
  · exfalso
    set z : G := t * c * w ^ 2 * x ^ 2 with hzdef
    have hzZ : z ∈ Z := by
      rw [hzdef]
      exact Z.mul_mem (Z.mul_mem htcZ (hs.W_sq w hw)) hxZ
    have ht_z : t * z = c * w ^ 2 * x ^ 2 := by
      have htt : t * t = 1 := by rw [← pow_two, hs.t_sq]
      rw [hzdef]
      calc t * (t * c * w ^ 2 * x ^ 2) = (t * t) * (c * w ^ 2 * x ^ 2) := by group
        _ = c * w ^ 2 * x ^ 2 := by rw [htt, one_mul]
    have hnW : w * x ∉ W := by
      intro h
      apply hxW
      have hx_eq : x = w⁻¹ * (w * x) := by group
      rw [hx_eq]
      exact W.mul_mem (W.inv_mem hw) h
    have hnQ : w * x ∈ Q := Q.mul_mem (hs.WQ hw) hx
    have hn2 : (w * x) ^ 2 = t * z := hwx2.trans ht_z.symm
    have hnt : w * x * t * (w * x)⁻¹ = t := by
      have h1 : (w * x) * (t * z) * (w * x)⁻¹ = t * z := by
        rw [← hn2]
        set n : G := w * x with hn_def
        show n * n ^ 2 * n⁻¹ = n ^ 2
        group
      have h2 : (w * x) * z * (w * x)⁻¹ = z := hs.Q_Z (w * x) hnQ z hzZ
      calc (w * x) * t * (w * x)⁻¹
          = ((w * x) * (t * z) * (w * x)⁻¹) *
              ((w * x) * z * (w * x)⁻¹)⁻¹ := by group
        _ = (t * z) * z⁻¹ := by rw [h1, h2]
        _ = t := by group
    exact hs.Q_t (w * x) hnQ hnW hnt

theorem fzc_sy2_rho_cosets [Finite G] (hs : FzCSy2Str t rho Z E W Q) {x : G} (hx : x ∈ Q)
    (hxW : x ∉ W) :
    ∀ q ∈ Q, q ∈ W ∨ q * x⁻¹ ∈ W ∨ q * (rho * x * rho⁻¹)⁻¹ ∈ W ∨
      q * (rho * (rho * x * rho⁻¹) * rho⁻¹)⁻¹ ∈ W := by
  set x₁ : G := rho * x * rho⁻¹ with hx₁def
  set x₂ : G := rho * x₁ * rho⁻¹ with hx₂def
  have hrho3 : rho * x₂ * rho⁻¹ = x := by
    rw [hx₂def, hx₁def]
    exact hs.rho_conj3 x
  have hx₁Q : x₁ ∈ Q := by rw [hx₁def]; exact hs.rho_nrm_Q x hx
  have hx₂Q : x₂ ∈ Q := by rw [hx₂def]; exact hs.rho_nrm_Q x₁ hx₁Q
  have hx₁W : x₁ ∉ W := by rw [hx₁def]; exact fzc_sy2_rho_ne_mem hs hxW
  have hx₂W : x₂ ∉ W := by rw [hx₂def]; exact fzc_sy2_rho_ne_mem hs hx₁W
  have hx₁xW : x₁ * x⁻¹ ∉ W := by
    intro h
    rw [hx₁def] at h
    exact hxW (hs.rho_QW x hx h)
  have hx₂xW : x₂ * x⁻¹ ∉ W := by
    intro h
    apply hx₂W
    have hxinv : x * x₂⁻¹ ∈ W := by simpa using W.inv_mem h
    have hrho : rho * x₂ * rho⁻¹ * x₂⁻¹ ∈ W := by rw [hrho3]; exact hxinv
    exact hs.rho_QW x₂ hx₂Q hrho
  have hx₂x₁W : x₂ * x₁⁻¹ ∉ W := by
    intro h
    apply hx₁xW
    have h₁ : rho * (x₂ * x₁⁻¹) * rho⁻¹ ∈ W := hs.rho_nrm_W _ h
    have h₂ : rho * (rho * (x₂ * x₁⁻¹) * rho⁻¹) * rho⁻¹ ∈ W := hs.rho_nrm_W _ h₁
    have heq : rho * (rho * (x₂ * x₁⁻¹) * rho⁻¹) * rho⁻¹ = x₁ * x⁻¹ := by
      have h1 : rho * (x₂ * x₁⁻¹) * rho⁻¹ =
          rho * (rho * (x₁ * x⁻¹) * rho⁻¹) * rho⁻¹ := by
        rw [hx₂def, hx₁def]; group
      rw [h1, hs.rho_conj3 (x₁ * x⁻¹)]
    rw [heq] at h₂
    exact h₂
  have hcard : Nat.card Q = 4 * Nat.card W := by
    rw [hs.card_Q, hs.card_W]
  have hfour := fzc_sy2_four_cosets (W := W) (Q := Q) hs.WQ hcard hs.W_nrm hs.Q_sq hs.Q_comm
    hx hxW hx₁Q hx₁W hx₁xW
  have h5 : x₂ * (x * x₁)⁻¹ ∈ W := by
    rcases hfour x₂ hx₂Q with h | h | h | h
    · exact absurd h hx₂W
    · exact absurd h hx₂xW
    · exact absurd h hx₂x₁W
    · exact h
  intro q hq
  rcases hfour q hq with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    have heq : q * x₂⁻¹ = (q * (x * x₁)⁻¹) * (x₂ * (x * x₁)⁻¹)⁻¹ := by group
    rw [heq]
    exact W.mul_mem h (W.inv_mem h5)

theorem fzc_sy2_sq_not_mem [Finite G] (hs : FzCSy2Str t rho Z E W Q)
    (hP : t ∈ ⁅Q, zpowers rho⁆) {x : G} (hx : x ∈ Q) (hxW : x ∉ W) : x ^ 2 ∉ Z := by
  intro hxZ
  set x₁ : G := rho * x * rho⁻¹ with hx₁def
  set x₂ : G := rho * x₁ * rho⁻¹ with hx₂def
  have hx₁Q : x₁ ∈ Q := by rw [hx₁def]; exact hs.rho_nrm_Q x hx
  have hx₂Q : x₂ ∈ Q := by rw [hx₂def]; exact hs.rho_nrm_Q x₁ hx₁Q
  have hx₁W : x₁ ∉ W := by rw [hx₁def]; exact fzc_sy2_rho_ne_mem hs hxW
  have hx₂W : x₂ ∉ W := by rw [hx₂def]; exact fzc_sy2_rho_ne_mem hs hx₁W
  have hx₁Z : x₁ ^ 2 ∈ Z := by
    have h : x₁ ^ 2 = rho * x ^ 2 * rho⁻¹ := by rw [hx₁def, conj_pow]
    rw [h]
    exact hs.rho_nrm_Z (x ^ 2) hxZ
  have hx₂Z : x₂ ^ 2 ∈ Z := by
    have h : x₂ ^ 2 = rho * x₁ ^ 2 * rho⁻¹ := by rw [hx₂def, conj_pow]
    rw [h]
    exact hs.rho_nrm_Z (x₁ ^ 2) hx₁Z
  have hQsq : ∀ q ∈ Q, q ^ 2 ∈ Z := by
    intro q hq
    rcases fzc_sy2_rho_cosets hs hx hxW q hq with h | h | h | h
    · exact hs.W_sq q h
    · have hq_eq : q = (q * x⁻¹) * x := by group
      rw [hq_eq]
      exact fzc_sy2_sq_coset hs hx hxW hxZ h
    · rw [← hx₁def] at h
      have hq_eq : q = (q * x₁⁻¹) * x₁ := by group
      rw [hq_eq]
      exact fzc_sy2_sq_coset hs hx₁Q hx₁W hx₁Z h
    · rw [← hx₁def, ← hx₂def] at h
      have hq_eq : q = (q * x₂⁻¹) * x₂ := by group
      rw [hq_eq]
      exact fzc_sy2_sq_coset hs hx₂Q hx₂W hx₂Z h
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z := by
    intro a ha b hb
    refine fzl_comm_mem_of_sq (N := Z) (hQsq a ha) (hQsq b hb)
      (hQsq (a * b) (Q.mul_mem ha hb)) ?_
    intro n hn
    have h' : b * n * b⁻¹ = n := hs.Q_Z b hb n hn
    have hbn : b⁻¹ * n * b = n := by
      calc b⁻¹ * n * b = b⁻¹ * (b * n * b⁻¹) * b := by rw [h']
        _ = n := by group
    rw [hbn]
    exact hn
  have hΦZ : fzlPhi Q ≤ Z := fzl_phi_le_of_elem hQcomm hQsq
  have htZ : t ∈ Z := by
    have htW : t ∈ W := hs.t_mem
    rw [← fzc_sy2_phi hs hP] at htW
    exact hΦZ htW
  exact hs.t_notin_E (hs.ZE htZ)

end CFSG.OddStandard.SmallF3.FritzII
