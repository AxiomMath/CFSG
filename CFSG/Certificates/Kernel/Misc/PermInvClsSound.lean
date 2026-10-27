module

public import Certificates.Data.Kernel.Misc.PermInvCls
public import CFSG.Certificates.Kernel.Misc.PermClosWSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.InvCls

open Equiv CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW

theorem repAt_sound {n w : ℕ} (hw : n + 1 < 2 ^ w) (hn : n < 16777216)
    (gs : List (Perm (Fin n))) {A : ℕ → ℕ} (hA : ∀ a < gs.length, A a = wcode w (gs.getD a 1))
    (d : Perm (Fin n)) {N : ℕ} {E R : ℕ → ℕ} {RW : ℕ → List ℕ} (el : ℕ → Perm (Fin n))
    (hE : ∀ k < N, E k = wcode w (el k)) {j : ℕ}
    (h : repAt n w A gs.length (wcode w d) N E R RW j = true) :
    R j < N ∧ ∃ c ∈ Subgroup.closure {g | g ∈ gs}, c * el (R j) = d * c := by
  have henc := wcode_enc hw hn
  unfold repAt at h
  obtain ⟨h1, h⟩ := CFSG.KC.LQT.P.andB_iff.1 h
  obtain ⟨h2, h3⟩ := CFSG.KC.LQT.P.andB_iff.1 h
  rw [CFSG.KC.LQT.P.blt_iff] at h1
  rw [CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.beq_iff] at h3
  obtain ⟨c, hc, hcw⟩ := wword_mem hw hn gs hA h2
  refine ⟨h1, c, hc, henc.inj ?_⟩
  rw [henc.enc_mul, henc.enc_mul, hcw, ← hE _ h1]
  exact h3

theorem clsAt_sound {n w : ℕ} (hw : n + 1 < 2 ^ w) (hn : n < 16777216) {N nR : ℕ}
    {E R CL : ℕ → ℕ} (el : ℕ → Perm (Fin n)) (hE : ∀ k < N, E k = wcode w (el k))
    (hR : ∀ j < nR, R j < N) {k : ℕ} (hk : k < N)
    (h : clsAt n w (pidn n w) N nR E R CL k = true) :
    el k = 1 ∨ el k * el k ≠ 1 ∨ ∃ j < nR, ∃ s < N, el s * el (R j) = el k * el s := by
  have hw' : n < 2 ^ w := by omega
  have henc := wcode_enc hw hn
  unfold clsAt at h
  simp only [CFSG.KC.LQT.P.letB_eq] at h
  rw [hE k hk] at h
  cases hv : Nat.beq (CL k) 0
  · rw [hv] at h
    have hv' : CL k ≠ 0 := Nat.ne_of_beq_eq_false hv
    cases hb : Nat.ble (CL k) n
    · rw [hb] at h
      dsimp only at h
      obtain ⟨h1, h⟩ := CFSG.KC.LQT.P.andB_iff.1 h
      obtain ⟨h2, h3⟩ := CFSG.KC.LQT.P.andB_iff.1 h
      rw [CFSG.KC.LQT.P.blt_iff] at h1 h2
      rw [CFSG.KC.LQT.P.beq_iff] at h3
      refine Or.inr (Or.inr ⟨_, h1, _, h2, henc.inj ?_⟩)
      rw [henc.enc_mul, henc.enc_mul, ← hE _ h2, ← hE _ (hR _ h1)]
      exact h3
    · rw [hb] at h
      dsimp only at h
      have hle : CL k ≤ n := Nat.le_of_ble_eq_true hb
      have hi : Nat.sub (CL k) 1 < n := by
        change CL k - 1 < n
        omega
      refine Or.inr (Or.inl fun he => ?_)
      rw [CFSG.KC.LQT.P.notB_iff, CFSG.KC.LQT.P.beq_iff] at h
      apply h
      rw [pg_wcode_nat hw' (el k) hi, pg_wcode hw' (el k)]
      have := congrArg (fun σ : Perm (Fin n) => ((σ ⟨_, hi⟩ : Fin n) : ℕ)) he
      simpa [Perm.mul_apply] using this
  · rw [hv] at h
    dsimp only at h
    rw [CFSG.KC.LQT.P.beq_iff, ← henc.enc_one] at h
    exact Or.inl (henc.inj h)

theorem invCls_sound {n w : ℕ} (hw : n + 1 < 2 ^ w) (hn : n < 16777216)
    (gs : List (Perm (Fin n))) {A : ℕ → ℕ} (hA : ∀ a < gs.length, A a = wcode w (gs.getD a 1))
    (d : Perm (Fin n)) {N nR : ℕ} {E R CL : ℕ → ℕ} {RW : ℕ → List ℕ} (el : ℕ → Perm (Fin n))
    (hE : ∀ k < N, E k = wcode w (el k))
    (hcls : ∀ k < N, clsAt n w (pidn n w) N nR E R CL k = true)
    (hrep : ∀ j < nR, repAt n w A gs.length (wcode w d) N E R RW j = true) :
    ∀ k < N, el k * el k = 1 → el k ≠ 1 →
      ∃ s < N, ∃ c ∈ Subgroup.closure {g | g ∈ gs},
        c * (el s)⁻¹ * el k = d * (c * (el s)⁻¹) := by
  intro k hk hsq hne
  have hR : ∀ j < nR, R j < N := fun j hj => (repAt_sound hw hn gs hA d el hE (hrep j hj)).1
  rcases clsAt_sound hw hn el hE hR hk (hcls k hk) with h1 | h1 | ⟨j, hj, s, hs, h1⟩
  · exact absurd h1 hne
  · exact absurd hsq h1
  · obtain ⟨-, c, hc, h2⟩ := repAt_sound hw hn gs hA d el hE (hrep j hj)
    refine ⟨s, hs, c, hc, ?_⟩
    have h3 : (el s)⁻¹ * el k = el (R j) * (el s)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← h1, inv_mul_cancel_left]
    rw [mul_assoc, h3, ← mul_assoc, h2, mul_assoc]

end CFSG.KC.Misc.InvCls

end
