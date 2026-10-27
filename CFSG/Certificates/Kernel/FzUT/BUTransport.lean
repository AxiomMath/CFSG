module

public import CFSG.Certificates.Kernel.FzUT.BUAut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2Spec

public section

namespace CFSG.KC.FzUT

open CFSG.OddStandard.SmallF3.FritzII CFSG.GH74.GLS.Bg.TwoGroups

theorem conj_apply (h a : MulAut FzUT) (x : FzUT) : (h * a * h⁻¹) x = h (a (h⁻¹ x)) := rfl

theorem inv_apply_self (h : MulAut FzUT) (y : FzUT) : h⁻¹ (h y) = y := h.symm_apply_apply y

theorem inZ_iff : ∀ x : FzUT, FzInZ x ↔ ∀ y : FzUT, x * y = y * x := by
  unfold FzInZ
  decide +kernel

theorem inZ_map (h : MulAut FzUT) {x : FzUT} (hx : FzInZ x) : FzInZ (h x) := by
  rw [inZ_iff] at hx ⊢
  intro y
  obtain ⟨y', rfl⟩ := h.surjective y
  rw [← map_mul, ← map_mul, hx]

theorem conj_pow_apply (h a : MulAut FzUT) (k : ℕ) (x : FzUT) :
    ((h * a * h⁻¹) ^ k) x = h ((a ^ k) (h⁻¹ x)) := by
  rw [conj_pow]
  rfl

theorem fzbAdm_conj {r aq as ay : MulAut FzUT} (A : FzbAdm r aq as ay) (h : MulAut FzUT) :
    FzbAdm (h * r * h⁻¹) (h * aq * h⁻¹) (h * as * h⁻¹) (h * ay * h⁻¹) := by
  have sur : ∀ x, ∃ y, x = h y := fun x => (h.surjective x).imp fun _ e => e.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self, A.r3]
  · intro x hx
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self]
    intro e
    apply A.r_fpf y (fun hy => hx (by rw [hy, map_one])) (h.injective e)
  · intro x
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self, A.q_r]
  · intro x
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self, A.q4]
  · rw [← A.q_fix]
    symm
    apply Finset.card_equiv h.toEquiv
    intro y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, conj_apply, inv_apply_self]
    exact ⟨fun e => by rw [e], fun e => h.injective e⟩
  · intro x
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self, A.s_r]
  · obtain ⟨k, hk⟩ := A.s_sq
    refine ⟨k, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, conj_pow_apply, inv_apply_self, hk]
  · rcases A.s_q with hq | hq
    · left
      intro x
      obtain ⟨y, rfl⟩ := sur x
      simp only [conj_apply, inv_apply_self, hq]
    · right
      intro x
      obtain ⟨y, rfl⟩ := sur x
      simp only [conj_apply, inv_apply_self, hq]
  · intro x hx
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self] at hx ⊢
    rw [← map_mul, A.s_inv y (h.injective hx), map_one]
  · intro x
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self]
    rw [← map_inv, ← map_mul]
    exact inZ_map h (A.s_Z y)
  · intro x
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self, A.y_sq]
  · intro x
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self, A.y_r]
  · intro x
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self, A.y_q]
  · intro x
    obtain ⟨y, rfl⟩ := sur x
    simp only [conj_apply, inv_apply_self, A.y_s]

theorem e1_ne : fzE1 ≠ 1 := by decide +kernel

theorem f1_ne : fzF1 ≠ 1 := by decide +kernel

theorem e1_sq : fzE1 * fzE1 = 1 := by decide +kernel

theorem f1_sq : fzF1 * fzF1 = 1 := by decide +kernel

theorem isInvP_of (σ : MulAut FzUT) {g : FzUT} (hg : g ≠ 1) (hsq : g * g = 1) :
    isInvP (enc (σ g)) = true := by
  simp only [isInvP, andB_true, Nat.blt_eq, Nat.beq_eq]
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (enc (σ g)) with h0 | h0
    · exfalso
      apply hg
      apply σ.injective
      apply enc_injective
      rw [h0, map_one, enc_one]
    · exact h0
  · rw [pmulP_eq, ← map_mul, hsq, map_one, enc_one]

theorem card_eq_cntB (f : FzUT → FzUT) (F : ℕ → ℕ) (hF : ∀ x, enc (f x) = F (enc x)) :
    (Finset.univ.filter fun x : FzUT => f x = x).card = cntB 64 (fun n => Nat.beq (F n) n) := by
  rw [cntB_eq]
  apply Finset.card_bij (fun x _ => enc x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Finset.mem_range, Nat.beq_eq]
    exact ⟨enc_lt x, by rw [← hF, hx]⟩
  · intro x _ y _ e
    exact enc_injective e
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Nat.beq_eq] at hn
    refine ⟨dec n, ?_, enc_dec_lt hn.1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply enc_injective
    rw [hF, enc_dec_lt hn.1, hn.2]

end CFSG.KC.FzUT
