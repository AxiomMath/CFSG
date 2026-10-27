module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisAlg

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {p : ℕ} [NeZero p] {f : ZMod p → Module.End K V} {t ti : Module.End K V} {c₀ : K}

theorem sum_range_single {M : Type*} [AddCommMonoid M] (g : ℕ → M) (e : ZMod p)
    (h : ∀ k < p, (k : ZMod p) ≠ e → g k = 0) : ∑ k ∈ Finset.range p, g k = g e.val := by
  refine Finset.sum_eq_single_of_mem e.val (Finset.mem_range.2 (ZMod.val_lt e)) ?_
  intro k hk hne
  refine h k (Finset.mem_range.1 hk) fun hcast => hne ?_
  have := congrArg ZMod.val hcast
  rwa [ZMod.val_cast_of_lt (Finset.mem_range.1 hk)] at this

namespace HeisData

variable (H : HeisData p f t ti c₀)

include H

theorem f_apply_self_of_mem {m : ZMod p} {w : V} (hw : f m w = w) (m' : ZMod p) (hm : m' ≠ m) :
    f m' w = 0 := by
  have := H.orth m' m hm
  rw [← hw]
  have h2 := congrArg (fun g : Module.End K V => g w) this
  simpa [Module.End.mul_apply, hw] using h2

theorem f_idem_apply (m : ZMod p) (w : V) : f m (f m w) = f m w := by
  have := congrArg (fun g : Module.End K V => g w) (H.idem m)
  simpa [Module.End.mul_apply] using this

theorem dual_apply_of_ne {ξ : Module.Dual K V} {c : ZMod p} (hξ : ∀ v, ξ (f c v) = ξ v)
    {m : ZMod p} (hm : m ≠ c) (w : V) : ξ (f m w) = 0 := by
  rw [← hξ (f m w), f_apply_self_of_mem H (f_idem_apply H m w) c hm.symm, map_zero]

theorem tpow_apply_block (k : ℕ) {m : ZMod p} {y : V} (hy : f m y = y) :
    f (m + k) ((t ^ k) y) = (t ^ k) y := by
  have := congrArg (fun g : Module.End K V => g y) (H.tpow_f k m)
  simp only [Module.End.mul_apply, hy] at this
  exact this.symm

theorem tipow_apply_block (k : ℕ) {m : ZMod p} {y : V} (hy : f m y = y) :
    f (m - k) ((ti ^ k) y) = (ti ^ k) y := by
  have := congrArg (fun g : Module.End K V => g y) (H.tipow_f k m)
  simp only [Module.End.mul_apply, hy] at this
  exact this.symm

theorem ti_pow_t_pow_apply (k : ℕ) (y : V) : (ti ^ k) ((t ^ k) y) = y := by
  have := congrArg (fun g : Module.End K V => g y) (H.ti_pow_t_pow k)
  simpa [Module.End.mul_apply] using this

theorem tpow_ne_zero (k : ℕ) {y : V} (hy : y ≠ 0) : (t ^ k) y ≠ 0 := by
  intro h
  apply hy
  rw [← ti_pow_t_pow_apply H k y, h, map_zero]

theorem dual_ti_t_eq_zero {y : V} (hy : f 0 y = y) {ξ : Module.Dual K V}
    {c : ZMod p} (hξ : ∀ v, ξ (f c v) = ξ v) (hξz : ξ ((t ^ c.val) y) = 0) {k l : ℕ} (hk : k < p)
    (hl : l < p) [Nontrivial V] : ξ ((ti ^ k) ((t ^ l) y)) = 0 := by
  have h1 := tpow_apply_block H l hy
  have h2 := tipow_apply_block H k h1
  rw [zero_add] at h2
  by_cases hc : ((l : ZMod p) - k) = c
  · rcases le_or_gt k l with hkl | hkl
    · have hc' : ((l - k : ℕ) : ZMod p) = c := by rw [Nat.cast_sub hkl]; exact hc
      have hval : l - k = c.val := by
        rw [← hc', ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      have : (ti ^ k) ((t ^ l) y) = (t ^ c.val) y := by
        have := congrArg (fun g : Module.End K V => g y) (H.ti_pow_mul_t_pow_le hkl)
        simpa [Module.End.mul_apply, hval] using this
      rw [this]; exact hξz
    · have hc' : ((k - l : ℕ) : ZMod p) = -c := by
        rw [Nat.cast_sub hkl.le, ← neg_sub, hc]
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, neg_zero] at hc'
        have h3 := (ZMod.natCast_eq_zero_iff _ _).1 hc'
        have := Nat.le_of_dvd (by omega) h3
        omega
      haveI : NeZero c := ⟨hc0⟩
      have hval : k - l = p - c.val := by
        rw [← ZMod.val_neg_of_ne_zero c, ← hc', ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      have hcv : c.val ≤ p := (ZMod.val_lt c).le
      have h3 : ti ^ (k - l) = ti ^ p * t ^ c.val := by
        calc ti ^ (k - l) = ti ^ (k - l) * (ti ^ c.val * t ^ c.val) := by
              rw [H.ti_pow_t_pow, mul_one]
          _ = ti ^ (k - l + c.val) * t ^ c.val := by rw [← mul_assoc, ← pow_add]
          _ = ti ^ p * t ^ c.val := by rw [show k - l + c.val = p by omega]
      have : (ti ^ k) ((t ^ l) y) = c₀⁻¹ • (t ^ c.val) y := by
        have h4 := congrArg (fun g : Module.End K V => g y) (H.ti_pow_mul_t_pow_ge hkl.le)
        have h5 := congrArg (fun g : Module.End K V => g y) h3
        simp only [Module.End.mul_apply] at h4 h5
        rw [h4, h5]
        rw [H.ti_pow_p]
        simp
      rw [this, map_smul, hξz, smul_zero]
  · calc ξ ((ti ^ k) ((t ^ l) y)) = ξ (f ((l : ZMod p) - k) ((ti ^ k) ((t ^ l) y))) := by rw [h2]
      _ = 0 := dual_apply_of_ne H hξ hc _

end HeisData

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
