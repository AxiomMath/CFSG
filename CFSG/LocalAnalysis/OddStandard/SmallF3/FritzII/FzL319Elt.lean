module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319IdxEv

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzL26 CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

@[expose] def fzEIdx (x : FzElt) : ℕ :=
  fzIdx x.1 + 64 * (x.2.1.val + 2 * x.2.2.1.val + 4 * x.2.2.2.val)

@[expose] def fzEOf (n : ℕ) : FzElt :=
  (fzElt (n % 64), (((n / 64 % 2 : ℕ) : ZMod 2), ((n / 128 % 2 : ℕ) : ZMod 2),
    ((n / 256 % 2 : ℕ) : ZMod 2)))

private theorem fzEIdx_digits (x : FzElt) :
    fzEIdx x % 64 = fzIdx x.1 ∧
    fzEIdx x / 64 = x.2.1.val + 2 * x.2.2.1.val + 4 * x.2.2.2.val ∧
    fzEIdx x / 64 % 2 = x.2.1.val ∧
    fzEIdx x / 128 % 2 = x.2.2.1.val ∧
    fzEIdx x / 256 % 2 = x.2.2.2.val ∧
    fzEIdx x / 64 < 8 := by
  have h0 := fzIdx_lt x.1
  have h1 := ZMod.val_lt x.2.1
  have h2 := ZMod.val_lt x.2.2.1
  have h3 := ZMod.val_lt x.2.2.2
  unfold fzEIdx
  omega

theorem fzEIdx_lt (x : FzElt) : fzEIdx x < 512 := by
  have h0 := fzIdx_lt x.1
  have h1 := ZMod.val_lt x.2.1
  have h2 := ZMod.val_lt x.2.2.1
  have h3 := ZMod.val_lt x.2.2.2
  unfold fzEIdx
  omega

theorem fzEOf_fzEIdx (x : FzElt) : fzEOf (fzEIdx x) = x := by
  obtain ⟨h0, -, h2, h3, h4, -⟩ := fzEIdx_digits x
  unfold fzEOf
  rw [h0, h2, h3, h4]
  simp only [fzElt_fzIdx, ZMod.natCast_zmod_val]

theorem fzEIdx_fzEOf {n : ℕ} (h : n < 512) : fzEIdx (fzEOf n) = n := by
  have h0 : n % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have h1 : n / 64 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h2 : n / 128 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h3 : n / 256 % 2 < 2 := Nat.mod_lt _ (by norm_num)
  unfold fzEOf fzEIdx
  rw [fzIdx_fzElt h0, ZMod.val_cast_of_lt h1, ZMod.val_cast_of_lt h2,
    ZMod.val_cast_of_lt h3]
  omega

theorem fzEIdx_one : fzEIdx fzOneC = 0 := by
  simp [fzEIdx, fzOneC, fzIdx_one]

private theorem fzEIdx_xor (v w : FzV) :
    (v.1.val + 2 * v.2.1.val + 4 * v.2.2.val) ^^^
        (w.1.val + 2 * w.2.1.val + 4 * w.2.2.val) =
      (v + w).1.val + 2 * (v + w).2.1.val + 4 * (v + w).2.2.val := by
  revert v w
  decide +kernel

private theorem fzEIdx_mulC (t s l : MulAut FzUT) (x y : FzElt) :
    fzEIdx (fzMulC t s l x y) =
      fzIdx (x.1 * fzAct t s l x.2 y.1) +
        64 * ((x.2 + y.2).1.val + 2 * (x.2 + y.2).2.1.val +
          4 * (x.2 + y.2).2.2.val) := rfl

private theorem fzAutI_apb (σ : MulAut FzUT) (b : ZMod 2) (w : FzUT) :
    (fzAutI σ).apb b.val (fzIdx w) = fzIdx (fzAp b σ w) := by
  by_cases h : b = 0
  · simp [AutI.apb, fzAp, h, (ZMod.val_eq_zero b).mpr h]
  · have hv : b.val ≠ 0 := fun hv => h ((ZMod.val_eq_zero b).mp hv)
    simp [AutI.apb, fzAp, h, hv, fzAutI_ap]

private theorem fzEm_k (x y : FzElt) :
    64 * (fzEIdx x / 64) + fzEIdx y % 64 < 512 ∧
    (64 * (fzEIdx x / 64) + fzEIdx y % 64) % 64 = fzIdx y.1 ∧
    (64 * (fzEIdx x / 64) + fzEIdx y % 64) / 64 % 2 = x.2.1.val ∧
    (64 * (fzEIdx x / 64) + fzEIdx y % 64) / 128 % 2 = x.2.2.1.val ∧
    (64 * (fzEIdx x / 64) + fzEIdx y % 64) / 256 = x.2.2.2.val := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4, hx5⟩ := fzEIdx_digits x
  obtain ⟨hy0, hy1, hy2, hy3, hy4, hy5⟩ := fzEIdx_digits y
  have hv1 := ZMod.val_lt x.2.1
  have hv2 := ZMod.val_lt x.2.2.1
  have hv3 := ZMod.val_lt x.2.2.2
  have hylt : fzEIdx y % 64 < 64 := Nat.mod_lt _ (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem fzEm_act (t s l : MulAut FzUT) (x y : FzElt) :
    (actTab (fzAutI t) (fzAutI s) (fzAutI l))[64 * (fzEIdx x / 64) + fzEIdx y % 64]! =
      fzIdx (fzAct t s l x.2 y.1) := by
  obtain ⟨hklt, hk0, hk1, hk2, hk3⟩ := fzEm_k x y
  unfold actTab
  rw [tabulate_getElem! _ _ hklt, hk0, hk1, hk2, hk3]
  rw [fzAutI_apb l x.2.2.2 y.1]
  rw [fzAutI_apb s x.2.2.1 (fzAp x.2.2.2 l y.1)]
  rw [fzAutI_apb t x.2.1 (fzAp x.2.2.1 s (fzAp x.2.2.2 l y.1))]
  rfl

theorem fzEm (t s l : MulAut FzUT) (x y : FzElt) :
    (pctx ()).em (actTab (fzAutI t) (fzAutI s) (fzAutI l)) (fzEIdx x) (fzEIdx y) =
      fzEIdx (fzMulC t s l x y) := by
  obtain ⟨hx0, hx1, -, -, -, -⟩ := fzEIdx_digits x
  obtain ⟨-, hy1, -, -, -, -⟩ := fzEIdx_digits y
  unfold PCtx.em
  rw [hx0, fzEm_act t s l x y, fzIdx_m, hx1, hy1, fzEIdx_xor, fzEIdx_mulC]

theorem fzEIdx_W (t : MulAut FzUT) (x : FzElt) :
    (((fzAutI t).ap (fzEIdx x % 64) == fzEIdx x % 64) && decide (fzEIdx x / 64 < 2)) = true ↔
      fzInW t x := by
  obtain ⟨h0, h1, -, -, -, -⟩ := fzEIdx_digits x
  simp only [Bool.and_eq_true_iff, beq_iff_eq, decide_eq_true_iff, h0, fzAutI_ap,
    fzIdx_injective.eq_iff, h1, fzInW]
  constructor
  · rintro ⟨ha, hb⟩
    have hv0 := ZMod.val_lt x.2.1
    have hv1 := ZMod.val_lt x.2.2.1
    have hv2 := ZMod.val_lt x.2.2.2
    refine ⟨ha, ?_, ?_⟩
    · rw [← ZMod.val_eq_zero]; omega
    · rw [← ZMod.val_eq_zero]; omega
  · rintro ⟨ha, hb, hc⟩
    have hv0 := ZMod.val_lt x.2.1
    have hb' : x.2.2.1.val = 0 := (ZMod.val_eq_zero x.2.2.1).mpr hb
    have hc' : x.2.2.2.val = 0 := (ZMod.val_eq_zero x.2.2.2).mpr hc
    refine ⟨ha, ?_⟩
    rw [hb', hc']
    omega

end CFSG.OddStandard.SmallF3.FritzII
