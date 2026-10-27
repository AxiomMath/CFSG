module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Spec
public import Certificates.Data.FzL26

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzL26 CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

@[expose] def fzIdx (x : FzUT) : ℕ :=
  (x.a.a.val + 2 * x.a.b.val) + 4 * (x.b.a.val + 2 * x.b.b.val) +
    16 * (x.c.a.val + 2 * x.c.b.val)

@[expose] def fzElt (n : ℕ) : FzUT :=
  ⟨⟨((n % 2 : ℕ) : ZMod 2), ((n / 2 % 2 : ℕ) : ZMod 2)⟩,
    ⟨((n / 4 % 2 : ℕ) : ZMod 2), ((n / 8 % 2 : ℕ) : ZMod 2)⟩,
    ⟨((n / 16 % 2 : ℕ) : ZMod 2), ((n / 32 % 2 : ℕ) : ZMod 2)⟩⟩

theorem fzIdx_lt (x : FzUT) : fzIdx x < 64 := by
  revert x
  decide +kernel

theorem fzElt_fzIdx (x : FzUT) : fzElt (fzIdx x) = x := by
  revert x
  decide +kernel

theorem fzIdx_fzElt {n : ℕ} (h : n < 64) : fzIdx (fzElt n) = n := by
  have key : ∀ n < 64, fzIdx (fzElt n) = n := by decide +kernel
  exact key n h

theorem fzIdx_injective : Function.Injective fzIdx := fun x y h => by
  rw [← fzElt_fzIdx x, ← fzElt_fzIdx y, h]

theorem fzIdx_mul (x y : FzUT) : fzIdx (x * y) = pmul (fzIdx x) (fzIdx y) := by
  revert x y
  decide +kernel

theorem fzIdx_inv (x : FzUT) : fzIdx x⁻¹ = pinv (fzIdx x) := by
  revert x
  decide +kernel

theorem fzIdx_one : fzIdx (1 : FzUT) = 0 := by
  decide +kernel

theorem fzIdx_rho0 (x : FzUT) : rho0 (fzIdx x) = fzIdx (fzRho0 x) := by
  revert x
  decide +kernel

theorem tabulate_getElem! {α : Type} [Inhabited α] (k : ℕ) (f : ℕ → α) {n : ℕ} (h : n < k) :
    (tabulate k f)[n]! = f n := by
  simp [tabulate, getElem!_pos, h]

theorem pctx_m {i j : ℕ} (hi : i < 64) (hj : j < 64) : (pctx ()).m i j = pmul i j := by
  unfold PCtx.m pctx
  rw [tabulate_getElem! _ _ (by omega)]
  have h1 : (64 * i + j) / 64 = i := by omega
  have h2 : (64 * i + j) % 64 = j := by omega
  rw [h1, h2]

theorem pctx_v {i : ℕ} (hi : i < 64) : (pctx ()).v i = pinv i := by
  unfold PCtx.v pctx
  rw [tabulate_getElem! _ _ hi]

theorem fzIdx_m (x y : FzUT) : (pctx ()).m (fzIdx x) (fzIdx y) = fzIdx (x * y) := by
  rw [pctx_m (fzIdx_lt x) (fzIdx_lt y), fzIdx_mul]

theorem fzIdx_v (x : FzUT) : (pctx ()).v (fzIdx x) = fzIdx x⁻¹ := by
  rw [pctx_v (fzIdx_lt x), fzIdx_inv]

theorem fzIdx_c (x y : FzUT) : (pctx ()).c (fzIdx x) (fzIdx y) = fzIdx ⁅x, y⁆ := by
  simp only [PCtx.c, fzIdx_m, fzIdx_v, commutatorElement_def, mul_assoc]

theorem fzIdx_bits (x : FzUT) :
    fzIdx x % 2 = x.a.a.val ∧ fzIdx x / 2 % 2 = x.a.b.val ∧ fzIdx x / 4 % 2 = x.b.a.val ∧
      fzIdx x / 8 % 2 = x.b.b.val ∧
      ((fzIdx x / 16) ^^^ f4mul (fzIdx x % 4) (fzIdx x / 4 % 4)) % 2 = (x.c + x.a * x.b).a.val ∧
      ((fzIdx x / 16) ^^^ f4mul (fzIdx x % 4) (fzIdx x / 4 % 4)) / 2 = (x.c + x.a * x.b).b.val := by
  revert x
  decide +kernel

theorem fzIdx_bit (b : ZMod 2) (g : FzUT) : bit b.val (fzIdx g) = fzIdx (fzPw b g) := by
  unfold bit fzPw
  by_cases hb : b = 0
  · simp [hb, fzIdx_one]
  · have : b.val ≠ 0 := fun h => hb ((ZMod.val_eq_zero b).mp h)
    simp [hb, this]

end CFSG.OddStandard.SmallF3.FritzII
