module

public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.OddStandard.SmallF3.FritzII

abbrev FzXW : Type := ZMod 2 × ZMod 4 × ZMod 4

@[expose] def fzXMap (it i1 i2 w : FzXW) : FzXW :=
  w.1.val • it + w.2.1.val • i1 + w.2.2.val • i2

@[expose] def fzXN4 (it i1 i2 m : FzXW) : FzXW :=
  m + fzXMap it i1 i2 m + fzXMap it i1 i2 (fzXMap it i1 i2 m) +
    fzXMap it i1 i2 (fzXMap it i1 i2 (fzXMap it i1 i2 m))

@[expose] def fzXZ (v : FzXW) : Prop :=
  v.1 = 0 ∧ (v.2.1 = 0 ∨ v.2.1 = 2) ∧ (v.2.2 = 0 ∨ v.2.2 = 2)

@[expose] def fzXZel (i : Fin 4) : FzXW := (0, (2 * (i.val % 2) : ℕ), (2 * (i.val / 2) : ℕ))

instance (v : FzXW) : Decidable (fzXZ v) := by
  unfold fzXZ; infer_instance

theorem fzXZ_exists {v : FzXW} (h : fzXZ v) : ∃ i : Fin 4, v = fzXZel i := by
  have key : ∀ v : FzXW, fzXZ v → ∃ i : Fin 4, v = fzXZel i := by decide +kernel
  exact key v h

@[expose] def fzXP (i j k : Fin 4) (a : FzXW) : Prop :=
  a.1 = 1 →
    fzXMap ((1, 0, 0) + fzXZel i) ((0, 0, 1) + fzXZel j) ((0, 1, 0) + fzXZel k) a = a →
    ∀ m : FzXW,
      fzXN4 ((1, 0, 0) + fzXZel i) ((0, 0, 1) + fzXZel j) ((0, 1, 0) + fzXZel k) m =
        (2 : ℕ) • a →
      fzXMap ((1, 0, 0) + fzXZel i) ((0, 0, 1) + fzXZel j) ((0, 1, 0) + fzXZel k)
        (fzXMap ((1, 0, 0) + fzXZel i) ((0, 0, 1) + fzXZel j) ((0, 1, 0) + fzXZel k)
          (1, 0, 0)) = (1, 0, 0)

instance (i j k : Fin 4) (a : FzXW) : Decidable (fzXP i j k a) := by
  unfold fzXP; infer_instance

theorem fzx_check_aux : ∀ i j k : Fin 4, ∀ a : FzXW, fzXP i j k a := by
  decide +kernel

theorem fzx_check {zt z1 z2 a m : FzXW} (hzt : fzXZ zt) (hz1 : fzXZ z1) (hz2 : fzXZ z2)
    (ha : a.1 = 1)
    (hfix : fzXMap ((1, 0, 0) + zt) ((0, 0, 1) + z1) ((0, 1, 0) + z2) a = a)
    (hN : fzXN4 ((1, 0, 0) + zt) ((0, 0, 1) + z1) ((0, 1, 0) + z2) m = (2 : ℕ) • a) :
    fzXMap ((1, 0, 0) + zt) ((0, 0, 1) + z1) ((0, 1, 0) + z2)
      (fzXMap ((1, 0, 0) + zt) ((0, 0, 1) + z1) ((0, 1, 0) + z2) (1, 0, 0)) = (1, 0, 0) := by
  obtain ⟨i, rfl⟩ := fzXZ_exists hzt
  obtain ⟨j, rfl⟩ := fzXZ_exists hz1
  obtain ⟨k, rfl⟩ := fzXZ_exists hz2
  exact fzx_check_aux i j k a ha hfix m hN

end CFSG.OddStandard.SmallF3.FritzII
