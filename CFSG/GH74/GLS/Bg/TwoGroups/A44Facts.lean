module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Model

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace A44

namespace M4

@[expose] def IsA0 (x : M4) : Prop :=
  x.a.val % 2 = 1 ∧ x.b.val % 2 = 0 ∧ x.c.val % 2 = 0 ∧ x.d.val % 2 = 1

instance (x : M4) : Decidable x.IsA0 := by unfold IsA0; infer_instance

theorem isA0_iff : ∀ x : M4, (∀ w : ZMod 4 × ZMod 4, (x.act w - w) + (x.act w - w) = 0) ↔ x.IsA0 := by
  decide +kernel

@[expose] def sq (x : M4) : M4 := mul x x

@[expose] def pow32 (x : M4) : M4 := sq (sq (sq (sq (sq x))))

@[expose] def conj (h x : M4) : M4 := mul (mul h x) h.inv

theorem card_G96 : Fintype.card G96 = 96 := by decide +kernel

theorem card_A0 : Fintype.card {x : G96 // x.1.IsA0} = 16 := by decide +kernel

theorem A0_comm : ∀ x y : M4, x.IsA0 → y.IsA0 → mul x y = mul y x := by decide +kernel

theorem A0_sq : ∀ x : M4, x.IsA0 → mul x x = one := by decide +kernel

theorem A0_normal : ∀ g x : M4, g.IsInv → x.IsA0 → (conj g x).IsA0 := by decide +kernel

theorem not_two_group : ∀ x : M4, x.IsInv → ¬ x.IsA0 →
    ¬ pow32 x = one ∨ ∃ h : M4, h.IsInv ∧ ¬ pow32 (mul x (conj h x)) = one := by decide +kernel

end M4

end A44

end CFSG.GH74.GLS.Bg.TwoGroups
