module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.HSTypeS6
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku.A6

open CFSG.Quasithin.HSType

variable {A : Type} [CommGroup A]

structure IsPolarForm (ω : A → A → ZMod 2) : Prop where
  mul_left : ∀ x y w : A, ω (x * y) w = ω x w + ω y w
  mul_right : ∀ w x y : A, ω w (x * y) = ω w x + ω w y
  alt : ∀ x : A, ω x x = 0

theorem zmod2_eq_add_self_zero : ∀ a : ZMod 2, a = a + a → a = 0 := by decide

theorem IsPolarForm.one_left {ω : A → A → ZMod 2} (hω : IsPolarForm ω) (w : A) :
    ω 1 w = 0 := by
  have h := hω.mul_left 1 1 w
  rw [mul_one] at h
  exact zmod2_eq_add_self_zero _ h

theorem IsPolarForm.one_right {ω : A → A → ZMod 2} (hω : IsPolarForm ω) (w : A) :
    ω w 1 = 0 := by
  have h := hω.mul_right w 1 1
  rw [mul_one] at h
  exact zmod2_eq_add_self_zero _ h

end CFSG.GH74.QTGen4.Ku.A6

end
