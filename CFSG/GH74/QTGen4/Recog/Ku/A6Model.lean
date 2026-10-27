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

@[expose] def zp (b : A) (a : ZMod 2) : A := if a = 1 then b else 1

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem zp_add {b : A} (hb : b * b = 1) (a a' : ZMod 2) :
    zp b (a + a') = zp b a * zp b a' := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases a' with rfl | rfl
  · simp [zp, h01]
  · simp [zp]
  · simp [zp]
  · rw [h11]
    simp [zp, h01, hb]

@[expose] def coordMap (b : Fin 4 → A) (v : SpV) : A :=
  zp (b 0) (v 0) * zp (b 1) (v 1) * zp (b 2) (v 2) * zp (b 3) (v 3)

theorem coordMap_add {b : Fin 4 → A} (hb : ∀ k, b k * b k = 1) (v w : SpV) :
    coordMap b (v + w) = coordMap b v * coordMap b w := by
  simp only [coordMap, Pi.add_apply]
  rw [zp_add (hb 0), zp_add (hb 1), zp_add (hb 2), zp_add (hb 3)]
  ac_rfl

theorem coordMap_spE (b : Fin 4 → A) (k : Fin 4) : coordMap b (spE k) = b k := by
  fin_cases k <;> simp [coordMap, spE, zp]

theorem add_self_sp (u : SpV) : u + u = 0 := by
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  funext i
  exact key (u i)

end CFSG.GH74.QTGen4.Ku.A6

end
