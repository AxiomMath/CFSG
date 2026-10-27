module

public import CFSG.CGT.Stroth77.Section224FrameModTwo
public import CFSG.CGT.Stroth77.Section225FrameFin

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Stroth224Frame

open Stroth225Frame

@[expose] def actUvOne (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  topUv * f

@[expose] def actTOne (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  topT * f

@[expose] def actRhoOne (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  topRho * f * (barRhoOne * barRhoOne)

theorem barRho_cube : barRhoOne * (barRhoOne * barRhoOne) = 1 := by decide

theorem eq_actUvOne_of_mul (f g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : g * 1 = topUv * f) :
    g = actUvOne f := by
  rw [actUvOne, ← h, mul_one]

theorem eq_actTOne_of_mul (f g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : g * 1 = topT * f) :
    g = actTOne f := by
  rw [actTOne, ← h, mul_one]

theorem eq_actRhoOne_of_mul (f g : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h : g * barRhoOne = topRho * f) :
    g = actRhoOne f := by
  rw [actRhoOne, ← h, mul_assoc, barRho_cube, mul_one]

theorem fixed_iff_row_zero (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (actUvOne f = f ∧ actTOne f = f) ↔ (f 0 0 = 0 ∧ f 0 1 = 0 ∧ f 0 2 = 0) := by
  have key : ∀ a b c d e g h i j : ZMod 2,
      (actUvOne !![a, b, c; d, e, g; h, i, j] = !![a, b, c; d, e, g; h, i, j] ∧
        actTOne !![a, b, c; d, e, g; h, i, j] = !![a, b, c; d, e, g; h, i, j]) ↔
      (a = 0 ∧ b = 0 ∧ c = 0) := by
    decide
  rw [Matrix.eta_fin_three f]
  exact key _ _ _ _ _ _ _ _ _

theorem row_zero_actRhoOne_actU (f : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hf : f 0 0 = 0 ∧ f 0 1 = 0 ∧ f 0 2 = 0) :
    ((actRhoOne f) 0 0 = 0 ∧ (actRhoOne f) 0 1 = 0 ∧ (actRhoOne f) 0 2 = 0) ∧
      ((actU f) 0 0 = 0 ∧ (actU f) 0 1 = 0 ∧ (actU f) 0 2 = 0) := by
  have key : ∀ d e g h i j : ZMod 2,
      ((actRhoOne !![0, 0, 0; d, e, g; h, i, j]) 0 0 = 0 ∧
        (actRhoOne !![0, 0, 0; d, e, g; h, i, j]) 0 1 = 0 ∧
        (actRhoOne !![0, 0, 0; d, e, g; h, i, j]) 0 2 = 0) ∧
      ((actU !![0, 0, 0; d, e, g; h, i, j]) 0 0 = 0 ∧
        (actU !![0, 0, 0; d, e, g; h, i, j]) 0 1 = 0 ∧
        (actU !![0, 0, 0; d, e, g; h, i, j]) 0 2 = 0) := by
    decide
  obtain ⟨h1, h2, h3⟩ := hf
  rw [Matrix.eta_fin_three f, h1, h2, h3]
  exact key _ _ _ _ _ _

abbrev Cond (F : Matrix (Fin 3) (Fin 3) (ZMod 2)) (Q : Fin 3 → ZMod 2) : Prop :=
  F *ᵥ Q = 0 ∧ (Q = 0 ↔ F = 0)

theorem struct_fin (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) (q : Fin 3 → ZMod 2)
    (hf : f 0 0 = 0 ∧ f 0 1 = 0 ∧ f 0 2 = 0) (h₀ : Cond f q)
    (h₁ : Cond (f + actRhoOne f) (q + barRhoOne *ᵥ q)) (h₂ : Cond (f + actU f) (q + barU *ᵥ q))
    (h₃ : Cond (f + actU (actRhoOne f)) (q + barU *ᵥ (barRhoOne *ᵥ q))) :
    (f 1 2 = 0 ∧ f 2 1 = 0 ∧ f 1 1 = f 2 2) ∧ q = ![f 1 1, f 1 0, f 2 0] := by
  have key : ∀ d e g h i j : ZMod 2, ∀ q : Fin 3 → ZMod 2,
      Cond !![0, 0, 0; d, e, g; h, i, j] q →
      Cond (!![0, 0, 0; d, e, g; h, i, j] + actRhoOne !![0, 0, 0; d, e, g; h, i, j])
        (q + barRhoOne *ᵥ q) →
      Cond (!![0, 0, 0; d, e, g; h, i, j] + actU !![0, 0, 0; d, e, g; h, i, j])
        (q + barU *ᵥ q) →
      Cond (!![0, 0, 0; d, e, g; h, i, j] + actU (actRhoOne !![0, 0, 0; d, e, g; h, i, j]))
        (q + barU *ᵥ (barRhoOne *ᵥ q)) →
      (g = 0 ∧ i = 0 ∧ e = j) ∧ q = ![e, d, h] := by
    set_option synthInstance.maxSize 2048 in decide
  obtain ⟨r1, r2, r3⟩ := hf
  rw [Matrix.eta_fin_three f, r1, r2, r3] at h₀ h₁ h₂ h₃
  exact key _ _ _ _ _ _ _ h₀ h₁ h₂ h₃

theorem row_zero_of_add_actUvOne (f : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hb : (f + actUvOne f) 1 2 = 0 ∧ (f + actUvOne f) 2 1 = 0 ∧
      (f + actUvOne f) 1 1 = (f + actUvOne f) 2 2)
    (hc : (f + actUvOne f) 1 0 = 0 ∧ (f + actUvOne f) 2 0 = 0) :
    f 0 0 = 0 ∧ f 0 1 = 0 ∧ f 0 2 = 0 := by
  have key : ∀ a b c d e g h i j : ZMod 2,
      ((!![a, b, c; d, e, g; h, i, j] + actUvOne !![a, b, c; d, e, g; h, i, j]) 1 2 = 0 ∧
        (!![a, b, c; d, e, g; h, i, j] + actUvOne !![a, b, c; d, e, g; h, i, j]) 2 1 = 0 ∧
        (!![a, b, c; d, e, g; h, i, j] + actUvOne !![a, b, c; d, e, g; h, i, j]) 1 1 =
          (!![a, b, c; d, e, g; h, i, j] + actUvOne !![a, b, c; d, e, g; h, i, j]) 2 2) →
      ((!![a, b, c; d, e, g; h, i, j] + actUvOne !![a, b, c; d, e, g; h, i, j]) 1 0 = 0 ∧
        (!![a, b, c; d, e, g; h, i, j] + actUvOne !![a, b, c; d, e, g; h, i, j]) 2 0 = 0) →
      a = 0 ∧ b = 0 ∧ c = 0 := by
    decide
  rw [Matrix.eta_fin_three f] at hb hc ⊢
  exact key _ _ _ _ _ _ _ _ _ hb hc

end Stroth224Frame

end CFSG.CGT.Stroth77
