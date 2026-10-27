module

public import Certificates.Data.Kernel.Spor.Fi24Ctl3
public import CFSG.Certificates.Kernel.Spor.Fi24PumpKSound

public section

namespace CFSG.KS.Fi24Ctl3

open CFSG.KC.Fi24Ctl3 CFSG.KC.Fi24PumpK CFSG.KS.Fi24PumpK

theorem ctlOK_spec {E : List Nat → List Nat → Bool} {r g x y h : List Nat}
    (hc : ctlOK E r g x y h = true) :
    (∀ l ∈ r, l < 26) ∧ (∀ l ∈ g, l < 26) ∧ (∀ l ∈ x, l < 26) ∧ (∀ l ∈ y, l < 26) ∧
      (∀ l ∈ h, l < 26) ∧ E (r ++ r ++ r) [] = true ∧ E (r ++ g) (g ++ x) = true ∧
      E (x ++ [2]) ([2] ++ x) = true ∧ E (x ++ y) (y ++ x) = true ∧ E (x ++ h) (h ++ y) = true ∧
      (E (y ++ [0]) ([0] ++ y) = true ∨ E h [0] = true) := by
  unfold ctlOK at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, letLt_iff] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr, hg⟩, hx⟩, hy⟩, hh⟩, h3⟩, hrg⟩, hb⟩, hxy⟩, hxh⟩, ha⟩ := hc
  exact ⟨hr, hg, hx, hy, hh, h3, hrg, hb, hxy, hxh, ha⟩

end CFSG.KS.Fi24Ctl3

end
