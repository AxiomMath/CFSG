module

public import Certificates.Data.Kernel.LocalQT.Sec
import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CFSG.KC.LQT

open CFSG.KC.Ord
open CFSG.KS.SporSch.LyM (andB_true')

theorem sqOK_intro {c : Lay} {V : Nat → Nat} {N ix iy ih r oh a b cc dd t : Nat} {σ : List Nat}
    (h0 : andB (Nat.blt ix N) (andB (Nat.blt iy N) (andB (Nat.blt ih N)
      (andB (Nat.blt (nat_lit 0) r) (Nat.blt (nat_lit 0) oh)))) = true)
    (h1 : Nat.beq (c.pow (V ix) r) c.ONE = true) (h2 : Nat.beq (c.pow (V iy) r) c.ONE = true)
    (h3 : Nat.beq (c.pow (V ih) oh) c.ONE = true)
    (h4 : Nat.beq (c.mul (V ix) (V iy)) (c.mul (V iy) (V ix)) = true)
    (h5 : conjOK c (V ih) (V ix) (c.mul (c.pow (V ix) a) (c.pow (V iy) cc)) = true)
    (h6 : conjOK c (V ih) (V iy) (c.mul (c.pow (V ix) b) (c.pow (V iy) dd)) = true)
    (h7 : normalOK c r (sel3 (V ix) (V iy) (V iy)) (nat_lit 2) t σ = true) :
    sqOK c V N ix iy ih r oh a b cc dd t σ = true := by
  obtain ⟨g1, h0⟩ := andB_true' h0
  obtain ⟨g2, h0⟩ := andB_true' h0
  obtain ⟨g3, h0⟩ := andB_true' h0
  obtain ⟨g4, g5⟩ := andB_true' h0
  unfold sqOK
  rw [g1, g2, g3, g4, g5, h1, h2, h3, h4, h5, h6, h7]
  rfl

theorem pow_zero' (c : Lay) (X : Nat) : c.pow X 0 = c.ONE := rfl
theorem pow_one' (c : Lay) (X : Nat) : c.pow X 1 = c.mul c.ONE X := rfl
theorem pow_two' (c : Lay) (X : Nat) : c.pow X 2 = c.mul (c.pow X 1) X := rfl
theorem pow_three' (c : Lay) (X : Nat) : c.pow X 3 = c.mul (c.pow X 2) X := rfl
theorem pow_four' (c : Lay) (X : Nat) : c.pow X 4 = c.mul (c.pow X 3) X := rfl
theorem pow_five' (c : Lay) (X : Nat) : c.pow X 5 = c.mul (c.pow X 4) X := rfl

theorem conjOK_of {c : Lay} {H X W : Nat} (h : Nat.beq (c.mul H X) (c.mul W H) = true) :
    conjOK c H X W = true := h

end CFSG.KC.LQT

end
