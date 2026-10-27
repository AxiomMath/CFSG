module

public import CFSG.ClassicalGroups.Symplectic.Perfect
public import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic

theorem symplectic_small_field_perfect (n : ℕ) (K : Type) [Field K]
    (h : (Nat.card K = 3 ∧ 2 ≤ n) ∨ (Nat.card K = 2 ∧ 3 ≤ n)) :
    Group.IsPerfect (StatedSp n K) := by
  have : Group.IsPerfect (TauCeti.GLSymplecticFin n K) := isPerfect_GLSymplecticFin K n (Or.inr h)
  let e : TauCeti.GLSymplecticFin n K ≃* StatedSp n K :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K).trans
      (MulEquiv.subgroupCongr (statedSp_eq_GLSymplectic (n := n) (K := K)).symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

end CFSG.LocalAnalysis.ComponentInitial
