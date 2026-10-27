module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

theorem two_pow_orderOf_two_le_index_fixV_mul_index_fixV {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (a b : MulAut V) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hab : orderOf (a * b) = p) :
    2 ^ orderOf (2 : ZMod p) ≤
      (fixV (Subgroup.zpowers a)).index * (fixV (Subgroup.zpowers b)).index :=
  have hW : ∀ w : V, w * w = 1 := fun w => (pow_two w).symm.trans (hV w)
  (two_pow_orderOf_le_index_fixV hW hp2 hab).trans (index_fixV_mul_le a b)

end CFSG.HardMathSupport.RichardWeiss.Proving
