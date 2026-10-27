module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAut74Auto

public section

namespace CFSG.GH74.PartII

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.HarrisU33.Outside

private lemma pow_four_F4c : ∀ x : F4c, x * x * (x * x) = x := by decide +kernel

theorem frobAut_mul_self : frobAut * frobAut = 1 :=
  MulEquiv.ext fun x => UT3.ext (pow_four_F4c x.a) (pow_four_F4c x.b) (pow_four_F4c x.c)

@[expose] def invAct (α : MulAut U4) (hα : α * α = 1) : Multiplicative (ZMod 2) →* MulAut U4 where
  toFun e := α ^ (Multiplicative.toAdd e).val
  map_one' := pow_zero α
  map_mul' a b := by
    have h2 : α ^ 2 = 1 := by rw [pow_two, hα]
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ h2, pow_add]

abbrev frobAct : Multiplicative (ZMod 2) →* MulAut U4 := invAct frobAut frobAut_mul_self

abbrev SylAhat8 : Type := U4 ⋊[frobAct] Multiplicative (ZMod 2)

instance (α : MulAut U4) (hα : α * α = 1) : Fintype (U4 ⋊[invAct α hα] Multiplicative (ZMod 2)) :=
  Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

end CFSG.GH74.PartII
