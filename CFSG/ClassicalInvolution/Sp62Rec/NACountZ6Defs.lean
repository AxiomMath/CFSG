module

public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1NA

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open


@[expose] def conjA0 : ↥N0 →* MulAut ↥A0 :=
  (Subgroup.normalizerMonoidHom A0).comp (Subgroup.inclusion N0_le_normalizer)

theorem coe_conjA0_apply (n : ↥N0) (a : ↥A0) :
    ((conjA0 n a : ↥A0) : StatedSp 3 (ZMod 2)) =
      (n : StatedSp 3 (ZMod 2)) * (a : StatedSp 3 (ZMod 2)) * (n : StatedSp 3 (ZMod 2))⁻¹ :=
  rfl

@[expose] def Lbar : Subgroup (MulAut ↥A0) := conjA0.range

end CFSG.ClassicalInvolution.Sp62Rec
