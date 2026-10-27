module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine

public section

noncomputable section

namespace CFSG.GorensteinWalter

universe u

@[expose] noncomputable def psl2UpperUnipotentEquiv
    (K : Type u) [Field K] :
    Multiplicative K ≃* psl2UpperUnipotentSubgroup K :=
  MulEquiv.ofBijective (psl2UpperUnipotentHom K).rangeRestrict
    ⟨fun x y h => psl2UpperUnipotentHom_injective
        (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

@[simp] theorem psl2UpperUnipotentEquiv_apply
    {K : Type u} [Field K] (x : Multiplicative K) :
    ((psl2UpperUnipotentEquiv K x : psl2UpperUnipotentSubgroup K) : PSL2 K) =
      psl2UpperUnipotentHom K x := rfl

end CFSG.GorensteinWalter
