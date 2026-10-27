module

public import CFSG.ClassicalInvolution.Q3.TL4Thm6Defs
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallM11

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Thm6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.GH74.KGroups CFSG.GH74.KGroups.M11

section Cit3


theorem smallSimpleLeaf6_m11 :
    SmallSimpleLeaf6 TA3.SmallM11 := by
  intro Y _ _ _ _ hnab _ hP R S t hd hc _
  left
  have := genFittingFStar_normal Y
  obtain ⟨M, hMP, hMA⟩ := M11.autModel hP
  have hinj := TA3.realize_injective (genFittingFStar Y) (MulEquiv.refl _) M
    (Nobq.centralizer_genFittingFStar_eq_bot hnab)
  have hXQ : (TA3.realize (genFittingFStar Y) (MulEquiv.refl _) M).range = Q.originalSubgroup :=
    le_antisymm (hMA ▸ TA3.realize_range_le _ _ M)
      (hMP ▸ TA3.le_realize_range _ _ M (by rw [hMP, hMA]))
  obtain ⟨S', ⟨eS⟩, hS₀⟩ := TA3.exists_sylow_map_equiv (MonoidHom.ofInjective hinj) S
  obtain ⟨eQ⟩ := hc.1
  refine TA3.GoodThreeElement.of_map_equiv (MonoidHom.ofInjective hinj) ?_
  refine TA3.good_of_goodCheck
    (ι := (TA3.realize (genFittingFStar Y) (MulEquiv.refl _) M).range.subtype)
    Subtype.val_injective (fun m => ?_) TA3.m11_goodCheck
    (TA3.TightDatum.map_equiv (MonoidHom.ofInjective hinj) hd ⟨eS⟩ hS₀) ⟨eS.symm.trans eQ⟩
  rw [mem_elemsT Q Q_ok m, ← hXQ]
  exact ⟨fun hm => ⟨⟨m, hm⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Thm6
