module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public section

namespace CFSG.BenderSuzuki.External

universe u

theorem normalizer_conjBy
    {G : Type u} [Group G] (H : Subgroup G) (g : G) :
    Subgroup.normalizer (H.conjBy g : Set G) =
      (Subgroup.normalizer (H : Set G)).conjBy g := by
  simpa [Subgroup.conjBy] using
    (Subgroup.map_normalizer_eq_of_bijective H
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).bijective).symm

end CFSG.BenderSuzuki.External
