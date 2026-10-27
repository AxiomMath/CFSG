module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
public import CFSG.RankThree.PartOne.KC.OrthogonalPlanePermutations

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

@[expose] noncomputable def normPureBlock (n : ℕ) (S : Finset (Fin n)) :
    Subgroup (normOmega E n) :=
  (supportedDerived (normHypForm E n)
    (S.sup (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K)))))).subgroupOf
    (normOmega E n)

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
