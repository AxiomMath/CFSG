module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Goldschmidt.StrongClosure
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs

public section

open CFSG.Open CFSG.Goldschmidt Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

structure IsGoldSemisimple (Y : Type) [Group Y] : Prop where
  o2 : CFSG.Open.pCore 2 Y = ⊥
  odd : goldschmidtOddCore Y = ⊥
  layer : goldschmidtLayer Y = ⊤
  comps : ∀ K : Subgroup Y, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K)

end CFSG.OddStandard.SmallF3.Omega
