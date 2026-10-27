module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M0
public import CFSG.ClassicalInvolution.Q3.Q3CHS2Tri

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.P24

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Q3.Q3CH
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer (tqMembers exactCore)

structure TwinInnerHyp {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (b d c : G) (B : Subgroup G) : Prop where
  hK : K ∈ Ω
  hK' : K' ∈ Ω
  hne : K' ≠ K
  hb : IsUniqueInvolution K b
  hb' : IsUniqueInvolution K' b
  htq : K ∈ tqMembers Ω c
  htq' : K' ∈ tqMembers Ω c
  hB : IsElemAbelian 2 B
  hbB : b ∈ B
  hdB : d ∈ B
  hcB : c ∈ B
  hgen : B = Subgroup.closure ({b, d, c} : Set G)
  hc1 : c ≠ 1
  hbc : b ≠ c
  hd1 : d ≠ 1
  hdb : d ≠ b
  hd2 : d * d = 1
  hdK : d ∈ exactCore c K ⊔ exactCore c K'

end CFSG.ClassicalInvolution.Q8P.P24
