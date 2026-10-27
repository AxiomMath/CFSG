module

public import CFSG.ClassicalInvolution.Q3.TL4OddDefs
public import CFSG.ClassicalInvolution.Q3.TL4E3Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3

theorem tightE3Leaf_of_R' {n : ℕ} (hα : TightAlphaLeafR 3 n) (h : TightE3LeafR' 3 n) :
    TightE3Leaf n :=
  fun Y _ _ R S t hL _ hcn hsp J hJ u hu htu ht Sb hex =>
    h Y R S t hL.toR hcn hsp (hα Y R S t hL.toR hcn) J hJ u hu htu ht Sb hex

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
