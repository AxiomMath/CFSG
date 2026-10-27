module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClMain2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClSp4

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.Blueprint

structure Ivk73ClassicalOne : Prop where
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk73Empty (fun X _ => LieModel X .PSU 4 p f)

theorem ivk73ClassicalTwo_of_one
    (h : Ivk73ClassicalOne) : Ivk73ClassicalTwo where
  sp4 := fun p f hp hp2 hf => ivk73_sp4 p f hp hp2 hf
  u4 := h.u4

theorem ivk_7_3_g4_of_rest_one
    (hr : Ivk73Rest) (hc : Ivk73ClassicalOne) (ho : IVK73_L3U3) : IVK_7_3_g4 :=
  ivk_7_3_g4_of_rest_two hr (ivk73ClassicalTwo_of_one hc) ho

end CFSG.GH74.GLS.IVK
