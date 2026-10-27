module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClMain
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClL4

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.Blueprint

structure Ivk73ClassicalTwo : Prop where
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .PSp 2 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk73Empty (fun X _ => LieModel X .PSU 4 p f)

theorem ivk73ClassicalThree_of_two
    (h : Ivk73ClassicalTwo) : Ivk73ClassicalThree where
  sp4 := h.sp4
  l4 := fun p f hp hp2 hf hmod => ivk73_l4 p f hp hp2 hf hmod
  u4 := h.u4

theorem ivk_7_3_g4_of_rest_two
    (hr : Ivk73Rest) (hc : Ivk73ClassicalTwo) (ho : IVK73_L3U3) : IVK_7_3_g4 :=
  ivk_7_3_g4_of_rest_three hr (ivk73ClassicalThree_of_two hc) ho

end CFSG.GH74.GLS.IVK
