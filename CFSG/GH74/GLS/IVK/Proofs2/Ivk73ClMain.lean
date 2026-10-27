module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClL5
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU5
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Leaf2

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.Blueprint

structure Ivk73ClassicalThree : Prop where
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .PSp 2 p f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk73Empty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk73Empty (fun X _ => LieModel X .PSU 4 p f)

theorem ivk73Classical_of_three
    (h : Ivk73ClassicalThree) : Ivk73Classical where
  sp4 := h.sp4
  l4 := h.l4
  u4 := h.u4
  l5 := fun p f hp hf hmod => ivk73_l5 p f hp hf hmod
  u5 := fun p f hp hf hmod => ivk73_u5 p f hp hf hmod

theorem ivk_7_3_g4_of_rest_three
    (hr : Ivk73Rest) (hc : Ivk73ClassicalThree) (ho : IVK73_L3U3) : IVK_7_3_g4 :=
  ivk_7_3_g4_of_rest_classical hr (ivk73Classical_of_three hc) ho

end CFSG.GH74.GLS.IVK
