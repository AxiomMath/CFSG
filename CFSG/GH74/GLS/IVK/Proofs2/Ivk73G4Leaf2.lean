module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Leaf

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint

structure Ivk73Classical : Prop where
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk73Empty (fun X _ => LieModel X .PSp 2 p f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk73Empty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk73Empty (fun X _ => LieModel X .PSU 4 p f)
  l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 → Ivk73Empty (fun X _ => LieModel X .PSL 5 p f)
  u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 → Ivk73Empty (fun X _ => LieModel X .PSU 5 p f)

@[expose] def IVK73_L3U3 : Prop :=
  Ivk73Empty fun X _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ (LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f)

theorem ivk73Leaves_of_rest_classical (hr : Ivk73Rest) (hc : Ivk73Classical) (ho : IVK73_L3U3) :
    Ivk73Leaves where
  alt := hr.alt
  m11 := hr.m11
  m12 := hr.m12
  m22 := hr.m22
  m23 := hr.m23
  j1 := hr.j1
  j2 := hr.j2
  j3 := hr.j3
  mcl := hr.mcl
  ly := hr.ly
  l2 := hr.l2
  l3 := fun p f hp hp2 hf N _ _ L K Q h hm => ho N L K Q h ⟨p, f, hp, hp2, hf, Or.inl hm⟩
  u3 := fun p f hp hp2 hf N _ _ L K Q h hm => ho N L K Q h ⟨p, f, hp, hp2, hf, Or.inr hm⟩
  sp4 := hc.sp4
  g2 := hr.g2
  d4 := hr.d4
  l4 := hc.l4
  u4 := hc.u4
  l5 := hc.l5
  u5 := hc.u5
  ree := hr.ree
  l28 := hr.l28
  l216 := hr.l216
  l34 := hr.l34
  u34 := hr.u34
  sz8 := hr.sz8

theorem ivk_7_3_g4_of_rest_classical (hr : Ivk73Rest) (hc : Ivk73Classical) (ho : IVK73_L3U3) :
    IVK_7_3_g4 :=
  ivk_7_3_g4_of_leaves (ivk73Leaves_of_rest_classical hr hc ho)

end CFSG.GH74.GLS.IVK
