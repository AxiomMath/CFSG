module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Walk

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

namespace ExtData

variable {M W N : Type*} [Group M] [CommGroup W] [Group N] {ρ : M →* MulAut W}

@[expose] def restrict (X : ExtData ρ N) (K : Subgroup M) (B : Subgroup N)
    (hB : ∀ n, n ∈ B ↔ X.π n ∈ K) : ExtData (ρ.comp K.subtype) ↥B where
  π := (X.π.comp B.subtype).codRestrict K fun b => (hB b).1 b.2
  eT b := X.eT b
  π_surjective := fun k => by
    obtain ⟨n, hn⟩ := X.π_surjective k
    exact ⟨⟨n, (hB n).2 (hn ▸ k.2)⟩, Subtype.ext hn⟩
  eT_mul := fun x y hx hy => X.eT_mul x y (congrArg Subtype.val hx) (congrArg Subtype.val hy)
  eT_conj := fun n x hx => X.eT_conj n x (congrArg Subtype.val hx)
  eT_inj := fun x y hx hy hxy =>
    Subtype.ext (X.eT_inj x y (congrArg Subtype.val hx) (congrArg Subtype.val hy) hxy)
  eT_surj := fun w => by
    obtain ⟨x, hx, hxw⟩ := X.eT_surj w
    exact ⟨⟨x, (hB x).2 (hx ▸ K.one_mem)⟩, Subtype.ext hx, hxw⟩

end ExtData

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
