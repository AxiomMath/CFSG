module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Walk

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

namespace ExtData

variable {M W N : Type*} [Group M] [CommGroup W] [Group N] {ρ : M →* MulAut W}
  (X : ExtData ρ N)

theorem ker_comm {x y : N} (hx : X.π x = 1) (hy : X.π y = 1) : x * y = y * x :=
  X.eT_inj _ _ (X.π_eq_one_mul hx hy) (X.π_eq_one_mul hy hx)
    (by rw [X.eT_mul x y hx hy, X.eT_mul y x hy hx, mul_comm])

@[expose] def kerHom : ↥X.π.ker →* W where
  toFun := fun x => X.eT x
  map_one' := X.eT_one
  map_mul' := fun x y => X.eT_mul x y x.2 y.2

@[expose] noncomputable def kerEquiv : ↥X.π.ker ≃* W :=
  MulEquiv.ofBijective X.kerHom
    ⟨fun x y hxy => Subtype.ext (X.eT_inj x y x.2 y.2 hxy), fun w => by
      obtain ⟨x, hx, hxw⟩ := X.eT_surj w
      exact ⟨⟨x, hx⟩, hxw⟩⟩

theorem kerEquiv_apply (x : ↥X.π.ker) : X.kerEquiv x = X.eT x := rfl

theorem kerEquiv_conj (b : N) (x : ↥X.π.ker) :
    X.kerEquiv (MulAut.conjNormal b x) = ρ (X.π b) (X.kerEquiv x) :=
  X.eT_conj b x x.2

end ExtData

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
