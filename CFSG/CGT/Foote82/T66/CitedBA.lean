module

public import CFSG.CGT.Foote82.Setup
public import CFSG.CGT.Foote82.T66.Perm310

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

@[expose] def G8 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G : Subgroup (GLV V))
    (φ : ↥G ≃* Equiv.Perm (Fin 9)), IsIrr G ⊤ →
      (∀ g : ↥G, φ g ∈ altOn {k : Fin 9 | k ≠ 0 ∧ k ≠ 1} →
        ∀ w ∈ commSpace (Subgroup.zpowers ((φ.symm (Equiv.swap 0 1) : ↥G) : GLV V)) ⊤,
          (g : GLV V) w = w) →
      HasIrrTildeV (((altOn {k : Fin 9 | k ≠ 0 ∧ k ≠ 1}).comap φ.toMonoidHom).map G.subtype) →
        Module.finrank (ZMod 2)
          (TildeV (((altOn {k : Fin 9 | k ≠ 0 ∧ k ≠ 1}).comap φ.toMonoidHom).map G.subtype)) ≠ 4

end CFSG.CGT.Foote82
