module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.GF2n.SzExplicit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Open CFSG.RankThree.GF2n Matrix

@[expose] def SzFpfSimpleNatural : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) ↥(Sz a) V),
    (∃ g : ↥(Sz a), orderOf g = 5 ∧ ∀ v, ρ g v = v → v = 0) →
    Nontrivial V → (∀ W : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∃ θ : (Fin 4 → GaloisField 2 (2 * a + 1)) →+ V, Function.Bijective θ ∧
      ∀ (g : ↥(Sz a)) (v : Fin 4 → GaloisField 2 (2 * a + 1)),
        θ (((g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))) *ᵥ v) = ρ g (θ v)

end CFSG.CGT.PushingUpLit.SolKNA
