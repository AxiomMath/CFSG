module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def PlaneIdxA : TauCeti.LieTypeIndex → Prop
  | .A _ _ => True
  | _ => False

@[expose] def PlaneIdxTwA : TauCeti.LieTypeIndex → Prop
  | .twistedA _ _ => True
  | _ => False

@[expose] def S267SpIdx : TauCeti.LieTypeIndex → Prop
  | .C _ _ => True
  | .B 2 _ => True
  | _ => False

@[expose] def S267OrthIdx : TauCeti.LieTypeIndex → Prop
  | .B r _ => 3 ≤ r
  | .D _ _ => True
  | .twistedD _ _ => True
  | _ => False

theorem genPlaneCompOn_classical_of_families (hA : GenPlaneCompOn PlaneIdxA)
    (h2A : GenPlaneCompOn PlaneIdxTwA) (hSp : GenPlaneCompOn S267SpIdx)
    (hOrth : GenPlaneCompOn S267OrthIdx) : GenPlaneCompOn S267ClassicalIdx := by
  intro p T _ _ d hd hcl
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact hA p T ⟨_, hv⟩ hd trivial
  | twistedA r q => exact h2A p T ⟨_, hv⟩ hd trivial
  | B r q =>
    have hr : 2 ≤ r :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp
        hv).1).1
    rcases Nat.lt_or_ge r 3 with h3 | h3
    · obtain rfl : r = 2 := by omega
      exact hSp p T ⟨_, hv⟩ hd trivial
    · exact hOrth p T ⟨_, hv⟩ hd h3
  | C r q => exact hSp p T ⟨_, hv⟩ hd trivial
  | D r q => exact hOrth p T ⟨_, hv⟩ hd trivial
  | twistedD r q => exact hOrth p T ⟨_, hv⟩ hd trivial
  | _ => exact absurd hcl (by simp [S267ClassicalIdx])

@[expose] def D4OuterCompNormal : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (d : TauCeti.ValidLieTypeIndex), OddLie 3 T d →
    (∃ q : TauCeti.PrimePower, d.1 = .D 4 q) → ∀ β : MulAut T, β ^ 3 = 1 →
      (∀ a : T, MulAut.conj a ≠ β) → CompNormal β

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
