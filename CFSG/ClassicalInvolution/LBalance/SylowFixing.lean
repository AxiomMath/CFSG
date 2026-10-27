module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalInvolution

@[expose] def sylowFixingAut {G : Type*} [Group G] (S : Subgroup G) : Subgroup (MulAut G) :=
  ⨅ s ∈ S, MulAction.stabilizer (MulAut G) s

@[simp] theorem mem_sylowFixingAut {G : Type*} [Group G] {S : Subgroup G} {φ : MulAut G} :
    φ ∈ sylowFixingAut S ↔ ∀ s ∈ S, φ s = s := by
  simp [sylowFixingAut, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

@[expose] def GlaubermanSylowFixingSolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.pPrimeCore 2 G = ⊥ →
    ∀ S : Sylow 2 G, Group.IsSolvable (sylowFixingAut (S : Subgroup G))

end CFSG.ClassicalInvolution
