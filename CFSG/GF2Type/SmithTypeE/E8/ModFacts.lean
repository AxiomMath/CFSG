module

public import CFSG.GF2Type.SmithTypeE.E8.ModDefs

public section

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.SeitzReduction (highRoot)
open CFSG.SeitzReduction.EPilot (pinnedElt)


@[expose] def IsRootInvol (r : ↥(adjointGroup .E7 (ZMod 2))) : Prop :=
  IsConj (pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)) r

structure E8ModelFacts : Prop where
  wt_ne_zero : ∀ w ∈ weightVec, w ≠ 0
  exists_adj : ∀ w ∈ weightVec, ∃ w' ∈ weightVec, w' ∈ collSpace w ∧ w' ≠ w
  wt_ne_add : ∀ w ∈ weightVec, ∀ w' ∈ weightVec, w' ∉ collSpace w → w + w' ∉ weightVec
  tv_wt : ∀ r : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r → ∀ w ∈ weightVec,
    e7Rep56 (ZMod 2) r w ∈ weightVec ∧ e7Rep56 (ZMod 2) r w ∈ collSpace w
  pair_rel_sym : ∀ r r' : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r → IsRootInvol r' → r ≠ r' →
    r * r' = r' * r ∨ r * r' * r = r' * r * r' ∨ r * r' * r * r' = r' * r * r' * r
  int_rel_sym : ∀ r r' : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r → IsRootInvol r' → r ≠ r' →
    ∀ c c' : Fin e7Data.d →₀ ZMod 2, e7Rep56 (ZMod 2) r c - c = e7Rep56 (ZMod 2) r' c' - c' →
      e7Rep56 (ZMod 2) r c - c = 0 ∨
        (r * r' = r' * r ∧ e7Rep56 (ZMod 2) r c - c ∈ weightVec)

end CFSG.GF2Type.SmithTypeE.E8
