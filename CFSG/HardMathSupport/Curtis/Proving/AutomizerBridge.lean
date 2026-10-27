module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open Subgroup

variable {G : Type*} [Group G]

noncomputable def automizerOn (H U : Subgroup G) (hU : U ≤ Subgroup.normalizer (H : Set G)) :
    U →* MulAut H :=
  (Subgroup.normalizerMonoidHom H).comp (Subgroup.inclusion hU)

theorem automizerOn_ker (H U : Subgroup G) (hU : U ≤ Subgroup.normalizer (H : Set G)) :
    (automizerOn H U hU).ker = (U ⊓ Subgroup.centralizer (H : Set G)).subgroupOf U := by
  ext u
  have hmem : Subgroup.inclusion hU u ∈ (Subgroup.normalizerMonoidHom H).ker ↔
      (u : G) ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    rfl
  have key : automizerOn H U hU u = 1 ↔ (u : G) ∈ Subgroup.centralizer (H : Set G) :=
    MonoidHom.mem_ker.symm.trans hmem
  rw [MonoidHom.mem_ker, key, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨u.2, h⟩, fun h => h.2⟩

theorem relIndex_centralizer_eq_card_automizer (H U : Subgroup G)
    (hU : U ≤ Subgroup.normalizer (H : Set G)) :
    (U ⊓ Subgroup.centralizer (H : Set G)).relIndex U =
      Nat.card (automizerOn H U hU).range := by
  rw [Subgroup.relIndex, ← automizerOn_ker H U hU, Subgroup.index_ker]

end CFSG.HardMathSupport.Curtis.Proving

end
