module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Step83Pair

open Subgroup CFSG.ComponentClassification.AS76b

variable {G : Type*} [Group G]

@[expose] def OddCommute (x y : G) : Prop :=
  ∀ c : G, c * x = x * c → Odd (orderOf c) → c * y = y * c

theorem oddCommute_of_oUpperTwo_le {x y : G}
    (h : oUpperTwo (centralizer ({x} : Set G)) ≤ centralizer ({y} : Set G)) : OddCommute x y :=
  fun _ hc hodd => mem_centralizer_singleton_iff.1
    (h (subset_closure ⟨mem_centralizer_singleton_iff.2 hc, hodd⟩))

theorem oddCommute_map {H : Type*} [Group H] (e : G ≃* H) {x y : G} (h : OddCommute x y) :
    OddCommute (e x) (e y) := by
  intro c hc hodd
  have hc' : e.symm c * x = x * e.symm c := by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hc]
  have hodd' : Odd (orderOf (e.symm c)) := by
    rwa [MulEquiv.orderOf_eq]
  have h' := congrArg e (h _ hc' hodd')
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'

theorem oddCommute_conj (g : G) {x y : G} (h : OddCommute x y) :
    OddCommute (g * x * g⁻¹) (g * y * g⁻¹) :=
  oddCommute_map (MulAut.conj g) h

end CFSG.ComponentClassification.RankTwoExceptional.Step83Pair
