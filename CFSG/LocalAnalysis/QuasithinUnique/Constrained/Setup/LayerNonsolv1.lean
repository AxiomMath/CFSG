module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab1

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem oddGen_subgroupOf (H : Subgroup (V ≃ₗ[k] V)) :
    (oddGen H).subgroupOf H = Subgroup.closure {h : ↥H | Odd (orderOf h)} := by
  have h : oddGen H = (Subgroup.closure {h : ↥H | Odd (orderOf h)}).map H.subtype := by
    unfold oddGen
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype]
    constructor
    · rintro ⟨hx, hodd⟩
      exact ⟨⟨x, hx⟩, by rw [← Subgroup.orderOf_coe]; exact hodd, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  rw [h]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem kerIn_le_of_le {X : Type*} [Group X] {M H : Subgroup X} (hMH : M ≤ H) :
    kerIn M H ≤ H := fun _ hx => hMH (kerIn_le hx)

theorem isSolvable_of_commutator_comm {X : Type*} [Group X] (B : Subgroup X)
    (hB : ∀ x ∈ ⁅B, B⁆, ∀ y ∈ ⁅B, B⁆, x * y = y * x) : Group.IsSolvable ↥B := by
  refine ⟨⟨2, ?_⟩⟩
  have h1 : (commutator ↥B).map B.subtype = ⁅B, B⁆ := by
    rw [commutator_def, Subgroup.map_commutator, map_subtype_top]
  rw [derivedSeries_succ, derivedSeries_one, eq_bot_iff]
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  apply Subtype.ext
  show (x : X) * y = y * x
  exact hB x (h1 ▸ ⟨x, hx, rfl⟩) y (h1 ▸ ⟨y, hy, rfl⟩)

end CFSG.QuasithinUnique.Setup.Layer
