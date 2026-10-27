module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.Holt

open MulAction CFSG.Open

variable {X : Type*} [Group X] {Ω : Type*} [MulAction X Ω]

theorem exists_sylow_eq_subgroupOf_of_fusionIsSylowIn {p : ℕ} {R K : Subgroup X}
    (h : fusionIsSylowIn p R K) : ∃ S : Sylow p K, (S : Subgroup K) = R.subgroupOf K := by
  refine ⟨⟨R.subgroupOf K, h.2.1.comap_of_injective K.subtype K.subtype_injective,
    fun {Q} hQ hle => ?_⟩, rfl⟩
  have hmap := h.2.2 (Q.map K.subtype) (Subgroup.map_subtype_le Q) (hQ.map K.subtype)
    fun x hx => ⟨⟨x, h.1 hx⟩, hle hx, rfl⟩
  rw [← hmap]
  exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q).symm

variable [Finite X] [Finite Ω] [IsPretransitive X Ω] {z : X}

end CFSG.Holt
