module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Suzuki
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem false_of_selfCentralizing_four_of_elemTwo {T U E : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hU4 : Nat.card U = 4) (hUexp : ∀ u ∈ U, u * u = 1)
    (hC : T ⊓ centralizer (U : Set G) ≤ U) (hET : E ≤ T) (hE : ∀ x ∈ E, x * x = 1)
    (hE8 : 8 ≤ Nat.card E) : False := by
  have hne : U ≠ T := by
    rintro rfl
    have := card_le_of_le hET
    omega
  have hcardE : Nat.card ↥(E.subgroupOf T) = Nat.card E :=
    Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv
  have hexpE : ∀ x ∈ E.subgroupOf T, x ^ 2 = 1 := fun x hx => by
    apply Subtype.ext
    rw [coe_pow, pow_two, coe_one]
    exact hE x (mem_subgroupOf.mp hx)
  rcases QuasithinUnique.suzuki_selfCentralizing_four hT hUT hU4
    (fun u hu => by rw [pow_two]; exact hUexp u hu) hC hne with ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · set W := (E.subgroupOf T).map e.toMonoidHom with hW
    have hWc : Nat.card W = Nat.card E := by
      rw [hW, card_map_of_injective e.injective, hcardE]
    have hW2 : ∀ w ∈ W, w ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hexpE x hx, map_one]
    have := QuasithinUnique.dihedral_card_le_four (by omega) W hW2
    omega
  · set W := (E.subgroupOf T).map e.toMonoidHom with hW
    have hWc : Nat.card W = Nat.card E := by
      rw [hW, card_map_of_injective e.injective, hcardE]
    have hW2 : ∀ w ∈ W, w ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hexpE x hx, map_one]
    have := ABGDGroups.semidihedral_card_le_four hn W hW2
    omega

end CFSG.ComponentClassification.GrSLit.GrS5
