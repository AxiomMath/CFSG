module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem le_of_relIndex_two_of_forall_relIndex_ne_two {N K K' E : Subgroup G}
    (hK'N : K' ≤ N) (hK : K.relIndex N = 2) (hEK : E ≤ K) (hEK' : E ≤ K')
    (hQ : ∀ L : Subgroup G, E ≤ L → L ≤ K' → L.relIndex K' ≠ 2) : K' ≤ K := by
  have hne0 : K.relIndex K' ≠ 0 := by
    have hd := Subgroup.relIndex_dvd_card (H := K) (K := K')
    exact (Nat.pos_of_dvd_of_pos hd Nat.card_pos).ne'
  have hle : K.relIndex K' ≤ K.relIndex N :=
    Subgroup.relIndex_le_of_le_right hK'N (by rw [hK]; norm_num)
  rw [hK] at hle
  have hcases : K.relIndex K' = 1 ∨ K.relIndex K' = 2 := by omega
  rcases hcases with h1 | h2
  · exact Subgroup.relIndex_eq_one.mp h1
  · exact absurd ((Subgroup.inf_relIndex_right (H := K) (K := K')).trans h2)
      (hQ (K ⊓ K') (le_inf hEK hEK') inf_le_right)

omit [Finite G] in
theorem forall_relIndex_ne_two_iff_quotient {E K : Subgroup G} (hEK : E ≤ K)
    [hN : (E.subgroupOf K).Normal] :
    (∀ L : Subgroup G, E ≤ L → L ≤ K → L.relIndex K ≠ 2) ↔
      ∀ T : Subgroup (↥K ⧸ E.subgroupOf K), T.index ≠ 2 := by
  constructor
  · intro hQ T hT
    let L : Subgroup G := (T.comap (QuotientGroup.mk' (E.subgroupOf K))).map K.subtype
    have hEL : E ≤ L := by
      intro e he
      refine ⟨⟨e, hEK he⟩, ?_, rfl⟩
      have h1 : QuotientGroup.mk' (E.subgroupOf K) ⟨e, hEK he⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr he
      change QuotientGroup.mk' (E.subgroupOf K) ⟨e, hEK he⟩ ∈ T
      rw [h1]
      exact T.one_mem
    have hLK : L ≤ K := Subgroup.map_subtype_le _
    have hLi : L.relIndex K = 2 := by
      change
        (((T.comap (QuotientGroup.mk' (E.subgroupOf K))).map K.subtype).subgroupOf K).index = 2
      rw [Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective K),
        Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hT]
    exact hQ L hEL hLK hLi
  · intro hT L hEL hLK hL2
    let T : Subgroup (↥K ⧸ E.subgroupOf K) :=
      (L.subgroupOf K).map (QuotientGroup.mk' (E.subgroupOf K))
    have hTi : T.index = 2 := by
      rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)]
      · exact hL2
      · rw [QuotientGroup.ker_mk']
        exact fun x hx => hEL (Subgroup.mem_subgroupOf.mp hx)
    exact hT T hTi

end CFSG.GroupTheory
