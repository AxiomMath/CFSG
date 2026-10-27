module

public import CFSG.Dihedral.OriginalFourgroupsGeneral
import all CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint

universe u v

theorem kleinFour_hom_eq_one_of_cycle {K : Type u} [Group K] [IsKleinFour K]
    {X : Type v} [Group X] (a : MulAut K)
    (ha : ∀ k : K, k ≠ 1 → a k ≠ k) (f : K →* X)
    (hfixed : ∀ k : K, f (a k) = f k) : ∀ k : K, f k = 1 := by
  intro k
  by_cases hk : k = 1
  · simp [hk]
  have hak : a k ≠ 1 := fun h => hk (a.injective (by simpa using h))
  have hneq : a k ≠ k := ha k hk
  have haak : a (a k) ≠ 1 := fun h => hak (a.injective (by simpa using h))
  have haakne : a (a k) ≠ a k := ha (a k) hak
  have haaknek : a (a k) ≠ k := by
    intro h
    have hprod : k * a k ≠ 1 := by
      intro hprod
      have heq : a k = k := by
        have h := mul_eq_one_iff_eq_inv.mp hprod
        simpa only [IsKleinFour.inv_eq_self] using h.symm
      exact hneq heq
    have hfix : a (k * a k) = k * a k := by
      rw [map_mul, h]
      exact IsKleinFour.isMulCommutative.is_comm.comm _ _
    exact ha (k * a k) hprod hfix
  have hthird : a (a k) = k * a k :=
    IsKleinFour.eq_mul_of_ne_all hk hak hneq.symm haak haaknek haakne
  have hmul : f k * f (a k) = 1 * f (a k) := by
    rw [← map_mul, ← hthird, hfixed, one_mul]
  exact mul_right_cancel hmul

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cycles_le_ker_of_commutative_quotient {X : Type} [Group X]
    [IsMulCommutative X] (H V : Subgroup G) (hV : IsKleinFour V)
    (hVH : V ≤ H) (hc : Cycles H V) (f : H →* X) :
    V ≤ f.ker.map H.subtype := by
  let : IsKleinFour V := hV
  obtain ⟨x, hxH, hxN, hxmove⟩ := hc
  let a : MulAut V := V.normalizerMonoidHom ⟨x, hxN⟩
  have ha : ∀ v : V, v ≠ 1 → a v ≠ v := by
    intro v hv heq
    exact hxmove v v.property (fun h => hv (Subtype.ext h))
      (congrArg Subtype.val heq)
  let fV : V →* X := f.comp (Subgroup.inclusion hVH)
  have hfixed : ∀ v : V, fV (a v) = fV v := by
    intro v
    have heq : (Subgroup.inclusion hVH) (a v) =
        (⟨x, hxH⟩ : H) * (Subgroup.inclusion hVH v) * (⟨x, hxH⟩ : H)⁻¹ := by
      apply Subtype.ext
      exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
    change f ((Subgroup.inclusion hVH) (a v)) = f ((Subgroup.inclusion hVH) v)
    rw [heq, map_mul, map_mul, map_inv,
      IsMulCommutative.is_comm.comm (f (⟨x, hxH⟩ : H))]
    simp [mul_assoc]
  have hall := kleinFour_hom_eq_one_of_cycle a ha fV hfixed
  intro v hv
  exact Subgroup.mem_map.mpr
    ⟨⟨v, hVH hv⟩, hall ⟨v, hv⟩, rfl⟩

omit [Finite G] in
theorem cycling_fourgroup_le_indexTwo (H V K : Subgroup G)
    (hV : IsKleinFour V) (hVH : V ≤ H) (hc : Cycles H V)
    (hKH : K ≤ H) (hnormal : (K.subgroupOf H).Normal)
    (hindex : (K.subgroupOf H).index = 2) : V ≤ K := by
  let : (K.subgroupOf H).Normal := hnormal
  let Q := H ⧸ K.subgroupOf H
  have hcard : Nat.card Q = 2 := by
    rw [← Subgroup.index_eq_card, hindex]
  let : IsCyclic Q := isCyclic_of_prime_card hcard
  let : IsMulCommutative Q := IsCyclic.isMulCommutative
  have hle := cycles_le_ker_of_commutative_quotient H V hV hVH hc
    (QuotientGroup.mk' (K.subgroupOf H))
  rwa [QuotientGroup.ker_mk', Subgroup.map_subgroupOf_eq_of_le hKH] at hle

namespace OriginalData

variable (d : OriginalData G)

theorem V_sup_eq_sylow : d.V 0 ⊔ d.V 1 = (d.S : Subgroup G) := by
  apply le_antisymm (sup_le (d.V_le_sylow 0) (d.V_le_sylow 1))
  rw [← d.generators]
  apply (Subgroup.closure_le _).mpr
  have hs : d.s ∈ d.V 0 ⊔ d.V 1 :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hsr : d.s * d.r ∈ d.V 0 ⊔ d.V 1 :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hr : d.r ∈ d.V 0 ⊔ d.V 1 := by
    simpa only [inv_mul_cancel_left] using (d.V 0 ⊔ d.V 1).mul_mem
      ((d.V 0 ⊔ d.V 1).inv_mem hs) hsr
  intro x hx
  rcases hx with rfl | hx
  · exact hr
  · rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hs

theorem no_indexTwo_of_both_cycles (H : Subgroup G)
    (hSH : (d.S : Subgroup G) ≤ H)
    (hc0 : Cycles H (d.V 0)) (hc1 : Cycles H (d.V 1)) : ¬ HasNormalIndexTwo H := by
  rintro ⟨K, hKH, hnormal, hindex⟩
  have hV0 := cycling_fourgroup_le_indexTwo H (d.V 0) K (d.V_isKleinFour_general 0)
    ((d.V_le_sylow 0).trans hSH) hc0 hKH hnormal hindex
  have hV1 := cycling_fourgroup_le_indexTwo H (d.V 1) K (d.V_isKleinFour_general 1)
    ((d.V_le_sylow 1).trans hSH) hc1 hKH hnormal hindex
  have hSK : (d.S : Subgroup G) ≤ K := by
    rw [← d.V_sup_eq_sylow]
    exact sup_le hV0 hV1
  have hprod := Subgroup.relIndex_mul_relIndex (d.S : Subgroup G) K H hSK hKH
  change ((d.S : Subgroup G).relIndex K) * (K.subgroupOf H).index =
    (d.S : Subgroup G).relIndex H at hprod
  have htwo : 2 ∣ (d.S : Subgroup G).index := by
    have ht : 2 ∣ (d.S : Subgroup G).relIndex H := by
      rw [← hprod, hindex]
      exact dvd_mul_left 2 _
    have hprodH := Subgroup.relIndex_mul_index hSH
    rw [← hprodH]
    exact dvd_mul_of_dvd_left ht _
  exact d.S.not_dvd_index htwo

theorem centralizer_overgroup_not_both_cycles (H : Subgroup G) (hH : H ≠ ⊤)
    (hCH : d.C ≤ H) : ¬ (Cycles H (d.V 0) ∧ Cycles H (d.V 1)) := by
  rintro ⟨hc0, hc1⟩
  exact d.no_indexTwo_of_both_cycles H (d.sylow_le_centralizer.trans hCH) hc0 hc1
    (d.index_two H hH hCH)

end OriginalData

end CFSG.DihedralBlueprint
