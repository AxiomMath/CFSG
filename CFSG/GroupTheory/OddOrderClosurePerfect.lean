module

public import CFSG.GroupTheory.OddOrderClosure

public section

namespace CFSG.GroupTheory

theorem oddOrderClosure_eq_top_of_isPerfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : oddOrderClosure (⊤ : Subgroup H) = ⊤ := by
  let N : Subgroup H := oddOrderClosure (⊤ : Subgroup H)
  haveI hN : N.Normal := by
    refine Subgroup.Normal.mk fun n hn g => ?_
    have hg : g ∈ Subgroup.normalizer N := by
      have h := normalizer_le_normalizer_oddOrderClosure (⊤ : Subgroup H)
      exact h (Subgroup.le_normalizer (H := (⊤ : Subgroup H)) (Subgroup.mem_top g))
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have hq : IsPGroup 2 (H ⧸ N) := by
    obtain ⟨k, hk⟩ := index_oddOrderClosure_eq_two_pow (⊤ : Subgroup H)
    rw [IsPGroup.iff_card]
    refine ⟨k, ?_⟩
    rw [← Subgroup.index_eq_card]
    exact (Subgroup.relIndex_top_right (oddOrderClosure (⊤ : Subgroup H))).symm.trans hk
  have hperf : Group.IsPerfect (H ⧸ N) := by
    have hmap : Group.IsPerfect
        ((⊤ : Subgroup H).map (QuotientGroup.mk' N : H →* H ⧸ N)) :=
      Group.IsPerfect.map (QuotientGroup.mk' N : H →* H ⧸ N)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at hmap
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.topEquiv (G := H ⧸ N)).toMonoidHom)
      (Subgroup.topEquiv (G := H ⧸ N)).surjective
  have hbot : Subsingleton (H ⧸ N) := by
    by_contra h
    haveI : Nontrivial (H ⧸ N) := not_subsingleton_iff_nontrivial.mp h
    exact (Group.IsPerfect.not_isNilpotent (G := H ⧸ N)) hq.isNilpotent
  rw [eq_top_iff]
  intro x _
  have hx : QuotientGroup.mk' N x = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff (N := N) (x := x)).1
    (by simpa only [QuotientGroup.mk'_apply] using hx)

theorem map_le_of_isPerfect_of_forall_odd_order {G H : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] [Group H] (f : G →* H) (K : Subgroup H)
    (h : ∀ x : G, Odd (orderOf x) → f x ∈ K) : ∀ x : G, f x ∈ K := by
  have hle : oddOrderClosure (⊤ : Subgroup G) ≤ K.comap f := by
    rw [oddOrderClosure_le_iff]
    rintro x ⟨-, hx⟩
    exact h x hx
  rw [oddOrderClosure_eq_top_of_isPerfect] at hle
  intro x
  exact hle (Subgroup.mem_top x)

theorem oddOrderClosure_eq_self_of_commutator_eq {G : Type*} [Group G] [Finite G]
    {Y : Subgroup G} (hY : ⁅Y, Y⁆ = Y) : oddOrderClosure Y = Y := by
  refine le_antisymm (oddOrderClosure_le Y) ?_
  letI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  have h : ∀ x : ↥Y, Y.subtype x ∈ oddOrderClosure Y :=
    map_le_of_isPerfect_of_forall_odd_order (f := Y.subtype) (K := oddOrderClosure Y)
      (fun x hx => mem_oddOrderClosure_of_mem_of_odd x.2 (by simpa using hx))
  intro y hy
  simpa using h ⟨y, hy⟩

end CFSG.GroupTheory

end
