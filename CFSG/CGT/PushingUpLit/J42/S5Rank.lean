module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.CGT.PushingUpLit.SolK

theorem closure_union_eq_of_normalClosure {G : Type*} [Group G] [Finite G] {H L : Subgroup G}
    (hH2 : IsPGroup 2 H) (hLH : L ≤ H) {s t : Set G} (hs : s ⊆ H) (ht : t ⊆ L)
    (hsL : Subgroup.closure s ⊔ L = H)
    (htL : ∀ N : Subgroup G, N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → t ⊆ N → L ≤ N) :
    Subgroup.closure (s ∪ t) = H := by
  classical
  have hcl : Subgroup.closure (s ∪ t) ≤ H :=
    (Subgroup.closure_le H).2 (Set.union_subset hs (ht.trans hLH))
  refine le_antisymm hcl ?_
  by_contra hcon
  have hnil : Group.IsNilpotent ↥H := hH2.isNilpotent
  have hne : (Subgroup.closure (s ∪ t)).subgroupOf H ≠ ⊤ := by
    intro htop
    apply hcon
    intro y hy
    have : (⟨y, hy⟩ : ↥H) ∈ (Subgroup.closure (s ∪ t)).subgroupOf H := by rw [htop]; trivial
    exact this
  obtain ⟨M', hM', hle⟩ :=
    (eq_top_or_exists_le_coatom ((Subgroup.closure (s ∪ t)).subgroupOf H)).resolve_left hne
  have hnorm : M'.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M'
      (Group.normalizerCondition_of_isNilpotent (G := ↥H)) hM'
  set N : Subgroup G := M'.map H.subtype with hN
  have hNH : N ≤ H := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hmemN : ∀ y : G, y ∈ Subgroup.closure (s ∪ t) → y ∈ N := by
    intro y hy
    refine ⟨⟨y, hcl hy⟩, hle ?_, rfl⟩
    exact hy
  have hNinv : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    rintro h hh _ ⟨n, hn, rfl⟩
    exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hnorm.conj_mem n hn ⟨h, hh⟩, rfl⟩
  have htN : t ⊆ N := fun y hy => hmemN y (Subgroup.subset_closure (Or.inr hy))
  have hLN : L ≤ N := htL N hNH hNinv htN
  have hsN : Subgroup.closure s ≤ N := by
    rw [Subgroup.closure_le]
    exact fun y hy => hmemN y (Subgroup.subset_closure (Or.inl hy))
  have hHN : H ≤ N := hsL ▸ sup_le hsN hLN
  apply hM'.1
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, hz, hzy⟩ := hHN y.2
  have : z = y := Subtype.ext hzy
  rwa [this] at hz

theorem exists_card_le_of_normalClosure {G : Type*} [Group G] [Finite G] {H L : Subgroup G}
    (hH2 : IsPGroup 2 H) (hLH : L ≤ H) {s t : Finset G} (hs : (s : Set G) ⊆ H)
    (ht : (t : Set G) ⊆ L) (hsL : Subgroup.closure (s : Set G) ⊔ L = H)
    (htL : ∀ N : Subgroup G, N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → (t : Set G) ⊆ N →
      L ≤ N) :
    ∃ r : Finset G, r.card ≤ s.card + t.card ∧ Subgroup.closure (r : Set G) = H := by
  classical
  refine ⟨s ∪ t, Finset.card_union_le s t, ?_⟩
  rw [Finset.coe_union]
  exact closure_union_eq_of_normalClosure hH2 hLH hs ht hsL htL

end CFSG.CGT.PushingUpLit.SolK
