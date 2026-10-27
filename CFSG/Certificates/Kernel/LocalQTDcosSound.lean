module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Group
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.KC.LQT.CM

variable {G : Type*} [Group G] [DecidableEq G]

def dcos (T : Finset G) (r : G) : Finset G := (T ×ˢ T).image fun p => p.1 * r * p.2

structure IsSubF (T : Finset G) : Prop where
  one : 1 ∈ T
  mul : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T
  inv : ∀ a ∈ T, a⁻¹ ∈ T

theorem mem_dcos {T : Finset G} {r x : G} : x ∈ dcos T r ↔ ∃ a ∈ T, ∃ b ∈ T, a * r * b = x := by
  unfold dcos
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, b, ⟨ha, hb⟩, rfl⟩

theorem card_dcos {T : Finset G} (hT : IsSubF T) (r : G) :
    (dcos T r).card * (T.filter fun t => r⁻¹ * t * r ∈ T).card = T.card * T.card := by
  unfold dcos
  rw [← Finset.card_product T T,
    Finset.card_eq_sum_card_image (fun p : G × G => p.1 * r * p.2) (T ×ˢ T)]
  refine (Finset.sum_const_nat fun y hy => ?_).symm
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hy
  rw [Finset.mem_product] at hab
  obtain ⟨ha, hb⟩ := hab
  symm
  refine Finset.card_bij' (fun t _ => (a * t, r⁻¹ * t⁻¹ * r * b))
    (fun p _ => a⁻¹ * p.1) (fun t ht => ?_) (fun p hp => ?_) (fun t _ => ?_) (fun p hp => ?_)
  · rw [Finset.mem_filter] at ht ⊢
    have h2 : r⁻¹ * t⁻¹ * r ∈ T := by
      have := hT.inv _ ht.2
      simpa [mul_assoc] using this
    refine ⟨Finset.mem_product.2 ⟨hT.mul _ ha _ ht.1, hT.mul _ h2 _ hb⟩, ?_⟩
    dsimp only
    group
  · rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, he⟩ := hp
    dsimp only at he
    rw [Finset.mem_filter]
    refine ⟨hT.mul _ (hT.inv _ ha) _ h1, ?_⟩
    have e : r⁻¹ * (a⁻¹ * p.1) * r = b * p.2⁻¹ := by
      have hp1 : p.1 = a * r * b * p.2⁻¹ * r⁻¹ := by
        rw [← he]
        group
      have : a⁻¹ * p.1 = r * b * p.2⁻¹ * r⁻¹ := by
        rw [hp1]
        group
      rw [this]
      group
    rw [e]
    exact hT.mul _ hb _ (hT.inv _ h2)
  · dsimp only
    group
  · rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨-, -⟩, he⟩ := hp
    dsimp only at he ⊢
    refine Prod.ext (by group) ?_
    dsimp only
    have : p.2 = r⁻¹ * p.1⁻¹ * (a * r * b) := by
      rw [← he]
      group
    rw [this]
    group

def dcosU (T : Finset G) : List G → Finset G
  | [] => ∅
  | r :: rs => dcos T r ∪ dcosU T rs

theorem mem_dcosU {T : Finset G} {x : G} : ∀ {rs : List G}, x ∈ dcosU T rs ↔ ∃ r ∈ rs, x ∈ dcos T r
  | [] => by simp [dcosU]
  | r :: rs => by
    rw [dcosU, Finset.mem_union, mem_dcosU]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem disj_dcos {T : Finset G} (hT : IsSubF T) {r r' : G}
    (h : ∀ t ∈ T, r⁻¹ * t * r' ∉ T) : Disjoint (dcos T r) (dcos T r') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_dcos.1 hx
  obtain ⟨a', ha', b', hb', e⟩ := mem_dcos.1 hx'
  refine h (a⁻¹ * a') (hT.mul _ (hT.inv _ ha) _ ha') ?_
  have ea : a' = a * r * b * b'⁻¹ * r'⁻¹ := by
    rw [← e]
    group
  have : r⁻¹ * (a⁻¹ * a') * r' = b * b'⁻¹ := by
    rw [ea]
    group
  rw [this]
  exact hT.mul _ hb _ (hT.inv _ hb')

theorem card_dcosU {T : Finset G} (hT : IsSubF T) : ∀ {rs : List G},
    rs.Pairwise (fun r r' => ∀ t ∈ T, r⁻¹ * t * r' ∉ T) →
    (dcosU T rs).card = (rs.map fun r => (dcos T r).card).sum
  | [], _ => rfl
  | r :: rs, h => by
    rw [List.pairwise_cons] at h
    rw [dcosU, Finset.card_union_of_disjoint, card_dcosU hT h.2, List.map_cons, List.sum_cons]
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy e
    subst e
    obtain ⟨r', hr', hy⟩ := mem_dcosU.1 hy
    exact Finset.disjoint_left.1 (disj_dcos hT (h.1 r' hr')) hx hy

theorem cover_of_count {M T : Finset G} (hT : IsSubF T) (hTM : T ⊆ M)
    (hM : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M) {rs : List G} (hr : ∀ r ∈ rs, r ∈ M)
    (hd : rs.Pairwise (fun r r' => ∀ t ∈ T, r⁻¹ * t * r' ∉ T))
    (hs : (rs.map fun r => (dcos T r).card).sum = M.card) :
    ∀ x ∈ M, ∃ r ∈ rs, x ∈ dcos T r := by
  have hsub : dcosU T rs ⊆ M := fun x hx => by
    obtain ⟨r, hr', hx⟩ := mem_dcosU.1 hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_dcos.1 hx
    exact hM _ (hM _ (hTM ha) _ (hr r hr')) _ (hTM hb)
  have he : dcosU T rs = M :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_dcosU hT hd, hs])
  intro x hx
  rw [← he] at hx
  exact mem_dcosU.1 hx

end CFSG.KC.LQT.CM

end
