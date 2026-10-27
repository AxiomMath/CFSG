module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfGen

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open Subgroup

variable {G : Type*} [Group G]

theorem mem_normalizer_of_gens {gens : Set G} {E : Subgroup G} [Finite E] (hE : E = closure gens)
    {x : G} (h : ∀ g ∈ gens, x * g * x⁻¹ ∈ E) : x ∈ normalizer (E : Set G) := by
  have hle : E.map (MulAut.conj x).toMonoidHom ≤ E := by
    rw [hE, MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [← hE]
    exact h g hg
  have heq : E.map (MulAut.conj x).toMonoidHom = E :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj x).injective])
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hle ⟨y, hy, rfl⟩
  · intro hy
    rw [← heq] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    have : w = y := by
      have h2 : x * w * x⁻¹ = x * y * x⁻¹ := hwy
      simpa using h2
    rwa [← this]

theorem mem_centralizer_of_gens {gens : Set G} {E : Subgroup G} (hE : E = closure gens) {x : G}
    (h : ∀ g ∈ gens, g * x = x * g) : x ∈ centralizer (E : Set G) := by
  have hle : E ≤ centralizer ({x} : Set G) := by
    rw [hE, closure_le]
    intro g hg
    exact mem_centralizer_singleton_iff.2 (h g hg)
  rw [mem_centralizer_iff]
  intro y hy
  exact mem_centralizer_singleton_iff.1 (hle hy)

theorem center_map_eq_of_gens {gens : Set G} {E S : Subgroup G} (hE : E = closure gens)
    (hSE : S ≤ E) (hS : ∀ s ∈ S, ∀ g ∈ gens, g * s = s * g)
    (h : ∀ x ∈ E, (∀ g ∈ gens, g * x = x * g) → x ∈ S) : (center E).map E.subtype = S := by
  have hgE : ∀ g ∈ gens, g ∈ E := fun g hg => by rw [hE]; exact subset_closure hg
  ext x
  rw [mem_center_map_subtype]
  constructor
  · rintro ⟨hx, hc⟩
    exact h x hx fun g hg => hc g (hgE g hg)
  · intro hx
    refine ⟨hSE hx, fun y hy => ?_⟩
    have := mem_centralizer_of_gens hE (hS x hx)
    exact (mem_centralizer_iff.1 this) y hy

theorem zpow_involution {s : G} (hs : s * s = 1) (k : ℤ) : s ^ k = 1 ∨ s ^ k = s := by
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  induction k using Int.induction_on with
  | zero => exact Or.inl (zpow_zero s)
  | succ i ih =>
    rw [zpow_add_one]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr (one_mul s)
    · exact Or.inl hs
  | pred i ih =>
    rw [zpow_sub_one, hinv]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr (one_mul s)
    · exact Or.inl hs

theorem commutator_zpowers_eq {E : Subgroup G} {s c e₁ : G} (hs : s * s = 1)
    (hc : ∀ e ∈ E, e * s * e⁻¹ * s⁻¹ ∈ zpowers c) (he₁ : e₁ ∈ E)
    (hce : e₁ * s * e₁⁻¹ * s⁻¹ = c) : ⁅E, zpowers s⁆ = zpowers c := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro e he t ht
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
    rcases zpow_involution hs k with h | h
    · rw [h, commutatorElement_one_right]
      exact one_mem _
    · rw [h, commutatorElement_def]
      exact hc e he
  · rw [zpowers_le, ← hce, ← commutatorElement_def]
    exact commutator_mem_commutator he₁ (mem_zpowers s)

omit [Group G] in
theorem natCard_eq_length {S : Set G} {L : List G} (hL : L.Nodup) (h : ∀ x, x ∈ S ↔ x ∈ L) :
    Nat.card S = L.length := by
  classical
  have hS : S = (L.toFinset : Set G) := by
    ext x
    rw [h, Finset.mem_coe, List.mem_toFinset]
  rw [hS, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]

theorem mem_sup_zpowers_of_mem_list {z τ x : G} (h : x = 1 ∨ x = z ∨ x = τ ∨ x = z * τ) :
    x ∈ zpowers z ⊔ zpowers τ := by
  have hz : z ∈ zpowers z ⊔ zpowers τ := mem_sup_left (mem_zpowers z)
  have hτ : τ ∈ zpowers z ⊔ zpowers τ := mem_sup_right (mem_zpowers τ)
  rcases h with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hz
  · exact hτ
  · exact mul_mem hz hτ


theorem mem_zpowers_involution {z x : G} (hz : z * z = 1) : x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact zpow_involution hz k
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem center_eq_of_gens {gens : Set G} {E : Subgroup G} (hE : E = closure gens) {z : G}
    (hz : z * z = 1) (h : ∀ x ∈ E, (∀ g ∈ gens, g * x = x * g) ↔ (x = 1 ∨ x = z)) :
    center E = (zpowers z).subgroupOf E := by
  have hgE : ∀ g ∈ gens, g ∈ E := fun g hg => by rw [hE]; exact subset_closure hg
  ext x
  rw [mem_center_iff, mem_subgroupOf, mem_zpowers_involution hz, ← h x x.2]
  constructor
  · intro hc g hg
    exact congrArg Subtype.val (hc ⟨g, hgE g hg⟩)
  · intro hc y
    exact Subtype.ext ((mem_centralizer_iff.1 (mem_centralizer_of_gens hE hc)) y y.2)

theorem dihedral_of_gens [Finite G] {r s : G} (hr : orderOf r = 4) (hs : s * s = 1)
    (hrel : s * r * s⁻¹ = r⁻¹) (hsr : s ∉ zpowers r) :
    Nonempty (closure ({r, s} : Set G) ≃* DihedralGroup 4) := by
  set D := closure ({r, s} : Set G)
  have hrD : r ∈ D := subset_closure (Set.mem_insert _ _)
  have hsD : s ∈ D := subset_closure (Set.mem_insert_of_mem _ rfl)
  let ρ : D := ⟨r, hrD⟩
  let σ : D := ⟨s, hsD⟩
  have hgen : ⊤ = zpowers ρ ⊔ zpowers σ := by
    apply map_injective D.subtype_injective
    rw [← MonoidHom.range_eq_map, range_subtype, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers]
    show closure ({r, s} : Set G) = zpowers r ⊔ zpowers s
    rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union, Set.insert_eq]
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simp [σ, pow_two, hs])
  have hrel' : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by simpa [σ, ρ] using hrel)
  have hσρ : σ ∉ zpowers ρ := by
    intro h
    apply hsr
    have := mem_map_of_mem D.subtype h
    rwa [MonoidHom.map_zpowers] at this
  have hρ : orderOf ρ = 4 := by rw [← Subgroup.orderOf_coe]; exact hr
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel' hσρ
  rw [hρ] at e
  exact ⟨e⟩

end CFSG.ComponentClassification.CatFactsSmall
