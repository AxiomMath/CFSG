module

public import CFSG.CGT.Timmesfeld75.Sec62Orbit
public import CFSG.CGT.Timmesfeld75.NormalClosure

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

structure PlaneData (𝒯 : Set (Subgroup G)) (q c : ℕ) : Prop where
  closed : ∀ R ∈ 𝒯, ∀ S ∈ 𝒯, ∀ t ∈ R, conjSubgroup t S ∈ 𝒯
  card_eq : ∀ R ∈ 𝒯, ∀ S ∈ 𝒯, R ≠ S → Nat.card ↥R = q * Nat.card ↥(normIn R S)
  card_sup : ∀ R ∈ 𝒯, ∀ S ∈ 𝒯, R ≠ S → Nat.card ↥(R ⊔ S) = c

section Plane

variable {𝒯 : Set (Subgroup G)} {q c : ℕ} {P₁ P₂ P₃ : Subgroup G}

theorem PlaneData.ncard_conjSet (D : PlaneData 𝒯 q c) {R S : Subgroup G} (hR : R ∈ 𝒯)
    (hS : S ∈ 𝒯) (hne : R ≠ S) : (conjSet R S).ncard = q := by
  have h := ncard_conjSet_mul_card R S
  rw [D.card_eq R hR S hS hne] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

omit [Finite G] in
theorem PlaneData.conjSet_subset (D : PlaneData 𝒯 q c) {R S : Subgroup G} (hR : R ∈ 𝒯)
    (hS : S ∈ 𝒯) : conjSet R S ⊆ 𝒯 := by
  rintro _ ⟨t, ht, rfl⟩
  exact D.closed R hR S hS t ht

omit [Finite G] in
theorem le_sup_of_mem_line {Z : Subgroup G} (hZ : Z ∈ insert P₁ (conjSet P₁ P₂)) :
    Z ≤ P₁ ⊔ P₂ := by
  rcases hZ with rfl | ⟨t, ht, rfl⟩
  · exact le_sup_left
  · exact conjSubgroup_le_of_le_of_mem le_sup_right (Subgroup.mem_sup_left ht)

theorem PlaneData.ncard_line (D : PlaneData 𝒯 q c) (h₁ : P₁ ∈ 𝒯) (h₂ : P₂ ∈ 𝒯)
    (h12 : P₁ ≠ P₂) : (insert P₁ (conjSet P₁ P₂)).ncard = q + 1 := by
  have hnot : P₁ ∉ conjSet P₁ P₂ := by
    rintro ⟨t, ht, e⟩
    refine h12 ?_
    have h1 := congrArg (conjSubgroup t⁻¹) e
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
    rw [← h1]
    exact (mem_normalizer_iff_conjSubgroup_eq.1 (Subgroup.le_normalizer (P₁.inv_mem ht))).symm
  rw [Set.ncard_insert_of_notMem hnot (Set.toFinite _), D.ncard_conjSet h₁ h₂ h12]

theorem PlaneData.disjoint_orbits (D : PlaneData 𝒯 q c) (h₁ : P₁ ∈ 𝒯) (h₂ : P₂ ∈ 𝒯)
    (h₃ : P₃ ∈ 𝒯) (h3 : ¬ P₃ ≤ P₁ ⊔ P₂) {R R' : Subgroup G}
    (hR : R ∈ insert P₁ (conjSet P₁ P₂)) (hR' : R' ∈ insert P₁ (conjSet P₁ P₂)) (hne : R ≠ R') :
    Disjoint (conjSet R P₃ \ {P₃}) (conjSet R' P₃ \ {P₃}) := by
  have hR𝒯 : R ∈ 𝒯 := by
    rcases hR with rfl | hR
    · exact h₁
    · exact D.conjSet_subset h₁ h₂ hR
  have hR'𝒯 : R' ∈ 𝒯 := by
    rcases hR' with rfl | hR'
    · exact h₁
    · exact D.conjSet_subset h₁ h₂ hR'
  have hRle := le_sup_of_mem_line hR
  have hR'le := le_sup_of_mem_line hR'
  have hRP : R ≠ P₃ := fun h => h3 (h ▸ hRle)
  have hR'P : R' ≠ P₃ := fun h => h3 (h ▸ hR'le)
  refine Set.disjoint_left.2 fun Z hZ hZ' => ?_
  obtain ⟨⟨s, hs, hZs⟩, hZne⟩ := hZ
  obtain ⟨⟨s', hs', hZs'⟩, -⟩ := hZ'
  have hZne' : Z ≠ P₃ := hZne
  have hZ𝒯 : Z ∈ 𝒯 := hZs ▸ D.closed R hR𝒯 P₃ h₃ s hs
  have hZ1 : P₃ ⊔ Z = R ⊔ P₃ := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_right ?_) ?_
    · rw [hZs]
      exact conjSubgroup_le_of_le_of_mem le_sup_right (Subgroup.mem_sup_left hs)
    · rw [D.card_sup R hR𝒯 P₃ h₃ hRP, D.card_sup P₃ h₃ Z hZ𝒯 hZne'.symm]
  have hZ2 : P₃ ⊔ Z = R' ⊔ P₃ := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_right ?_) ?_
    · rw [hZs']
      exact conjSubgroup_le_of_le_of_mem le_sup_right (Subgroup.mem_sup_left hs')
    · rw [D.card_sup R' hR'𝒯 P₃ h₃ hR'P, D.card_sup P₃ h₃ Z hZ𝒯 hZne'.symm]
  have hR'sub : R' ≤ R ⊔ P₃ := hZ1 ▸ hZ2 ▸ le_sup_left
  have hRR' : R ⊔ R' = R ⊔ P₃ := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hR'sub) ?_
    rw [D.card_sup R hR𝒯 P₃ h₃ hRP, D.card_sup R hR𝒯 R' hR'𝒯 hne]
  exact h3 ((le_sup_right : P₃ ≤ R ⊔ P₃).trans (hRR' ▸ sup_le hRle hR'le))

theorem PlaneData.card_ge (D : PlaneData 𝒯 q c) (hq : 1 ≤ q) (h₁ : P₁ ∈ 𝒯) (h₂ : P₂ ∈ 𝒯)
    (h₃ : P₃ ∈ 𝒯) (h12 : P₁ ≠ P₂) (h3 : ¬ P₃ ≤ P₁ ⊔ P₂) : q ^ 2 + q + 1 ≤ 𝒯.ncard := by
  set ℓ₀ := insert P₁ (conjSet P₁ P₂) with hℓ₀
  have hℓ𝒯 : ℓ₀ ⊆ 𝒯 := Set.insert_subset h₁ (D.conjSet_subset h₁ h₂)
  have hmem : ∀ R ∈ ℓ₀, R ∈ 𝒯 := fun R hR => hℓ𝒯 hR
  have hne3 : ∀ R ∈ ℓ₀, R ≠ P₃ := fun R hR h => h3 (h ▸ le_sup_of_mem_line hR)
  have hcardR : ∀ R ∈ ℓ₀, ((conjSet R P₃) \ {P₃}).ncard = q - 1 := by
    intro R hR
    have hP₃ : P₃ ∈ conjSet R P₃ := ⟨1, R.one_mem, (conjSubgroup_one P₃).symm⟩
    rw [Set.ncard_sdiff_singleton_of_mem hP₃,
      D.ncard_conjSet (hmem R hR) h₃ (hne3 R hR)]
  have hU := ncard_biUnion_const (Set.toFinite ℓ₀) (s := fun R => (conjSet R P₃) \ {P₃})
    (m := q - 1) (fun R hR R' hR' hne => D.disjoint_orbits h₁ h₂ h₃ h3 hR hR' hne) hcardR
  set Ω₂ := insert P₃ (⋃ R ∈ ℓ₀, (conjSet R P₃) \ {P₃}) with hΩ₂
  have hΩ₂𝒯 : Ω₂ ⊆ 𝒯 := by
    refine Set.insert_subset h₃ (Set.iUnion₂_subset fun R hR => ?_)
    exact Set.sdiff_subset.trans (D.conjSet_subset (hmem R hR) h₃)
  have hnot : P₃ ∉ ⋃ R ∈ ℓ₀, (conjSet R P₃) \ {P₃} := by
    intro hmem'
    simp only [Set.mem_iUnion] at hmem'
    obtain ⟨R, -, -, hP⟩ := hmem'
    exact hP rfl
  have hΩ₂card : Ω₂.ncard = ℓ₀.ncard * (q - 1) + 1 := by
    rw [hΩ₂, Set.ncard_insert_of_notMem hnot (Set.toFinite _), hU]
  have hdisj : Disjoint ℓ₀ Ω₂ := by
    refine Set.disjoint_left.2 fun Z hZ hZ' => ?_
    have hZle := le_sup_of_mem_line hZ
    rcases hZ' with hZP | hZ'
    · exact h3 (hZP ▸ hZle)
    · simp only [Set.mem_iUnion] at hZ'
      obtain ⟨R, hR, ⟨s, hs, hZs⟩, -⟩ := hZ'
      have hsX : s⁻¹ ∈ P₁ ⊔ P₂ := (P₁ ⊔ P₂).inv_mem (le_sup_of_mem_line hR hs)
      have h1 : conjSubgroup s⁻¹ Z = P₃ := by
        rw [hZs, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      exact h3 (h1 ▸ conjSubgroup_le_of_le_of_mem hZle hsX)
  have hcard1 : ℓ₀.ncard = q + 1 := D.ncard_line h₁ h₂ h12
  have hsub : ℓ₀ ∪ Ω₂ ⊆ 𝒯 := Set.union_subset hℓ𝒯 hΩ₂𝒯
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hΩ₂card, hcard1] at h
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  nlinarith [h]

end Plane

end CFSG.CGT.Timmesfeld75
