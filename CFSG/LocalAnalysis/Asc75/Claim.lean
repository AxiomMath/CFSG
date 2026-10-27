module

public import CFSG.LocalAnalysis.Asc75.Data

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

@[expose] def stabSet (U : Set G) : Subgroup G where
  carrier := {g | ∀ x, x ∈ U ↔ g⁻¹ * x * g ∈ U}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    rw [ha x, hb (a⁻¹ * x * a)]
    have e : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
    rw [e]
  inv_mem' := by
    intro a ha x
    have h := ha (a * x * a⁻¹)
    have e : a⁻¹ * (a * x * a⁻¹) * a = x := by group
    rw [e] at h
    have e2 : (a⁻¹)⁻¹ * x * a⁻¹ = a * x * a⁻¹ := by group
    rw [e2]
    exact h.symm

theorem mem_stabSet_iff {U : Set G} {g : G} :
    g ∈ stabSet U ↔ ∀ x, x ∈ U ↔ g⁻¹ * x * g ∈ U := Iff.rfl

theorem mem_stabSet_of_forall {U : Set G} {g : G} (h1 : ∀ x ∈ U, g⁻¹ * x * g ∈ U)
    (h2 : ∀ x ∈ U, g * x * g⁻¹ ∈ U) : g ∈ stabSet U := by
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this

section Swap

variable {S A₁ A₂ H : Subgroup G}

@[expose] def nU (S A₁ A₂ : Subgroup G) : Subgroup G := S ⊓ stabSet (uSet A₁ A₂)

theorem nU_le_S : nU S A₁ A₂ ≤ S := inf_le_left

theorem conjugate_subset_uSet {s : G} (hs : s ∈ stabSet (uSet A₁ A₂)) {A : Subgroup G}
    (hA : A = A₁ ∨ A = A₂) : (conjugate A s : Set G) ⊆ uSet A₁ A₂ := by
  intro y hy
  have hx : s * y * s⁻¹ ∈ A := mem_conjugate_iff.1 hy
  have hxU : s * y * s⁻¹ ∈ uSet A₁ A₂ := by
    rcases hA with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  have := (hs (s * y * s⁻¹)).1 hxU
  rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at this

end Swap

section Claim

variable [Finite G] {S A₁ A₂ H : Subgroup G}

theorem Hyp.A₁_le_nU (h : Hyp S A₁ A₂ H) : A₁ ≤ nU S A₁ A₂ := by
  intro a ha
  refine ⟨h.le₁ ha, mem_stabSet_of_forall (fun x hx => ?_) (fun x hx => ?_)⟩
  · rcases hx with hx | hx
    · exact Or.inl (A₁.mul_mem (A₁.mul_mem (A₁.inv_mem ha) hx) ha)
    · have : a⁻¹ * x * a = x := by
        rw [mul_assoc, ← h.comm a ha x hx]; group
      rw [this]; exact Or.inr hx
  · rcases hx with hx | hx
    · exact Or.inl (A₁.mul_mem (A₁.mul_mem ha hx) (A₁.inv_mem ha))
    · have : a * x * a⁻¹ = x := by
        rw [h.comm a ha x hx]; group
      rw [this]; exact Or.inr hx

theorem Hyp.A₂_le_nU (h : Hyp S A₁ A₂ H) : A₂ ≤ nU S A₁ A₂ := by
  intro b hb
  refine ⟨h.le₂ hb, mem_stabSet_of_forall (fun x hx => ?_) (fun x hx => ?_)⟩
  · rcases hx with hx | hx
    · have : b⁻¹ * x * b = x := by
        rw [mul_assoc, h.comm x hx b hb]; group
      rw [this]; exact Or.inl hx
    · exact Or.inr (A₂.mul_mem (A₂.mul_mem (A₂.inv_mem hb) hx) hb)
  · rcases hx with hx | hx
    · have : b * x * b⁻¹ = x := by
        rw [← h.comm x hx b hb]; group
      rw [this]; exact Or.inl hx
    · exact Or.inr (A₂.mul_mem (A₂.mul_mem hb hx) (A₂.inv_mem hb))

theorem swap_dichotomy {s : G} (hs : s ∈ stabSet (uSet A₁ A₂)) :
    s ∈ Subgroup.normalizer (A₁ : Set G) ∨ s ∈ Subgroup.normalizer (A₂ : Set G) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁) := by
  have h1 := SubgroupClass.subset_union.1 (conjugate_subset_uSet hs (A := A₁) (Or.inl rfl))
  have h2 := SubgroupClass.subset_union.1 (conjugate_subset_uSet hs (A := A₂) (Or.inr rfl))
  have c1 : Nat.card (conjugate A₁ s) = Nat.card A₁ := card_conjugate A₁ s
  have c2 : Nat.card (conjugate A₂ s) = Nat.card A₂ := card_conjugate A₂ s
  rcases h1 with h1 | h1
  · left
    exact mem_normalizer_of_conjugate_eq (Subgroup.eq_of_le_of_card_ge h1 c1.ge)
  · rcases h2 with h2 | h2
    · right; right
      have k1 : Nat.card A₁ ≤ Nat.card A₂ := c1 ▸ Subgroup.card_le_of_le h1
      have k2 : Nat.card A₂ ≤ Nat.card A₁ := c2 ▸ Subgroup.card_le_of_le h2
      exact ⟨Subgroup.eq_of_le_of_card_ge h1 (by omega), Subgroup.eq_of_le_of_card_ge h2 (by omega)⟩
    · right; left
      exact mem_normalizer_of_conjugate_eq (Subgroup.eq_of_le_of_card_ge h2 c2.ge)

theorem exists_good {X' : Subgroup G} (hX' : X' ≤ nU S A₁ A₂)
    (h4 : 4 ≤ Nat.card X') :
    ∃ y ∈ X', y ≠ 1 ∧ (y ∈ Subgroup.normalizer (A₁ : Set G) ∨
      y ∈ Subgroup.normalizer (A₂ : Set G)) := by
  have hne : X' ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h4
    omega
  obtain ⟨y₁', hy₁'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hy₁ : (y₁' : G) ∈ X' := y₁'.2
  have hy₁1 : (y₁' : G) ≠ 1 := fun e => hy₁' (Subtype.ext e)
  set y₁ : G := (y₁' : G) with hy₁def
  rcases swap_dichotomy (hX' hy₁).2 with h11 | h12 | ⟨h1a, h1b⟩
  · exact ⟨y₁, hy₁, hy₁1, Or.inl h11⟩
  · exact ⟨y₁, hy₁, hy₁1, Or.inr h12⟩
  · have : ∃ y₂ ∈ X', y₂ ≠ 1 ∧ y₂ ≠ y₁ := by
      by_contra hno
      push Not at hno
      have hsub : (X' : Set G) ⊆ {1, y₁} := by
        intro y hy
        by_cases hy1 : y = 1
        · simp [hy1]
        · simp [hno y hy hy1]
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({1, y₁} : Set G).ncard ≤ 2 := by
        calc ({1, y₁} : Set G).ncard ≤ ({y₁} : Set G).ncard + 1 := Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      rw [← Nat.card_coe_set_eq] at h1
      change Nat.card X' ≤ _ at h1
      omega
    obtain ⟨y₂, hy₂, hy₂1, hy₂y₁⟩ := this
    rcases swap_dichotomy (hX' hy₂).2 with h21 | h22 | ⟨h2a, h2b⟩
    · exact ⟨y₂, hy₂, hy₂1, Or.inl h21⟩
    · exact ⟨y₂, hy₂, hy₂1, Or.inr h22⟩
    · refine ⟨y₁⁻¹ * y₂, X'.mul_mem (X'.inv_mem hy₁) hy₂, ?_, Or.inl ?_⟩
      · intro e
        exact hy₂y₁ (inv_mul_eq_one.1 e).symm
      · apply mem_normalizer_of_conjugate_eq
        have e1 : conjugate A₁ y₁⁻¹ = A₂ := by
          rw [← h1b, conjugate_inv_conjugate]
        rw [conjugate_mul, e1]
        exact h2b


theorem Hyp.claim (h : Hyp S A₁ A₂ H) {X : Subgroup G} (hX : X ≤ A₁ ∨ X ≤ A₂)
    (h4 : 4 ≤ Nat.card X) {g : G} (hg : conjugate X g ≤ nU S A₁ A₂) :
    g ∈ H ∧ ∀ x ∈ X, g⁻¹ * x * g ∈ uSet A₁ A₂ := by
  have h4' : 4 ≤ Nat.card (conjugate X g) := by rw [card_conjugate]; exact h4
  obtain ⟨y, hyX, hy1, hyN⟩ := exists_good hg h4'
  have hx₀ : g * y * g⁻¹ ∈ X := mem_conjugate_iff.1 hyX
  have hxU : g * y * g⁻¹ ∈ uSet A₁ A₂ := by
    rcases hX with hX | hX
    · exact Or.inl (hX hx₀)
    · exact Or.inr (hX hx₀)
  have hyS : y ∈ S := nU_le_S (hg hyX)
  have hyeq : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  have hyU : y ∈ uSet A₁ A₂ := by
    rcases hyN with hN | hN
    · have := h.closed₁ _ hxU g (by rw [hyeq]; exact ⟨hyS, hN⟩)
      rwa [hyeq] at this
    · have := h.closed₂ _ hxU g (by rw [hyeq]; exact ⟨hyS, hN⟩)
      rwa [hyeq] at this
  have hx₀1 : g * y * g⁻¹ ≠ 1 := by
    intro e
    apply hy1
    rw [← hyeq, e]; group
  have hgH : g ∈ H := by
    rcases hX with hX | hX
    · have hAi : (A₁ = A₁ ∨ A₁ = A₂) := Or.inl rfl
      rcases hyU with hy | hy
      · exact h.mem_of_conj_mem hAi (Or.inl rfl) (hX hx₀) hx₀1 (by rw [hyeq]; exact hy)
      · exact h.mem_of_conj_mem hAi (Or.inr rfl) (hX hx₀) hx₀1 (by rw [hyeq]; exact hy)
    · have hAi : (A₂ = A₁ ∨ A₂ = A₂) := Or.inr rfl
      rcases hyU with hy | hy
      · exact h.mem_of_conj_mem hAi (Or.inl rfl) (hX hx₀) hx₀1 (by rw [hyeq]; exact hy)
      · exact h.mem_of_conj_mem hAi (Or.inr rfl) (hX hx₀) hx₀1 (by rw [hyeq]; exact hy)
  refine ⟨hgH, fun x hx => ?_⟩
  have hxU' : x ∈ uSet A₁ A₂ := by
    rcases hX with hX | hX
    · exact Or.inl (hX hx)
    · exact Or.inr (hX hx)
  have hS' : g⁻¹ * x * g ∈ S := nU_le_S (hg (conj_mem_conjugate hx g))
  exact h.closed_H x hxU' g hgH hS'

theorem exists_mem_normalizer_not_mem {S N : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hS : IsPGroup p S) (hNS : N ≤ S) (hne : ¬ S ≤ N) :
    ∃ g ∈ S, g ∉ N ∧ ∀ n ∈ N, g⁻¹ * n * g ∈ N ∧ g * n * g⁻¹ ∈ N := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥S)
  set W : Subgroup ↥S := N.subgroupOf S with hW
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply hne
    intro x hx
    have : (⟨x, hx⟩ : ↥S) ∈ W := by rw [htop]; trivial
    exact (Subgroup.mem_subgroupOf.mp this)
  have hlt : W < Subgroup.normalizer (W : Set ↥S) := hnc W (lt_top_iff_ne_top.mpr hWtop)
  obtain ⟨u, hun, huW⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp hlt).2
  refine ⟨(u : G), u.2, fun hmem => huW (Subgroup.mem_subgroupOf.mpr hmem), fun n hn => ?_⟩
  have hnS : n ∈ S := hNS hn
  have hnW : (⟨n, hnS⟩ : ↥S) ∈ W := Subgroup.mem_subgroupOf.mpr hn
  have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (W : Set ↥S)).inv_mem hun)
    ⟨n, hnS⟩).mp hnW
  have h2 := (Subgroup.mem_normalizer_iff.mp hun ⟨n, hnS⟩).mp hnW
  exact ⟨by simpa using Subgroup.mem_subgroupOf.mp h1, by simpa using Subgroup.mem_subgroupOf.mp h2⟩

theorem Hyp.S_le_stab (h : Hyp S A₁ A₂ H) : S ≤ stabSet (uSet A₁ A₂) := by
  by_contra hS
  have hne : ¬ S ≤ nU S A₁ A₂ := fun hSN => hS (fun s hs => (hSN hs).2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgS, hgN, hnorm⟩ := exists_mem_normalizer_not_mem h.pgroup nU_le_S hne
  have hconj : ∀ {A : Subgroup G}, A ≤ nU S A₁ A₂ →
      conjugate A g ≤ nU S A₁ A₂ ∧ conjugate A g⁻¹ ≤ nU S A₁ A₂ := by
    intro A hA
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have := hA (mem_conjugate_iff.1 hy)
      have := (hnorm _ this).1
      rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
    · have := hA (mem_conjugate_iff.1 hy)
      have := (hnorm _ this).2
      rwa [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group] at this
  obtain ⟨hA1g, hA1gi⟩ := hconj h.A₁_le_nU
  obtain ⟨hA2g, hA2gi⟩ := hconj h.A₂_le_nU
  have c1 := h.claim (X := A₁) (Or.inl le_rfl) h.four_le₁ hA1g
  have c2 := h.claim (X := A₂) (Or.inr le_rfl) h.four_le₂ hA2g
  have d1 := h.claim (X := A₁) (Or.inl le_rfl) h.four_le₁ hA1gi
  have d2 := h.claim (X := A₂) (Or.inr le_rfl) h.four_le₂ hA2gi
  apply hgN
  refine ⟨hgS, mem_stabSet_of_forall (fun x hx => ?_) (fun x hx => ?_)⟩
  · rcases hx with hx | hx
    · exact c1.2 x hx
    · exact c2.2 x hx
  · rcases hx with hx | hx
    · have := d1.2 x hx
      rwa [inv_inv] at this
    · have := d2.2 x hx
      rwa [inv_inv] at this

theorem Hyp.S_le_H (h : Hyp S A₁ A₂ H) : S ≤ H := by
  intro s hs
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.ne_bot₁
  have hxA : (x : G) ∈ A₁ := x.2
  have hx1 : (x : G) ≠ 1 := fun e => hx (Subtype.ext e)
  have hU := (h.S_le_stab hs (x : G)).1 (Or.inl hxA)
  rcases hU with hU | hU
  · exact h.mem_of_conj_mem (Or.inl rfl) (Or.inl rfl) hxA hx1 hU
  · exact h.mem_of_conj_mem (Or.inl rfl) (Or.inr rfl) hxA hx1 hU

end Claim

end CFSG.Asc75
