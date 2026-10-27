module

public import CFSG.LocalAnalysis.Asc75.Unique

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

theorem conjugate_bot (g : G) : conjugate (⊥ : Subgroup G) g = ⊥ := by
  ext y
  simp only [mem_conjugate_iff, Subgroup.mem_bot]
  constructor
  · intro hy
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this, hy]; group
  · intro hy
    rw [hy]; group

theorem conjugate_eq_bot_iff {Z : Subgroup G} {g : G} : conjugate Z g = ⊥ ↔ Z = ⊥ := by
  constructor
  · intro h
    have h2 := congrArg (fun W => conjugate W g⁻¹) h
    simpa only [conjugate_inv_conjugate, conjugate_bot] using h2
  · intro h
    rw [h, conjugate_bot]

theorem conjugate_closure (X : Set G) (g : G) :
    conjugate (Subgroup.closure X) g = Subgroup.closure {x : G | g * x * g⁻¹ ∈ X} := by
  apply le_antisymm
  · intro x hx
    have hx' : g * x * g⁻¹ ∈ Subgroup.closure X := mem_conjugate_iff.1 hx
    have key : ∀ y ∈ Subgroup.closure X, g⁻¹ * y * g ∈
        Subgroup.closure {x : G | g * x * g⁻¹ ∈ X} := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        refine Subgroup.subset_closure ?_
        show g * (g⁻¹ * y * g) * g⁻¹ ∈ X
        rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
      | one => simp
      | mul y z _ _ hy hz =>
        have : g⁻¹ * (y * z) * g = (g⁻¹ * y * g) * (g⁻¹ * z * g) := by group
        rw [this]; exact Subgroup.mul_mem _ hy hz
      | inv y _ hy =>
        have : g⁻¹ * y⁻¹ * g = (g⁻¹ * y * g)⁻¹ := by group
        rw [this]; exact Subgroup.inv_mem _ hy
    have := key _ hx'
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  · refine (Subgroup.closure_le _).2 ?_
    intro x hx
    exact mem_conjugate_iff.2 (Subgroup.subset_closure hx)

theorem conjugate_conjugate_inf_ne_bot_iff (X Y : Subgroup G) (g x : G) :
    conjugate (conjugate X g) x ⊓ conjugate Y g ≠ ⊥ ↔ conjugate X (g * x * g⁻¹) ⊓ Y ≠ ⊥ := by
  have e : conjugate (conjugate X g) x ⊓ conjugate Y g =
      conjugate (conjugate X (g * x * g⁻¹) ⊓ Y) g := by
    ext y
    simp only [Subgroup.mem_inf, mem_conjugate_iff]
    rw [show g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ by group]
  rw [e, Ne, Ne, conjugate_eq_bot_iff]

theorem genSet_conjugate (A₁ A₂ : Subgroup G) (g : G) :
    genSet (conjugate A₁ g) (conjugate A₂ g) = {x : G | g * x * g⁻¹ ∈ genSet A₁ A₂} := by
  ext x
  simp only [genSet, Set.mem_ofPred_eq]
  rw [conjugate_conjugate_inf_ne_bot_iff, conjugate_conjugate_inf_ne_bot_iff,
    conjugate_conjugate_inf_ne_bot_iff, conjugate_conjugate_inf_ne_bot_iff]

theorem mem_uSet_conjugate_iff {A₁ A₂ : Subgroup G} {g x : G} :
    x ∈ uSet (conjugate A₁ g) (conjugate A₂ g) ↔ g * x * g⁻¹ ∈ uSet A₁ A₂ := by
  simp only [uSet, Set.mem_union, SetLike.mem_coe, mem_conjugate_iff]

theorem mem_normalizer_conjugate_iff {X : Subgroup G} {g n : G} :
    n ∈ Subgroup.normalizer ((conjugate X g : Subgroup G) : Set G) ↔
      g * n * g⁻¹ ∈ Subgroup.normalizer (X : Set G) := by
  simp only [Subgroup.mem_normalizer_iff, mem_conjugate_iff]
  constructor
  · intro h x'
    have := h (g⁻¹ * x' * g)
    rwa [show g * (g⁻¹ * x' * g) * g⁻¹ = x' by group,
      show g * (n * (g⁻¹ * x' * g) * n⁻¹) * g⁻¹ = g * n * g⁻¹ * x' * (g * n * g⁻¹)⁻¹ by group] at this
  · intro h x
    have := h (g * x * g⁻¹)
    rwa [show g * n * g⁻¹ * (g * x * g⁻¹) * (g * n * g⁻¹)⁻¹ = g * (n * x * n⁻¹) * g⁻¹ by group]
      at this

section Conj

variable [Finite G] {S A₁ A₂ H : Subgroup G}

theorem pRank_conjugate_le (A : Subgroup G) (g : G) :
    CFSG.Open.pRank 2 (conjugate A g) ≤ CFSG.Open.pRank 2 A := by
  obtain ⟨E, hEA, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two (conjugate A g)
  refine CFSG.SectionRank.le_pRank one_lt_two (E := conjugate E g⁻¹) ?_ ?_ ?_
  · intro x hx
    have h1 := mem_conjugate_iff.1 hx
    have h2 := mem_conjugate_iff.1 (hEA h1)
    rwa [show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group] at h2
  · exact CFSG.SectionRank.isElemAbelian_map hE _
  · rw [card_conjugate, hcard]

theorem pRank_conjugate (A : Subgroup G) (g : G) :
    CFSG.Open.pRank 2 (conjugate A g) = CFSG.Open.pRank 2 A := by
  refine le_antisymm (pRank_conjugate_le A g) ?_
  have := pRank_conjugate_le (conjugate A g) g⁻¹
  rwa [conjugate_inv_conjugate] at this

theorem Hyp.conj (h : Hyp S A₁ A₂ H) (g : G) :
    Hyp (conjugate S g) (conjugate A₁ g) (conjugate A₂ g) (conjugate H g) where
  pgroup := isPGroup_conjugate h.pgroup g
  odd_index := by
    have : (conjugate S g).index = S.index := Subgroup.index_map_equiv S (MulAut.conj g⁻¹)
    rw [this]; exact h.odd_index
  le₁ := conjugate_mono h.le₁ g
  le₂ := conjugate_mono h.le₂ g
  comm := by
    intro a ha b hb
    have ha' : g * a * g⁻¹ ∈ A₁ := mem_conjugate_iff.1 ha
    have hb' : g * b * g⁻¹ ∈ A₂ := mem_conjugate_iff.1 hb
    have hc := h.comm _ ha' _ hb'
    calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [hc]
      _ = b * a := by group
  rank₁ := by rw [pRank_conjugate]; exact h.rank₁
  rank₂ := by rw [pRank_conjugate]; exact h.rank₂
  hdef := by rw [h.hdef, conjugate_closure, genSet_conjugate]
  closed_H := by
    intro a ha k hk hS
    rw [mem_uSet_conjugate_iff] at ha ⊢
    have hk' : g * k * g⁻¹ ∈ H := mem_conjugate_iff.1 hk
    have hS' : g * (k⁻¹ * a * k) * g⁻¹ ∈ S := mem_conjugate_iff.1 hS
    have e : (g * k * g⁻¹)⁻¹ * (g * a * g⁻¹) * (g * k * g⁻¹) = g * (k⁻¹ * a * k) * g⁻¹ := by group
    have := h.closed_H _ ha _ hk' (by rw [e]; exact hS')
    rwa [e] at this
  closed₁ := by
    intro a ha y hy
    rw [mem_uSet_conjugate_iff] at ha ⊢
    obtain ⟨hyS, hyN⟩ := hy
    have hS' : g * (y⁻¹ * a * y) * g⁻¹ ∈ S := mem_conjugate_iff.1 hyS
    have hN' := mem_normalizer_conjugate_iff.1 hyN
    have e : (g * y * g⁻¹)⁻¹ * (g * a * g⁻¹) * (g * y * g⁻¹) = g * (y⁻¹ * a * y) * g⁻¹ := by group
    have := h.closed₁ _ ha (g * y * g⁻¹) (by rw [e]; exact ⟨hS', hN'⟩)
    rwa [e] at this
  closed₂ := by
    intro a ha y hy
    rw [mem_uSet_conjugate_iff] at ha ⊢
    obtain ⟨hyS, hyN⟩ := hy
    have hS' : g * (y⁻¹ * a * y) * g⁻¹ ∈ S := mem_conjugate_iff.1 hyS
    have hN' := mem_normalizer_conjugate_iff.1 hyN
    have e : (g * y * g⁻¹)⁻¹ * (g * a * g⁻¹) * (g * y * g⁻¹) = g * (y⁻¹ * a * y) * g⁻¹ := by group
    have := h.closed₂ _ ha (g * y * g⁻¹) (by rw [e]; exact ⟨hS', hN'⟩)
    rwa [e] at this

end Conj

end CFSG.Asc75
