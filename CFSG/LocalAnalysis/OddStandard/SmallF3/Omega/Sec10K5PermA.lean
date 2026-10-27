module

public import Mathlib.GroupTheory.Perm.Finite

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

open Equiv Equiv.Perm

abbrev scHom : Perm (Fin 4) × Perm (Fin 4) →* Perm (Fin 4 ⊕ Fin 4) :=
  Perm.sumCongrHom (Fin 4) (Fin 4)

abbrev blockPart (Φ : Subgroup (Perm (Fin 4 ⊕ Fin 4))) : Subgroup (Perm (Fin 4 ⊕ Fin 4)) :=
  Φ ⊓ scHom.range

abbrev blockPre (Φ : Subgroup (Perm (Fin 4 ⊕ Fin 4))) :
    Subgroup (Perm (Fin 4) × Perm (Fin 4)) :=
  Subgroup.comap scHom Φ

abbrev proj1 (Φ : Subgroup (Perm (Fin 4 ⊕ Fin 4))) : Subgroup (Perm (Fin 4)) :=
  (blockPre Φ).map (MonoidHom.fst (Perm (Fin 4)) (Perm (Fin 4)))

abbrev proj2 (Φ : Subgroup (Perm (Fin 4 ⊕ Fin 4))) : Subgroup (Perm (Fin 4)) :=
  (blockPre Φ).map (MonoidHom.snd (Perm (Fin 4)) (Perm (Fin 4)))

theorem eq_inl_of_isLeft_true {x : Fin 4 ⊕ Fin 4} (h : x.isLeft = true) :
    ∃ i, x = Sum.inl i := by
  cases x with
  | inl i => exact ⟨i, rfl⟩
  | inr j => simp at h

theorem eq_inr_of_isLeft_false {x : Fin 4 ⊕ Fin 4} (h : x.isLeft = false) :
    ∃ j, x = Sum.inr j := by
  cases x with
  | inl i => simp at h
  | inr j => exact ⟨j, rfl⟩

theorem eq_inr_of_not_mem {x : Fin 4 ⊕ Fin 4}
    (h : x ∉ Set.range (Sum.inl : Fin 4 → Fin 4 ⊕ Fin 4)) : ∃ j, x = Sum.inr j := by
  cases x with
  | inl i => exact absurd ⟨i, rfl⟩ h
  | inr j => exact ⟨j, rfl⟩

theorem isLeft_of_isLeft_inl_false {σ : Perm (Fin 4 ⊕ Fin 4)}
    (h : ∀ i, (σ (Sum.inl i)).isLeft = false) :
    ∀ j, (σ (Sum.inr j)).isLeft = true := by
  intro j
  have hR : (Finset.univ.image (fun i : Fin 4 => σ (Sum.inl i))).card = 4 := by
    rw [Finset.card_image_of_injective (f := fun i : Fin 4 => σ (Sum.inl i))
      (Finset.univ : Finset (Fin 4)) (σ.injective.comp Sum.inl_injective)]
    decide +kernel
  have hL : (Finset.univ.filter (fun x : Fin 4 ⊕ Fin 4 => x.isLeft = false)).card = 4 := by
    decide +kernel
  have hsub : Finset.univ.image (fun i : Fin 4 => σ (Sum.inl i)) ⊆
      Finset.univ.filter (fun x : Fin 4 ⊕ Fin 4 => x.isLeft = false) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h i⟩
  have heq : Finset.univ.image (fun i : Fin 4 => σ (Sum.inl i)) =
      Finset.univ.filter (fun x : Fin 4 ⊕ Fin 4 => x.isLeft = false) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hL, hR])
  cases hv : (σ (Sum.inr j)).isLeft with
  | false =>
      exfalso
      have hmem : σ (Sum.inr j) ∈ Finset.univ.image (fun i : Fin 4 => σ (Sum.inl i)) := by
        rw [heq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
      exact Sum.inl_ne_inr (σ.injective hi)
  | true => rfl

theorem mul_mem_range {w u : Perm (Fin 4 ⊕ Fin 4)}
    (hw : ∀ i, (w (Sum.inl i)).isLeft = false)
    (hu : ∀ j, (u (Sum.inr j)).isLeft = true) :
    u * w ∈ scHom.range := by
  apply Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := eq_inr_of_isLeft_false (hw i)
  obtain ⟨k, hk⟩ := eq_inl_of_isLeft_true (hu j)
  exact ⟨k, by rw [Equiv.Perm.mul_apply, hj, hk]⟩

end CFSG.OddStandard.SmallF3.Omega.K5
