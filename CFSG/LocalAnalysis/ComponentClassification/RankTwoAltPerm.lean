module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltDefs

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

@[expose] def kOf : Fin 4 → Perm (Fin 4) :=
  ![1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3)]

theorem kOf_apply_zero : ∀ i : Fin 4, kOf i 0 = i := by decide

theorem kOf_apply_comm : ∀ i j : Fin 4, kOf i j = kOf j i := by decide

theorem kOf_mem : ∀ i : Fin 4, kOf i ∈ kleinFour := by
  have h1 : (swap 0 1 * swap 2 3 : Perm (Fin 4)) ∈ kleinFour := subset_closure (Set.mem_insert _ _)
  have h2 : (swap 0 2 * swap 1 3 : Perm (Fin 4)) ∈ kleinFour :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  intro i
  fin_cases i
  · exact one_mem _
  · exact h1
  · exact h2
  · exact mul_mem h1 h2

theorem swap_mem_kleinFour_one : (swap 0 1 * swap 2 3 : Perm (Fin 4)) ∈ kleinFour :=
  subset_closure (Set.mem_insert _ _)

theorem swap_mem_kleinFour_two : (swap 0 2 * swap 1 3 : Perm (Fin 4)) ∈ kleinFour :=
  subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def fixCycle : Fin 4 → Perm (Fin 4) :=
  ![swap 1 2 * swap 2 3, swap 0 2 * swap 2 3, swap 0 1 * swap 1 3, swap 0 1 * swap 1 2]

@[expose] def moveCycle : Fin 4 → Perm (Fin 4) :=
  ![swap 0 1 * swap 1 2, swap 0 1 * swap 1 2, swap 0 1 * swap 1 2, swap 1 2 * swap 2 3]

theorem fixCycle_mem : ∀ i, fixCycle i ∈ alternatingGroup (Fin 4) := by
  intro i
  rw [mem_alternatingGroup]
  revert i
  decide

theorem moveCycle_mem : ∀ i, moveCycle i ∈ alternatingGroup (Fin 4) := by
  intro i
  rw [mem_alternatingGroup]
  revert i
  decide

theorem fixCycle_apply_eq : ∀ i j : Fin 4, fixCycle i j = j → j = i := by decide

theorem fixCycle_apply_self : ∀ i : Fin 4, fixCycle i i = i := by decide

theorem moveCycle_apply_ne : ∀ i : Fin 4, moveCycle i i ≠ i := by decide

theorem conj_mem_kleinFour (g : Perm (Fin 4)) {k : Perm (Fin 4)} (hk : k ∈ kleinFour) :
    g * k * g⁻¹ ∈ kleinFour := by
  have hle : kleinFour.map (MulAut.conj g).toMonoidHom ≤ kleinFour := by
    rw [kleinFour, MonoidHom.map_closure, closure_le]
    have hgen : ∀ x ∈ ({swap 0 1 * swap 2 3, swap 0 2 * swap 1 3} : Set (Perm (Fin 4))),
        ∃ i, g * x * g⁻¹ = kOf i := by
      have h : ∀ g : Perm (Fin 4), (∃ i, g * (swap 0 1 * swap 2 3) * g⁻¹ = kOf i) ∧
          ∃ i, g * (swap 0 2 * swap 1 3) * g⁻¹ = kOf i := by decide
      rintro x (rfl | rfl)
      · exact (h g).1
      · exact (h g).2
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := hgen x hx
    change g * x * g⁻¹ ∈ kleinFour
    rw [hi]
    exact kOf_mem i
  exact hle ⟨k, hk, rfl⟩

variable {α : Type*} [DecidableEq α] (ι : Fin 4 ↪ α)

omit [DecidableEq α] in
theorem apply_apply_of_commute {φ ψ : Perm α} (h : Commute φ ψ) (x : α) :
    φ (ψ x) = ψ (φ x) := by
  rw [← Perm.mul_apply, h.eq, Perm.mul_apply]

theorem exists_kleinFour_of_commute {φ : Perm α}
    (h1 : Commute φ (viaEmbeddingHom ι (swap 0 1 * swap 2 3)))
    (h2 : Commute φ (viaEmbeddingHom ι (swap 0 2 * swap 1 3))) :
    ∃ k ∈ kleinFour, ∀ i, φ (ι i) = ι (k i) := by
  have hc : ∀ i, Commute φ (viaEmbeddingHom ι (kOf i)) := by
    intro i
    fin_cases i
    · change Commute φ (viaEmbeddingHom ι 1)
      rw [map_one]
      exact Commute.one_right φ
    · exact h1
    · exact h2
    · change Commute φ (viaEmbeddingHom ι (swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3)))
      rw [map_mul]
      exact h1.mul_right h2
  have hrange : φ (ι 0) ∈ Set.range ι := by
    by_contra hn
    have e := apply_apply_of_commute h1 (ι 0)
    rw [viaEmbeddingHom_apply_image, viaEmbeddingHom_apply_of_notMem ι _ hn,
      show (swap 0 1 * swap 2 3 : Perm (Fin 4)) 0 = 1 by decide] at e
    exact absurd (ι.injective (φ.injective e)) (by decide)
  obtain ⟨j, hj⟩ := hrange
  refine ⟨kOf j, kOf_mem j, fun i => ?_⟩
  have e := apply_apply_of_commute (hc i) (ι 0)
  rw [viaEmbeddingHom_apply_image, kOf_apply_zero, ← hj, viaEmbeddingHom_apply_image] at e
  rw [e, kOf_apply_comm]

theorem apply_eq_of_commute_alternating {φ : Perm α}
    (hφ : ∀ k ∈ alternatingGroup (Fin 4), Commute φ (viaEmbeddingHom ι k)) (i : Fin 4) :
    φ (ι i) = ι i := by
  have hrange : φ (ι i) ∈ Set.range ι := by
    by_contra hn
    have e := apply_apply_of_commute (hφ _ (moveCycle_mem i)) (ι i)
    rw [viaEmbeddingHom_apply_image, viaEmbeddingHom_apply_of_notMem ι _ hn] at e
    exact moveCycle_apply_ne i (ι.injective (φ.injective e))
  obtain ⟨j, hj⟩ := hrange
  have e := apply_apply_of_commute (hφ _ (fixCycle_mem i)) (ι i)
  rw [viaEmbeddingHom_apply_image, fixCycle_apply_self, ← hj, viaEmbeddingHom_apply_image] at e
  rw [← hj, fixCycle_apply_eq i j (ι.injective e.symm)]

theorem commute_of_apply_eq {φ : Perm α} (hφ : ∀ i, φ (ι i) = ι i) (k : Perm (Fin 4)) :
    Commute φ (viaEmbeddingHom ι k) := by
  apply Equiv.ext
  intro x
  simp only [Perm.mul_apply]
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    rw [viaEmbeddingHom_apply_image, hφ, hφ, viaEmbeddingHom_apply_image]
  · have hφx : φ x ∉ Set.range ι := by
      rintro ⟨i, hi⟩
      apply hx
      refine ⟨i, φ.injective ?_⟩
      rw [hφ, hi]
    rw [viaEmbeddingHom_apply_of_notMem ι _ hx, viaEmbeddingHom_apply_of_notMem ι _ hφx]

theorem exists_two_not_mem [Fintype α] (hα : 7 ≤ Fintype.card α) (x : α) :
    ∃ s s' : α, s ∉ Set.range ι ∧ s' ∉ Set.range ι ∧ s ≠ x ∧ s' ≠ x ∧ s ≠ s' := by
  classical
  have hcard : 1 < (Finset.univ \ insert x (Finset.univ.map ι)).card := by
    have h1 : (insert x (Finset.univ.map ι)).card ≤ 5 := by
      calc (insert x (Finset.univ.map ι)).card ≤ (Finset.univ.map ι).card + 1 :=
            Finset.card_insert_le _ _
        _ = 5 := by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  obtain ⟨s, hs, s', hs', hss⟩ := Finset.one_lt_card.mp hcard
  have hout : ∀ y ∈ Finset.univ \ insert x (Finset.univ.map ι), y ∉ Set.range ι ∧ y ≠ x := by
    intro y hy
    rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hy
    refine ⟨?_, hy.2.1⟩
    rintro ⟨i, rfl⟩
    exact hy.2.2 (Finset.mem_map_of_mem _ (Finset.mem_univ i))
  exact ⟨s, s', (hout s hs).1, (hout s' hs').1, (hout s hs).2, (hout s' hs').2, hss⟩

theorem eq_one_of_commute_stab [Fintype α] (hα : 7 ≤ Fintype.card α) {φ : Perm α}
    (hA : ∀ k ∈ alternatingGroup (Fin 4), Commute φ (viaEmbeddingHom ι k))
    (hd : ∀ r s : α, r ∉ Set.range ι → s ∉ Set.range ι → r ≠ s →
      Commute φ (swap (ι 0) (ι 1) * swap r s)) : φ = 1 := by
  apply Equiv.ext
  intro x
  rw [Perm.one_apply]
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨i, rfl⟩ := hx
    exact apply_eq_of_commute_alternating ι hA i
  · have hφx : φ x ∉ Set.range ι := by
      rintro ⟨i, hi⟩
      apply hx
      refine ⟨i, φ.injective ?_⟩
      rw [apply_eq_of_commute_alternating ι hA i, hi]
    have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
    have key : ∀ t : α, t ∉ Set.range ι → t ≠ x → φ x = x ∨ φ x = t := by
      intro t ht htx
      by_contra hcon
      push Not at hcon
      have e := apply_apply_of_commute (hd x t hx ht htx.symm) x
      have hd1 : (swap (ι 0) (ι 1) * swap x t) x = t := by
        rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne
          (fun h => ht ⟨0, h.symm⟩) (fun h => ht ⟨1, h.symm⟩)]
      have hd2 : (swap (ι 0) (ι 1) * swap x t) (φ x) = φ x := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hcon.1 hcon.2, swap_apply_of_ne_of_ne
          (fun h => hφx ⟨0, h.symm⟩) (fun h => hφx ⟨1, h.symm⟩)]
      rw [hd1, hd2] at e
      exact htx (φ.injective e)
    obtain ⟨s, s', hs, hs', hsx, hs'x, hss⟩ := exists_two_not_mem ι hα x
    rcases key s hs hsx with h | h
    · exact h
    · rcases key s' hs' hs'x with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hss

theorem exists_perm_comp_eq [Fintype α] (ι' : Fin 4 ↪ α) :
    ∃ σ : Perm α, ∀ i, σ (ι i) = ι' i := by
  classical
  have : Finite {x | x ∈ Set.range ι} := (inferInstance : Finite (Set.range ι))
  let e : {x // x ∈ Set.range ι} ≃ {x // x ∈ Set.range ι'} :=
    (Equiv.ofInjective ι ι.injective).symm.trans (Equiv.ofInjective ι' ι'.injective)
  refine ⟨Equiv.extendSubtype e, fun i => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (ι i) ⟨i, rfl⟩]
  change ((Equiv.ofInjective ι' ι'.injective) ((Equiv.ofInjective ι ι.injective).symm
    ⟨ι i, ⟨i, rfl⟩⟩) : α) = ι' i
  rw [show (Equiv.ofInjective ι ι.injective).symm ⟨ι i, ⟨i, rfl⟩⟩ = i from
    (Equiv.ofInjective ι ι.injective).symm_apply_apply i]
  rfl

theorem conj_viaEmbeddingHom_of_comp {ι' : Fin 4 ↪ α} {σ : Perm α} (hσ : ∀ i, σ (ι i) = ι' i)
    (k : Perm (Fin 4)) : σ * viaEmbeddingHom ι k * σ⁻¹ = viaEmbeddingHom ι' k := by
  have hinv : ∀ i, σ⁻¹ (ι' i) = ι i := fun i => by rw [Perm.inv_eq_iff_eq, hσ]
  apply Equiv.ext
  intro x
  simp only [Perm.mul_apply]
  by_cases hx : x ∈ Set.range ι'
  · obtain ⟨i, rfl⟩ := hx
    rw [hinv, viaEmbeddingHom_apply_image, hσ, viaEmbeddingHom_apply_image]
  · have hx' : σ⁻¹ x ∉ Set.range ι := by
      rintro ⟨i, hi⟩
      apply hx
      refine ⟨i, ?_⟩
      rw [← hσ, hi, perm_apply_inv]
    rw [viaEmbeddingHom_apply_of_notMem ι _ hx', perm_apply_inv,
      viaEmbeddingHom_apply_of_notMem ι' _ hx]

end CFSG.ComponentClassification.RankTwoAlt
