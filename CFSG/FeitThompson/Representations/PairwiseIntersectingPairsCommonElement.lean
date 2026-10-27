module

public import Mathlib.Data.Set.Card

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {α : Type*}

theorem exists_eq_pair_of_mem_of_ncard_eq_two {s : Set α} {a : α}
    (hs : s.ncard = 2) (ha : a ∈ s) : ∃ b, a ≠ b ∧ s = {a, b} := by
  obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.1 hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact ⟨y, hxy, rfl⟩
  · exact ⟨x, Ne.symm hxy, Set.pair_comm _ _⟩

theorem eq_or_eq_or_eq_of_ncard_inter_eq_one_of_triangle {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {v : Set α} (hv : v.ncard = 2)
    (h1 : (v ∩ {a, b}).ncard = 1) (h2 : (v ∩ {a, c}).ncard = 1) (h3 : (v ∩ {b, c}).ncard = 1) :
    v = {a, b} ∨ v = {a, c} ∨ v = {b, c} := by
  have hsub : v ⊆ {a, b, c} := by
    intro x hx
    obtain ⟨y, hxy, hv'⟩ := exists_eq_pair_of_mem_of_ncard_eq_two hv hx
    by_contra hxabc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxabc
    have key : ∀ p q : α, p ≠ x → q ≠ x → (v ∩ {p, q}).ncard = 1 → y ∈ ({p, q} : Set α) := by
      intro p q hp hq h
      obtain ⟨z, hz⟩ := Set.ncard_eq_one.1 h
      have hzmem : z ∈ v ∩ {p, q} := hz ▸ rfl
      have hz1 : z ∈ ({x, y} : Set α) := hv' ▸ hzmem.1
      have hz2 : z ∈ ({p, q} : Set α) := hzmem.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz1 hz2
      rcases hz1 with h' | h'
      · subst h'
        rcases hz2 with h'' | h''
        · exact absurd h''.symm hp
        · exact absurd h''.symm hq
      · subst h'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact hz2
    have hy1 := key a b (Ne.symm hxabc.1) (Ne.symm hxabc.2.1) h1
    have hy2 := key a c (Ne.symm hxabc.1) (Ne.symm hxabc.2.2) h2
    have hy3 := key b c (Ne.symm hxabc.2.1) (Ne.symm hxabc.2.2) h3
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy1 hy2 hy3
    rcases hy1 with rfl | rfl
    · rcases hy3 with h | h
      · exact hab h
      · exact hac h
    · rcases hy2 with h | h
      · exact hab h.symm
      · exact hbc h
  obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.1 hv
  have hx : x ∈ ({a, b, c} : Set α) := hsub (by simp)
  have hy : y ∈ ({a, b, c} : Set α) := hsub (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp_all [Set.pair_comm]

theorem ncard_iInter_eq_one_of_pairwise_ncard_inter_eq_one {n : ℕ} (hn : n = 2 ∨ 4 ≤ n)
    {S : Fin n → Set α} (hinj : Function.Injective S) (hcard : ∀ i, (S i).ncard = 2)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).ncard = 1) : (⋂ i, S i).ncard = 1 := by
  have hn2 : 2 ≤ n := by omega
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (hinter i0 i1 hi01)
  have hamem : a ∈ S i0 ∩ S i1 := ha ▸ rfl
  have hall : ∀ i, a ∈ S i := by
    intro i
    by_contra hai
    have hi0 : i ≠ i0 := by rintro rfl; exact hai hamem.1
    have hi1 : i ≠ i1 := by rintro rfl; exact hai hamem.2
    have h4 : 4 ≤ n := by
      rcases hn with h | h
      · exfalso
        have hi := i.isLt
        have e0 : i.val ≠ 0 := fun h' => hi0 (Fin.ext h')
        have e1 : i.val ≠ 1 := fun h' => hi1 (Fin.ext h')
        omega
      · exact h
    obtain ⟨b, hab, hS0⟩ := exists_eq_pair_of_mem_of_ncard_eq_two (hcard i0) hamem.1
    obtain ⟨c, hac, hS1⟩ := exists_eq_pair_of_mem_of_ncard_eq_two (hcard i1) hamem.2
    have hbc : b ≠ c := by
      rintro rfl
      have hb : b ∈ S i0 ∩ S i1 :=
        Set.mem_inter (by rw [hS0]; simp) (by rw [hS1]; simp)
      rw [ha] at hb
      simp only [Set.mem_singleton_iff] at hb
      exact hab hb.symm
    have hbi : b ∈ S i := by
      obtain ⟨z, hz⟩ := Set.ncard_eq_one.1 (hinter i i0 hi0)
      have hzm : z ∈ S i ∩ S i0 := hz ▸ rfl
      have hz2 : z ∈ S i0 := hzm.2
      rw [hS0] at hz2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz2
      rcases hz2 with rfl | rfl
      · exact absurd hzm.1 hai
      · exact hzm.1
    have hci : c ∈ S i := by
      obtain ⟨z, hz⟩ := Set.ncard_eq_one.1 (hinter i i1 hi1)
      have hzm : z ∈ S i ∩ S i1 := hz ▸ rfl
      have hz2 : z ∈ S i1 := hzm.2
      rw [hS1] at hz2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz2
      rcases hz2 with rfl | rfl
      · exact absurd hzm.1 hai
      · exact hzm.1
    have hSi : S i = {b, c} := by
      have hsub : ({b, c} : Set α) ⊆ S i := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        exacts [hbi, hci]
      exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard i, Set.ncard_pair hbc])
        (Set.finite_of_ncard_ne_zero (by rw [hcard i]; omega))).symm
    obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({i0, i1, i} : Finset (Fin n))) (t := Finset.univ) (by
        have h3 : ({i0, i1, i} : Finset (Fin n)).card ≤ 3 := by
          refine le_trans (Finset.card_insert_le _ _) ?_
          have := Finset.card_le_two (a := i1) (b := i)
          omega
        rw [Finset.card_univ, Fintype.card_fin]
        omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    obtain ⟨hl0, hl1, hli⟩ := hl
    have hcases := eq_or_eq_or_eq_of_ncard_inter_eq_one_of_triangle hab hac hbc (hcard l)
      (by rw [← hS0]; exact hinter l i0 hl0)
      (by rw [← hS1]; exact hinter l i1 hl1)
      (by rw [← hSi]; exact hinter l i hli)
    rcases hcases with h | h | h
    · exact hl0 (hinj (h.trans hS0.symm))
    · exact hl1 (hinj (h.trans hS1.symm))
    · exact hli (hinj (h.trans hSi.symm))
  have heq : (⋂ i, S i) = {a} := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [← ha]
      exact ⟨Set.mem_iInter.1 hx i0, Set.mem_iInter.1 hx i1⟩
    · simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact Set.mem_iInter.2 hall
  rw [heq, Set.ncard_singleton]

theorem ncard_biInter_eq_one_of_pairwise_ncard_inter_eq_one {𝒜 : Finset (Set α)}
    (hn : 𝒜.card = 2 ∨ 4 ≤ 𝒜.card) (hcard : ∀ s ∈ 𝒜, s.ncard = 2)
    (hinter : ∀ s ∈ 𝒜, ∀ t ∈ 𝒜, s ≠ t → (s ∩ t).ncard = 1) :
    (⋂ s ∈ 𝒜, s).ncard = 1 := by
  classical
  set S : Fin 𝒜.card → Set α := fun i => ((𝒜.equivFin.symm i : {x // x ∈ 𝒜}) : Set α) with hS
  have hinjS : Function.Injective S := fun i j hij =>
    𝒜.equivFin.symm.injective (Subtype.ext hij)
  have hiInter : (⋂ i, S i) = ⋂ s ∈ 𝒜, s := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · simp only [Set.mem_iInter] at hx ⊢
      intro s hs
      simpa [hS] using hx (𝒜.equivFin ⟨s, hs⟩)
    · simp only [Set.mem_iInter] at hx ⊢
      intro i
      exact hx _ (𝒜.equivFin.symm i).2
  rw [← hiInter]
  exact ncard_iInter_eq_one_of_pairwise_ncard_inter_eq_one hn hinjS
    (fun i => hcard _ (𝒜.equivFin.symm i).2)
    (fun i j hij => hinter _ (𝒜.equivFin.symm i).2 _ (𝒜.equivFin.symm j).2
      (fun h => hij (hinjS h)))

end

end CFSG.FeitThompson
