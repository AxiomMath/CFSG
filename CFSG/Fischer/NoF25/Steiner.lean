module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.Fischer

theorem even_card_of_involution {α : Type*} [DecidableEq α] (s : Equiv.Perm α) (hs : s * s = 1)
    (X : Finset α) (hX : ∀ x ∈ X, s x ∈ X) (hfree : ∀ x ∈ X, s x ≠ x) : Even X.card := by
  have hss : ∀ x, s (s x) = x := fun x => by
    have := congrArg (fun t : Equiv.Perm α => t x) hs
    simpa using this
  have h := Finset.sum_involution (s := X) (f := fun _ => (1 : ZMod 2)) (fun x _ => s x)
    (fun _ _ => by decide) (fun x hx _ => hfree x hx) (fun x hx => hX x hx) (fun x _ => hss x)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact ZMod.natCast_eq_zero_iff_even.1 h

theorem fix_mem_of_steiner {α : Type*} [Fintype α] [DecidableEq α] (𝒮 : Finset (Finset α))
    (hcard : ∀ O ∈ 𝒮, O.card = 8) (hsteiner : ∀ Y : Finset α, Y.card = 5 → ∃! O, O ∈ 𝒮 ∧ Y ⊆ O)
    (s : Equiv.Perm α) (hs : s * s = 1) (hpres : ∀ O ∈ 𝒮, O.map s.toEmbedding ∈ 𝒮)
    (hfix : (Finset.univ.filter fun x => s x = x).card = 8) :
    (Finset.univ.filter fun x => s x = x) ∈ 𝒮 := by
  set F := Finset.univ.filter fun x => s x = x with hF
  have hmemF : ∀ x, x ∈ F ↔ s x = x := fun x => by simp [hF]
  have hss : ∀ x, s (s x) = x := fun x => by
    have := congrArg (fun t : Equiv.Perm α => t x) hs
    simpa using this
  by_contra hFS
  have key : ∀ O ∈ 𝒮, 5 ≤ (O ∩ F).card → (O ∩ F).card = 6 := by
    intro O hO h5
    obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq h5
    have hYO : Y ⊆ O := fun y hy => (Finset.mem_inter.1 (hYsub hy)).1
    have hYmap : Y ⊆ O.map s.toEmbedding := by
      intro y hy
      rw [Finset.mem_map]
      exact ⟨y, hYO hy, (hmemF y).1 (Finset.mem_inter.1 (hYsub hy)).2⟩
    obtain ⟨O', _, hu⟩ := hsteiner Y hYcard
    have hsO : O.map s.toEmbedding = O := by
      rw [hu _ ⟨hpres O hO, hYmap⟩, hu _ ⟨hO, hYO⟩]
    have hsmem : ∀ x ∈ O, s x ∈ O := fun x hx => by
      rw [← hsO]
      exact Finset.mem_map_of_mem _ hx
    have heven : Even (O \ F).card := by
      refine even_card_of_involution s hs (O \ F) (fun x hx => ?_) (fun x hx => ?_)
      · rw [Finset.mem_sdiff] at hx ⊢
        refine ⟨hsmem x hx.1, fun h => hx.2 ?_⟩
        rw [hmemF] at h ⊢
        rw [hss x] at h
        exact h.symm
      · rw [Finset.mem_sdiff, hmemF] at hx
        exact hx.2
    have hsum := Finset.card_sdiff_add_card_inter O F
    rw [hcard O hO] at hsum
    have hne8 : (O ∩ F).card ≠ 8 := by
      intro h8
      apply hFS
      have h1 : O ∩ F = O :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h8, hcard O hO])
      have h2 : O ∩ F = F :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h8, hfix])
      rw [← h2, h1]
      exact hO
    obtain ⟨m, hm⟩ := heven
    omega
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (Y O : Finset α) => Y ⊆ O) (s := F.powersetCard 5) (t := 𝒮)
  have hL : ∑ Y ∈ F.powersetCard 5,
      (Finset.bipartiteAbove (fun (Y O : Finset α) => Y ⊆ O) 𝒮 Y).card = 56 := by
    rw [Finset.sum_congr rfl (g := fun _ => 1)]
    · rw [Finset.sum_const, Finset.card_powersetCard, hfix]
      rfl
    · intro Y hY
      rw [Finset.mem_powersetCard] at hY
      obtain ⟨O, ⟨hO, hYO⟩, hu⟩ := hsteiner Y hY.2
      rw [Finset.card_eq_one]
      refine ⟨O, ?_⟩
      ext O'
      rw [Finset.mem_bipartiteAbove, Finset.mem_singleton]
      exact ⟨fun h => hu O' h, fun h => h ▸ ⟨hO, hYO⟩⟩
  have hR : 6 ∣ ∑ O ∈ 𝒮,
      (Finset.bipartiteBelow (fun (Y O : Finset α) => Y ⊆ O) (F.powersetCard 5) O).card := by
    apply Finset.dvd_sum
    intro O hO
    have e : Finset.bipartiteBelow (fun (Y O : Finset α) => Y ⊆ O) (F.powersetCard 5) O =
        (O ∩ F).powersetCard 5 := by
      ext Y
      rw [Finset.mem_bipartiteBelow, Finset.mem_powersetCard, Finset.mem_powersetCard,
        Finset.subset_inter_iff]
      tauto
    rw [e, Finset.card_powersetCard]
    by_cases h5 : 5 ≤ (O ∩ F).card
    · rw [key O hO h5]
      decide
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      exact dvd_zero 6
  rw [← hdc, hL] at hR
  exact absurd hR (by decide)

end CFSG.Fischer
