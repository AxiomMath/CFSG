module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.Timmesfeld75

section CommHom

variable {G : Type*} [Group G]

@[expose] def normCommHom (N : Subgroup G) (w : G) (hN : ∀ m ∈ N, ∀ m' ∈ N, m * m' = m' * m)
    (hw : ∀ m ∈ N, w * m * w⁻¹ ∈ N) : ↥N →* ↥N where
  toFun m := ⟨w * m * w⁻¹ * m⁻¹, N.mul_mem (hw m m.2) (N.inv_mem m.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' m m' := by
    apply Subtype.ext
    have hb : (w * (m' : G) * w⁻¹) * (m' : G)⁻¹ ∈ N :=
      N.mul_mem (hw m' m'.2) (N.inv_mem m'.2)
    have hc := hN ((m : G)⁻¹) (N.inv_mem m.2) _ hb
    have e1 : w * ((m : G) * m') * w⁻¹ = (w * m * w⁻¹) * (w * m' * w⁻¹) := by group
    show w * ((m : G) * m') * w⁻¹ * ((m : G) * m')⁻¹ =
      (w * m * w⁻¹ * (m : G)⁻¹) * (w * m' * w⁻¹ * (m' : G)⁻¹)
    calc w * ((m : G) * m') * w⁻¹ * ((m : G) * m')⁻¹
        = (w * m * w⁻¹) * (((w * m' * w⁻¹) * (m' : G)⁻¹) * (m : G)⁻¹) := by
          rw [e1]
          group
      _ = (w * m * w⁻¹) * ((m : G)⁻¹ * ((w * m' * w⁻¹) * (m' : G)⁻¹)) := by rw [hc]
      _ = _ := by group

end CommHom

section Counting

open Classical in
theorem card_ge_of_pairwise_inf_eq_bot {I : Type*} [Group I] [Finite I] {ι : Type*}
    (J : Subgroup I) (s : Finset ι) (S : ι → Subgroup I) (hSJ : ∀ i ∈ s, S i ≤ J)
    (hS : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → S i ⊓ S j = ⊥) {c : ℕ}
    (hc : ∀ i ∈ s, Nat.card (S i) = c) : s.card * (c - 1) + 1 ≤ Nat.card J := by
  have := Fintype.ofFinite I
  let t : ι → Finset I := fun i => (Set.toFinset (S i : Set I)).erase 1
  have hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (t i) (t j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hx1 : x ≠ 1 := (Finset.mem_erase.1 hxi).1
    have hxS : x ∈ S i ⊓ S j := ⟨by simpa [t] using (Finset.mem_erase.1 hxi).2,
      by simpa [t] using (Finset.mem_erase.1 hxj).2⟩
    rw [hS i hi j hj hij, Subgroup.mem_bot] at hxS
    exact hx1 hxS
  have hcard : ∀ i ∈ s, (t i).card = c - 1 := by
    intro i hi
    have h1 : (Set.toFinset (S i : Set I)).card = c := by
      rw [← hc i hi, Set.toFinset_card, Nat.card_eq_fintype_card]
      rfl
    rw [Finset.card_erase_of_mem (by simp), h1]
  have hbi : (s.biUnion t).card = s.card * (c - 1) := by
    rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hcard]
  have hsub : s.biUnion t ⊆ (Set.toFinset (J : Set I)).erase 1 := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
    refine Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hxi).1, ?_⟩
    simpa using hSJ i hi (by simpa [t] using (Finset.mem_erase.1 hxi).2)
  have h2 := Finset.card_le_card hsub
  have hJ : (Set.toFinset (J : Set I)).card = Nat.card J := by
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]
    rfl
  rw [hbi, Finset.card_erase_of_mem (by simp), hJ] at h2
  have h3 : 0 < Nat.card J := Nat.card_pos
  omega

end Counting

end CFSG.CGT.Timmesfeld75
