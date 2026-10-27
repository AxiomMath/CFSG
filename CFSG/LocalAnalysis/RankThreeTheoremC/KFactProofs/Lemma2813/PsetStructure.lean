module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Generation
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.FixPoints

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

section CT

variable {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]

theorem Pset_add_mem {w : M} {x y : V3} (hx : x ∈ Pset M w) (hy : y ∈ Pset M w) (hxy : x ≠ y) :
    x + y ∈ Pset M w := by
  rw [mem_Pset] at hx hy ⊢
  obtain ⟨hx0, hxw⟩ := hx
  obtain ⟨hy0, hyw⟩ := hy
  refine ⟨?_, ?_⟩
  · intro h
    apply hxy
    calc x = x + y + y := by rw [add_assoc, add_self_V3, add_zero]
      _ = 0 + y := by rw [h]
      _ = y := zero_add y
  · have hsup : w ∈ fixSub M (Spt x ⊔ Spt y) := by
      rw [fixSub_sup]
      exact ⟨hxw, hyw⟩
    exact fixSub_mono (Spt_add_le hx0 hy0 hxy) hsup

theorem eq_zero_of_three_mem_Pset (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) {w : M}
    {x y z : V3} (hx : x ∈ Pset M w) (hy : y ∈ Pset M w) (hz : z ∈ Pset M w) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (h : z ≠ x + y) : w = 0 := by
  rw [mem_Pset] at hx hy hz
  obtain ⟨hx0, hxw⟩ := hx
  obtain ⟨hy0, hyw⟩ := hy
  obtain ⟨hz0, hzw⟩ := hz
  apply hM0
  intro g
  have htop : w ∈ fixSub M (Spt x ⊔ Spt y ⊔ Spt z) := by
    rw [fixSub_sup, fixSub_sup]
    exact ⟨⟨hxw, hyw⟩, hzw⟩
  rw [Spt_sup_three hx0 hy0 hz0 hxy hxz hyz h] at htop
  exact htop g (Subgroup.mem_top g)

theorem Pset_card_cases (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) {w : M} (hw : w ≠ 0) :
    (Pset M w).card = 0 ∨ (Pset M w).card = 1 ∨
      ∃ x y : V3, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y ∧ Pset M w = {x, y, x + y} := by
  classical
  by_cases h01 : (Pset M w).card ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h01 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · right
    right
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (not_le.1 h01)
    have hxy' := Pset_add_mem hx hy hxy
    have hx0 := ((mem_Pset).1 hx).1
    have hy0 := ((mem_Pset).1 hy).1
    refine ⟨x, y, hx0, hy0, hxy, ?_⟩
    apply Finset.Subset.antisymm
    · intro z hz
      by_contra hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      obtain ⟨hzx, hzy, hzxy⟩ := hnot
      exact hw (eq_zero_of_three_mem_Pset hM0 hx hy hz hxy (Ne.symm hzx) (Ne.symm hzy) hzxy)
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hxy'

theorem pst_Ncnt_eq (k : ℕ) :
    Ncnt M k = Nat.card {w : M // w ≠ 0 ∧ (Pset M w).card = k} := by
  unfold Ncnt
  rfl

theorem Ncnt_total (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0) :
    Ncnt M 0 + Ncnt M 1 + Ncnt M 3 + 1 = Nat.card M := by
  classical
  haveI : Fintype M := Fintype.ofFinite M
  have key : ∀ k : ℕ, Ncnt M k =
      ∑ w : M, (if w ≠ 0 ∧ (Pset M w).card = k then 1 else 0) := by
    intro k
    rw [pst_Ncnt_eq, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have hpt : ∀ w : M, (1 : ℕ) = (if w = 0 then 1 else 0) +
      (if w ≠ 0 ∧ (Pset M w).card = 0 then 1 else 0) +
      (if w ≠ 0 ∧ (Pset M w).card = 1 then 1 else 0) +
      (if w ≠ 0 ∧ (Pset M w).card = 3 then 1 else 0) := by
    intro w
    by_cases hw : w = 0
    · simp [hw]
    · rcases Pset_card_cases hM0 hw with h | h | ⟨x, y, hx, hy, hxy, h⟩
      · simp [hw, h]
      · simp [hw, h]
      · have hx' : x ≠ x + y := by
          intro h'
          apply hy
          have h'' : x + 0 = x + y := by rw [add_zero]; exact h'
          exact (add_left_cancel h'').symm
        have hy' : y ≠ x + y := by
          intro h'
          apply hx
          have h'' : y + 0 = y + x := by rw [add_zero, add_comm y x]; exact h'
          exact (add_left_cancel h'').symm
        have hc : (Pset M w).card = 3 := Finset.card_eq_three.2 ⟨x, y, x + y, hxy, hx', hy', h⟩
        simp [hw, hc]
  have hsum : ∑ _w : M, (1 : ℕ) = ∑ w : M, ((if w = 0 then 1 else 0) +
      (if w ≠ 0 ∧ (Pset M w).card = 0 then 1 else 0) +
      (if w ≠ 0 ∧ (Pset M w).card = 1 then 1 else 0) +
      (if w ≠ 0 ∧ (Pset M w).card = 3 then 1 else 0)) :=
    Finset.sum_congr rfl (fun w _ => hpt w)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have h1 : (∑ w : M, (if w = 0 then 1 else 0 : ℕ)) = 1 := by simp
  have htot : Nat.card M = ∑ _w : M, (1 : ℕ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
  rw [key 0, key 1, key 3, htot, hsum, h1]
  ring

end CT

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
