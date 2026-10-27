module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.FrameD0

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

private theorem perm_eq_or_eq_of_comm_swap {p q : Fin 10} (hpq : p ≠ q)
    {π : Perm (Fin 10)} (h : π * swap p q = swap p q * π) : π p = p ∨ π p = q := by
  have h' : swap (π p) (π q) = swap p q := by
    rw [mul_swap_eq_swap_mul] at h
    exact mul_right_cancel h
  have h1 : π q = swap p q (π p) := by
    have := congrArg (fun f : Perm (Fin 10) => f (π p)) h'
    simpa [Equiv.swap_apply_left] using this
  by_cases hx : π p = p
  · exact Or.inl hx
  · right
    by_contra hy
    have hfix : swap p q (π p) = π p := Equiv.swap_apply_of_ne_of_ne hx hy
    rw [hfix] at h1
    exact hpq ((π.injective h1).symm)

private theorem perm_eq_of_comm_swaps {p q r : Fin 10} (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) {π : Perm (Fin 10)} (hq : π * swap p q = swap p q * π)
    (hr : π * swap p r = swap p r * π) : π p = p := by
  rcases perm_eq_or_eq_of_comm_swap hpq hq with h | h
  · exact h
  · rcases perm_eq_or_eq_of_comm_swap hpr hr with h' | h'
    · exact (Ne.symm hpq (h.symm.trans h')).elim
    · exact (hqr (h.symm.trans h')).elim

private theorem cycleType_swap_eight (a b : Fin 8) (h : a ≠ b) :
    (swap a b : Perm (Fin 8)).cycleType = {2} :=
  isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr h)

private theorem cycleType_target2 :
    (swap (0 : Fin 8) 1 * swap 2 3 : Perm (Fin 8)).cycleType = Multiset.replicate 2 2 := by
  have hd : Disjoint (swap (0 : Fin 8) 1) (swap 2 3 : Perm (Fin 8)) :=
    disjoint_swap_swap (by decide : [(0 : Fin 8), 1, 2, 3].Nodup)
  rw [hd.cycleType_mul, cycleType_swap_eight 0 1 (by decide),
    cycleType_swap_eight 2 3 (by decide)]
  decide

private theorem cycleType_target3 :
    (swap (0 : Fin 8) 1 * (swap 2 3 * swap 4 5) : Perm (Fin 8)).cycleType =
      Multiset.replicate 3 2 := by
  have hd : Disjoint (swap (0 : Fin 8) 1) ((swap 2 3 * swap 4 5) : Perm (Fin 8)) :=
    (disjoint_swap_swap (by decide : [(0 : Fin 8), 1, 2, 3].Nodup)).mul_right
      (disjoint_swap_swap (by decide : [(0 : Fin 8), 1, 4, 5].Nodup))
  have hd2 : Disjoint (swap (2 : Fin 8) 3) (swap 4 5 : Perm (Fin 8)) :=
    disjoint_swap_swap (by decide : [(2 : Fin 8), 3, 4, 5].Nodup)
  rw [hd.cycleType_mul, cycleType_swap_eight 0 1 (by decide), hd2.cycleType_mul,
    cycleType_swap_eight 2 3 (by decide), cycleType_swap_eight 4 5 (by decide)]
  decide

private theorem cycleType_target4 :
    (swap (0 : Fin 8) 1 * ((swap 2 3 * swap 4 5) * swap 6 7) : Perm (Fin 8)).cycleType =
      Multiset.replicate 4 2 := by
  have hd : Disjoint (swap (0 : Fin 8) 1) (((swap 2 3 * swap 4 5) * swap 6 7) : Perm (Fin 8)) :=
    ((disjoint_swap_swap (by decide : [(0 : Fin 8), 1, 2, 3].Nodup)).mul_right
      (disjoint_swap_swap (by decide : [(0 : Fin 8), 1, 4, 5].Nodup))).mul_right
      (disjoint_swap_swap (by decide : [(0 : Fin 8), 1, 6, 7].Nodup))
  have hd2 : Disjoint ((swap (2 : Fin 8) 3 * swap 4 5)) (swap 6 7 : Perm (Fin 8)) :=
    (disjoint_swap_swap (by decide : [(2 : Fin 8), 3, 6, 7].Nodup)).mul_left
      (disjoint_swap_swap (by decide : [(4 : Fin 8), 5, 6, 7].Nodup))
  have hd3 : Disjoint (swap (2 : Fin 8) 3) (swap 4 5 : Perm (Fin 8)) :=
    disjoint_swap_swap (by decide : [(2 : Fin 8), 3, 4, 5].Nodup)
  rw [hd.cycleType_mul, cycleType_swap_eight 0 1 (by decide), hd2.cycleType_mul,
    hd3.cycleType_mul, cycleType_swap_eight 2 3 (by decide), cycleType_swap_eight 4 5 (by decide),
    cycleType_swap_eight 6 7 (by decide)]
  decide

private theorem exists_conj_of_cycleType {ρ target : Perm (Fin 8)}
    (h : ρ.cycleType = target.cycleType) : ∃ s : Perm (Fin 8), s * ρ * s⁻¹ = target :=
  isConj_iff.mp (isConj_iff_cycleType_eq.mpr h)

theorem eq_cD₀_or_of_commutes (π : Perm (Fin 10)) (hπ : π * π = 1)
    (hc : ∀ ρ : Perm (Fin 8), ρ 0 = 0 → ρ 1 = 1 → π * liftS8 ρ = liftS8 ρ * π)
    (h89 : π * τ₀ * π⁻¹ = swap 0 1) (h01 : π * swap 0 1 * π⁻¹ = τ₀) :
    π = cD₀ ∨ π = swap 0 9 * swap 1 8 := by
  have h23 : π * swap 2 3 = swap 2 3 * π := by
    have h := hc (swap (2 : Fin 8) 3) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h24 : π * swap 2 4 = swap 2 4 * π := by
    have h := hc (swap (2 : Fin 8) 4) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h34 : π * swap 3 4 = swap 3 4 * π := by
    have h := hc (swap (3 : Fin 8) 4) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h35 : π * swap 3 5 = swap 3 5 * π := by
    have h := hc (swap (3 : Fin 8) 5) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h45 : π * swap 4 5 = swap 4 5 * π := by
    have h := hc (swap (4 : Fin 8) 5) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h46 : π * swap 4 6 = swap 4 6 * π := by
    have h := hc (swap (4 : Fin 8) 6) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h56 : π * swap 5 6 = swap 5 6 * π := by
    have h := hc (swap (5 : Fin 8) 6) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h57 : π * swap 5 7 = swap 5 7 * π := by
    have h := hc (swap (5 : Fin 8) 7) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h67 : π * swap 6 7 = swap 6 7 * π := by
    have h := hc (swap (6 : Fin 8) 7) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h62 : π * swap 6 2 = swap 6 2 * π := by
    have h := hc (swap (6 : Fin 8) 2) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h72 : π * swap 7 2 = swap 7 2 * π := by
    have h := hc (swap (7 : Fin 8) 2) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h73 : π * swap 7 3 = swap 7 3 * π := by
    have h := hc (swap (7 : Fin 8) 3) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have hp2 : π 2 = 2 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h23 h24
  have hp3 : π 3 = 3 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h34 h35
  have hp4 : π 4 = 4 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h45 h46
  have hp5 : π 5 = 5 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h56 h57
  have hp6 : π 6 = 6 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h67 h62
  have hp7 : π 7 = 7 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h72 h73
  have h9 : π 9 = swap 0 1 (π 8) := by
    have := congrArg (fun f : Perm (Fin 10) => f (π 8)) h89
    simpa [Equiv.Perm.mul_apply, τ₀] using this
  have h8 : π 8 = swap 0 1 (π 9) := by
    have := congrArg (fun f : Perm (Fin 10) => f (π 9)) h89
    simpa [Equiv.Perm.mul_apply, τ₀] using this
  have h1 : π 1 = τ₀ (π 0) := by
    have := congrArg (fun f : Perm (Fin 10) => f (π 0)) h01
    simpa [Equiv.Perm.mul_apply] using this
  have h0 : π 0 = τ₀ (π 1) := by
    have := congrArg (fun f : Perm (Fin 10) => f (π 1)) h01
    simpa [Equiv.Perm.mul_apply] using this
  have hsq8 : π (π 8) = 8 := by
    have := congrArg (fun f : Perm (Fin 10) => f 8) hπ
    simpa [Equiv.Perm.mul_apply] using this
  have h8mem : π 8 = 0 ∨ π 8 = 1 := by
    by_cases h0' : π 8 = 0
    · exact Or.inl h0'
    by_cases h1' : π 8 = 1
    · exact Or.inr h1'
    · exfalso
      have hfix : swap 0 1 (π 8) = π 8 := Equiv.swap_apply_of_ne_of_ne h0' h1'
      rw [hfix] at h9
      exact (by decide : (9 : Fin 10) ≠ 8) (π.injective h9)
  rcases h8mem with h8c | h8c
  · have hπ0 : π 0 = 8 := by rw [← h8c]; exact hsq8
    have hπ1 : π 1 = 9 := by rw [h1, hπ0]; decide
    have hπ9 : π 9 = 1 := by rw [h9, h8c]; decide
    left
    refine Equiv.ext fun x => ?_
    fin_cases x <;>
      simp [cD₀, Equiv.Perm.mul_apply, hp2, hp3, hp4, hp5, hp6, hp7, h8c, hπ0, hπ1,
        hπ9] <;>
      decide
  · have hπ1 : π 1 = 8 := by rw [← h8c]; exact hsq8
    have hπ0 : π 0 = 9 := by rw [h0, hπ1]; decide
    have hπ9 : π 9 = 0 := by rw [h9, h8c]; decide
    right
    refine Equiv.ext fun x => ?_
    fin_cases x <;>
      simp [Equiv.Perm.mul_apply, hp2, hp3, hp4, hp5, hp6, hp7, h8c, hπ0, hπ1, hπ9] <;>
      decide

theorem eq_cD₁_or_of_commutes (π : Perm (Fin 10)) (hπ : π * π = 1)
    (hc : ∀ ρ : Perm (Fin 8), ρ 2 = 2 → ρ 3 = 3 → π * liftS8 ρ = liftS8 ρ * π)
    (h89 : π * τ₀ * π⁻¹ = swap 2 3) (h23 : π * swap 2 3 * π⁻¹ = τ₀) :
    π = cD₁ ∨ π = swap 2 9 * swap 3 8 := by
  have h01 : π * swap 0 1 = swap 0 1 * π := by
    have h := hc (swap (0 : Fin 8) 1) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h04 : π * swap 0 4 = swap 0 4 * π := by
    have h := hc (swap (0 : Fin 8) 4) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h14 : π * swap 1 4 = swap 1 4 * π := by
    have h := hc (swap (1 : Fin 8) 4) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h15 : π * swap 1 5 = swap 1 5 * π := by
    have h := hc (swap (1 : Fin 8) 5) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h45 : π * swap 4 5 = swap 4 5 * π := by
    have h := hc (swap (4 : Fin 8) 5) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h46 : π * swap 4 6 = swap 4 6 * π := by
    have h := hc (swap (4 : Fin 8) 6) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h56 : π * swap 5 6 = swap 5 6 * π := by
    have h := hc (swap (5 : Fin 8) 6) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h57 : π * swap 5 7 = swap 5 7 * π := by
    have h := hc (swap (5 : Fin 8) 7) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h67 : π * swap 6 7 = swap 6 7 * π := by
    have h := hc (swap (6 : Fin 8) 7) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h60 : π * swap 6 0 = swap 6 0 * π := by
    have h := hc (swap (6 : Fin 8) 0) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h70 : π * swap 7 0 = swap 7 0 * π := by
    have h := hc (swap (7 : Fin 8) 0) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have h71 : π * swap 7 1 = swap 7 1 * π := by
    have h := hc (swap (7 : Fin 8) 1) (by decide) (by decide)
    simpa [liftS8_swap] using h
  have hp0 : π 0 = 0 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h01 h04
  have hp1 : π 1 = 1 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h14 h15
  have hp4 : π 4 = 4 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h45 h46
  have hp5 : π 5 = 5 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h56 h57
  have hp6 : π 6 = 6 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h67 h60
  have hp7 : π 7 = 7 := perm_eq_of_comm_swaps (by decide) (by decide) (by decide) h70 h71
  have h9 : π 9 = swap 2 3 (π 8) := by
    have := congrArg (fun f : Perm (Fin 10) => f (π 8)) h89
    simpa [Equiv.Perm.mul_apply, τ₀] using this
  have h8 : π 8 = swap 2 3 (π 9) := by
    have := congrArg (fun f : Perm (Fin 10) => f (π 9)) h89
    simpa [Equiv.Perm.mul_apply, τ₀] using this
  have h3 : π 3 = τ₀ (π 2) := by
    have := congrArg (fun f : Perm (Fin 10) => f (π 2)) h23
    simpa [Equiv.Perm.mul_apply] using this
  have h2 : π 2 = τ₀ (π 3) := by
    have := congrArg (fun f : Perm (Fin 10) => f (π 3)) h23
    simpa [Equiv.Perm.mul_apply] using this
  have hsq8 : π (π 8) = 8 := by
    have := congrArg (fun f : Perm (Fin 10) => f 8) hπ
    simpa [Equiv.Perm.mul_apply] using this
  have h8mem : π 8 = 2 ∨ π 8 = 3 := by
    by_cases h2' : π 8 = 2
    · exact Or.inl h2'
    by_cases h3' : π 8 = 3
    · exact Or.inr h3'
    · exfalso
      have hfix : swap 2 3 (π 8) = π 8 := Equiv.swap_apply_of_ne_of_ne h2' h3'
      rw [hfix] at h9
      exact (by decide : (9 : Fin 10) ≠ 8) (π.injective h9)
  rcases h8mem with h8c | h8c
  · have hπ2 : π 2 = 8 := by rw [← h8c]; exact hsq8
    have hπ3 : π 3 = 9 := by rw [h3, hπ2]; decide
    have hπ9 : π 9 = 3 := by rw [h9, h8c]; decide
    left
    refine Equiv.ext fun x => ?_
    fin_cases x <;>
      simp [cD₁, Equiv.Perm.mul_apply, hp0, hp1, hp4, hp5, hp6, hp7, h8c, hπ2, hπ3,
        hπ9] <;>
      decide
  · have hπ3 : π 3 = 8 := by rw [← h8c]; exact hsq8
    have hπ2 : π 2 = 9 := by rw [h2, hπ3]; decide
    have hπ9 : π 9 = 2 := by rw [h9, h8c]; decide
    right
    refine Equiv.ext fun x => ?_
    fin_cases x <;>
      simp [Equiv.Perm.mul_apply, hp0, hp1, hp4, hp5, hp6, hp7, h8c, hπ2, hπ3, hπ9] <;>
      decide

theorem exists_double_transposition_factors (π : Perm (Fin 10))
    (h : π = cD₁ ∨ π = swap 2 9 * swap 3 8) :
    ∃ t₁ t₂ ρ : Perm (Fin 10), π = t₁ * t₂ ∧ ρ * t₁ * ρ⁻¹ = t₂ ∧
      t₁ 0 = 0 ∧ t₁ 1 = 1 ∧ t₂ 0 = 0 ∧ t₂ 1 = 1 ∧ ρ 0 = 0 ∧ ρ 1 = 1 := by
  rcases h with rfl | rfl
  · exact ⟨swap 2 8, swap 3 9, swap 2 3 * swap 8 9, rfl, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩
  · exact ⟨swap 2 9, swap 3 8, swap 2 3 * swap 8 9, rfl, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩

theorem exists_conj_normal_form (ρ : Perm (Fin 8)) (hρ : ρ * ρ = 1) :
    ∃ (s ρ' : Perm (Fin 8)) (ε : Fin 2), ρ' * ρ' = 1 ∧ ρ' 0 = 0 ∧ ρ' 1 = 1 ∧
      s * ρ * s⁻¹ = swap 0 1 ^ (ε : ℕ) * ρ' := by
  by_cases h1 : ρ = 1
  · subst h1
    exact ⟨1, 1, 0, by simp, by simp, by simp, by simp⟩
  · set k := Multiset.card ρ.cycleType with hk
    have hct : ρ.cycleType = Multiset.replicate k 2 := by
      simpa [hk] using cycleType_eq_replicate_two hρ
    have hkpos : 0 < k := by
      rw [hk]; exact card_cycleType_pos.mpr h1
    have hkle : k ≤ 4 := by
      have h := card_support_eq_two_mul_card_cycleType hρ
      have hc : ρ.support.card ≤ 8 := by simpa using Finset.card_le_univ ρ.support
      rw [← hk] at h
      omega
    interval_cases k
    · have hcyc : ρ.cycleType = (swap (0 : Fin 8) 1).cycleType := by
        rw [hct, cycleType_swap_eight 0 1 (by decide)]
        decide
      obtain ⟨s, hs⟩ := exists_conj_of_cycleType hcyc
      exact ⟨s, 1, 1, by simp, by simp, by simp, by simpa using hs⟩
    · have hcyc : ρ.cycleType = (swap (0 : Fin 8) 1 * swap 2 3).cycleType := by
        rw [hct, cycleType_target2]
      obtain ⟨s, hs⟩ := exists_conj_of_cycleType hcyc
      exact ⟨s, swap 2 3, 1, by decide, by decide, by decide, by simpa using hs⟩
    · have hcyc : ρ.cycleType = (swap (0 : Fin 8) 1 * (swap 2 3 * swap 4 5)).cycleType := by
        rw [hct, cycleType_target3]
      obtain ⟨s, hs⟩ := exists_conj_of_cycleType hcyc
      exact ⟨s, swap 2 3 * swap 4 5, 1, by decide, by decide, by decide, by simpa using hs⟩
    · have hcyc : ρ.cycleType =
          (swap (0 : Fin 8) 1 * ((swap 2 3 * swap 4 5) * swap 6 7)).cycleType := by
        rw [hct, cycleType_target4]
      obtain ⟨s, hs⟩ := exists_conj_of_cycleType hcyc
      exact ⟨s, (swap 2 3 * swap 4 5) * swap 6 7, 1, by decide, by decide, by decide,
        by simpa using hs⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
