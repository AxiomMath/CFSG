module

public import CFSG.ClassicalGroups.Unitary.Transitivity

public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

theorem herm_e0_e0 {n : ℕ} : herm σ (e0 K n) (e0 K n) = 1 := by
  rw [herm_single_zero]
  simp

theorem T_succ_eq_top (hσ : IsUnitaryInvolution σ) {n : ℕ}
    (htrans : ∀ x : Fin (n + 1) → K, herm σ x x = 1 → ∃ t ∈ T σ (n + 1), t • x = e0 K n)
    (hT : T σ n = ⊤) : T σ (n + 1) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hge : herm σ (g • e0 K n) (g • e0 K n) = 1 := by rw [herm_smul_smul, herm_e0_e0]
  obtain ⟨t, ht, hte⟩ := htrans _ hge
  have hM : (t * g) • e0 K n = e0 K n := by rw [mul_smul, hte]
  have hblk : blk (t * g) hM ∈ T σ n := by rw [hT]; exact Subgroup.mem_top _
  have hMT := mem_T_of_blk_mem_T hσ.invol hM hblk
  have hg : g = t⁻¹ * (t * g) := by group
  rw [hg]
  exact (T σ (n + 1)).mul_mem ((T σ (n + 1)).inv_mem ht) hMT

theorem T_four_eq_top (hσ : IsUnitaryInvolution σ) : T σ 4 = ⊤ := by
  obtain ⟨W⟩ := hσ.nonempty_wittData
  rw [eq_top_iff]
  intro g _
  obtain ⟨t, ht, hta, htb⟩ := exists_mem_T_fix_hyp hσ W g
  obtain ⟨h1, h0⟩ := W.fix_singles_of_fix (n := 2) hta htb
  have hM : (t * g) • e0 K 3 = e0 K 3 := h0
  have hc : consL 3 (e0 K 2) = (Pi.single 1 1 : Fin 4 → K) := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j =>
      rw [consL_apply, Fin.cons_succ, ← Fin.succ_zero_eq_one, e0]
      simp only [Pi.single_apply, Fin.succ_inj]
  have hA : blk (t * g) hM • e0 K 2 = e0 K 2 := by
    have := smul_consL_eq_consL_blk hM (e0 K 2)
    rw [hc, h1, ← hc, consL_apply, consL_apply] at this
    exact (Fin.cons_right_injective _ this).symm
  have hA' : blk (blk (t * g) hM) hA ∈ T σ 2 := by
    rw [T_two_eq_top hσ]
    exact Subgroup.mem_top _
  have hAT : blk (t * g) hM ∈ T σ 3 := mem_T_of_blk_mem_T hσ.invol hA hA'
  have hMT : t * g ∈ T σ 4 := mem_T_of_blk_mem_T hσ.invol hM hAT
  have hg : g = t⁻¹ * (t * g) := by group
  rw [hg]
  exact (T σ 4).mul_mem ((T σ 4).inv_mem ht) hMT

theorem T_eq_top (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 2 ≤ n)
    (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) : T σ n = ⊤ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (by omega : n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with rfl | rfl | rfl | h5
    · exact T_two_eq_top hσ
    · exact T_succ_eq_top hσ (n := 2) (fun x hx =>
        exists_mem_T_smul_eq_of_norm_one hσ (Or.inr ⟨le_rfl, h3 rfl⟩) hx herm_e0_e0)
        (T_two_eq_top hσ)
    · exact T_four_eq_top hσ
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact T_succ_eq_top hσ (fun x hx =>
        exists_mem_T_smul_eq_of_norm_one hσ (Or.inl (by omega)) hx herm_e0_e0)
        (ih m (by omega) (by omega) (fun h => by omega))

end CFSG.ClassicalGroups.Unitary
