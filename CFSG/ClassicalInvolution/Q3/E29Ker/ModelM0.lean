module

public import CFSG.ClassicalInvolution.Q3.E29Ker.Model
public import CFSG.ClassicalInvolution.Q3.E29Ker.Alpha0

public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E29Data

theorem mkQ_nA_mem : mkQ 8 nA ∈ memBar α0 α0_card true :=
  ⟨nA, nA_mem_memAt, rfl⟩

theorem mkQ_nB_mem : mkQ 8 nB ∈ memBar α0 α0_card true :=
  ⟨nB, nB_mem_memAt, rfl⟩

theorem nWord_zero_mem_memAt {W : List ℕ} (hW : ∀ l ∈ W, l < 2) :
    nWord 0 W ∈ memAt α0 α0_card true := by
  unfold nWord
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  have hl2 := hW l hl
  interval_cases l
  · rw [show 2 * 0 + 0 = 0 from rfl, nG_zero]
    exact nA_mem_memAt
  · rw [show 2 * 0 + 1 = 1 from rfl, nG_one]
    exact nB_mem_memAt

theorem mem_memBar_zero29 {x : AEQ 8}
    (hx : x ∈ memBar α0 α0_card true) : ∃ W ∈ localWords29, x = mkQ 8 (nWord 0 W) := by
  classical
  have hpair : ∀ s : ℕ, s < 8 → ∀ t : ℕ, t < 8 → s ≠ t →
      mkQ 8 ((n8 0).getD s 1) ≠ mkQ 8 ((n8 0).getD t 1) := by
    intro s hs t ht hst heq
    have h := model_check.2.2.1
    unfold nodupM0 at h
    rw [List.all_eq_true] at h
    have h1 := h s (List.mem_range.mpr hs)
    rw [List.all_eq_true] at h1
    have h2 := h1 t (List.mem_range.mpr ht)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h2
    rcases h2 with h2 | h2
    · exact hst h2
    · have h3 : eqPi ((n8 0).getD s 1) ((n8 0).getD t 1) = true := eqPi_iff.mpr heq
      rw [h3] at h2
      exact Bool.noConfusion h2
  have hnd : ((List.range 8).map fun s => mkQ 8 ((n8 0).getD s 1)).Nodup :=
    List.Nodup.map_on (fun s hs t ht h => by
      by_contra hst
      exact hpair s (List.mem_range.mp hs) t (List.mem_range.mp ht) hst h) List.nodup_range
  have hcard : ((List.range 8).map fun s => mkQ 8 ((n8 0).getD s 1)).toFinset.card = 8 := by
    rw [List.toFinset_card_of_nodup hnd]
    simp
  have hget : ∀ s : ℕ, s < 8 → ∃ W ∈ localWords29, (n8 0).getD s 1 = nWord 0 W := by
    intro s hs
    interval_cases s
    · exact ⟨[], by decide, rfl⟩
    · exact ⟨[0], by decide, rfl⟩
    · exact ⟨[0, 0], by decide, rfl⟩
    · exact ⟨[0, 0, 0], by decide, rfl⟩
    · exact ⟨[1], by decide, rfl⟩
    · exact ⟨[1, 0], by decide, rfl⟩
    · exact ⟨[1, 0, 0], by decide, rfl⟩
    · exact ⟨[1, 0, 0, 0], by decide, rfl⟩
  have hsubset : (((List.range 8).map fun s => mkQ 8 ((n8 0).getD s 1)).toFinset : Set (AEQ 8)) ⊆
      (memBar α0 α0_card true : Set (AEQ 8)) := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_coe.mp hy))
    obtain ⟨W, hW, hWeq⟩ := hget s (List.mem_range.mp hs)
    exact ⟨nWord 0 W, nWord_zero_mem_memAt (localWords29_lt W hW), by rw [hWeq]⟩
  have hnat : Nat.card (memBar α0 α0_card true) = 8 :=
    natCard_memBar (by norm_num) α0 α0_card true
  have hncard : (memBar α0 α0_card true : Set (AEQ 8)).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hnat
  have hfin : (memBar α0 α0_card true : Set (AEQ 8)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hncard]; norm_num)
  have hle : (memBar α0 α0_card true : Set (AEQ 8)).ncard ≤
      (((List.range 8).map fun s => mkQ 8 ((n8 0).getD s 1)).toFinset : Set (AEQ 8)).ncard :=
    le_of_eq (by rw [Set.ncard_coe_finset, hcard, hncard])
  have heq := Set.eq_of_subset_of_ncard_le hsubset hle hfin
  have hxF : x ∈ (((List.range 8).map fun s => mkQ 8 ((n8 0).getD s 1)).toFinset :
      Set (AEQ 8)) := by
    rw [heq]
    exact hx
  obtain ⟨s, hs, hsx⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_coe.mp hxF))
  have hsx' : mkQ 8 ((n8 0).getD s 1) = x := hsx
  obtain ⟨W, hW, hWeq⟩ := hget s (List.mem_range.mp hs)
  exact ⟨W, hW, by rw [← hsx', hWeq]⟩

end CFSG.ClassicalInvolution.Q3.E29Ker
