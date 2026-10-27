module

public import CFSG.ClassicalInvolution.Q3.E64Ker.Model

public section

namespace CFSG.ClassicalInvolution.Q3.E64Ker

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E64Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

theorem mem_memBar_zero {x : AEQ 7}
    (hx : x ∈ memBar α0 α0_card true) : ∃ W ∈ localWords, x = mkQ 7 (mWord 0 W) := by
  classical
  have hsub : ∀ y ∈ m8 0, y ∈ aeSub 7 := by
    intro y hy
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hy
    exact mWord_mem (by norm_num) (localWords_lt W hW)
  have hnd : ((m8 0).map (mkQ 7)).Nodup :=
    List.Nodup.map_on (fun y hy z hz h => mkQ7_inj (hsub y hy) (hsub z hz) h)
      model_check.2.2.1
  have hcard : ((m8 0).map (mkQ 7)).toFinset.card = 8 := by
    rw [List.toFinset_card_of_nodup hnd]
    simp [m8, localWords]
  have hsubset : (((m8 0).map (mkQ 7)).toFinset : Set (AEQ 7)) ⊆
      (memBar α0 α0_card true : Set (AEQ 7)) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_coe.mp hy))
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp ha
    exact ⟨mWord 0 W, mWord_zero_mem_memAt (localWords_lt W hW), rfl⟩
  have hnat : Nat.card (memBar α0 α0_card true) = 8 :=
    natCard_memBar (by norm_num) α0 α0_card true
  have hncard : (memBar α0 α0_card true : Set (AEQ 7)).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hnat
  have hfin : (memBar α0 α0_card true : Set (AEQ 7)).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hncard]; norm_num)
  have hle : (memBar α0 α0_card true : Set (AEQ 7)).ncard ≤
      (((m8 0).map (mkQ 7)).toFinset : Set (AEQ 7)).ncard :=
    le_of_eq (by rw [Set.ncard_coe_finset, hcard, hncard])
  have heq := Set.eq_of_subset_of_ncard_le hsubset hle hfin
  have hxF : x ∈ (((m8 0).map (mkQ 7)).toFinset : Set (AEQ 7)) := by
    rw [heq]
    exact hx
  obtain ⟨a, ha, hax⟩ := List.mem_map.mp (List.mem_toFinset.mp (Finset.mem_coe.mp hxF))
  obtain ⟨W, hW, rfl⟩ := List.mem_map.mp ha
  exact ⟨W, hW, hax.symm⟩

end CFSG.ClassicalInvolution.Q3.E64Ker
