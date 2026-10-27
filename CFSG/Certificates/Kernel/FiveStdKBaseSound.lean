module

public import CFSG.Certificates.Kernel.FiveStdKOrbSound

public section

namespace CFSG.KC.FiveStdK

open CFSG.GH74.GLS.LU.Local.FiveStd

variable {Gp : Type} [Group Gp]

theorem nodup_Cs_of_tree {ι : E → Gp} (hM : Model ι) {T G nG : Nat} (gE : Nat → E)
    (hg : ∀ l < nG, validE (gE l) = true ∧ codeE (gE l) = f20 G l)
    (h : ∀ i < 28800, tPt T G nG 28800 i = true) : Cs.Nodup := by
  classical
  obtain ⟨h1, h2⟩ := tree_sound hM gE hg h
  have hlt : ∀ i < 28800, rCode (f64 T i) < 781250 := by
    intro i hi
    obtain ⟨x, -, hx, -⟩ := h1 i hi
    rw [← hx]
    exact codeE_lt x
  have hnd := decL_nodup hlt h2
  have hsub : (decL (fun i => rCode (f64 T i)) 28800).toFinset ⊆ Cs.toFinset := by
    intro y hy
    rw [List.mem_toFinset] at hy ⊢
    obtain ⟨i, hi, rfl⟩ := mem_decL.1 hy
    obtain ⟨x, hx, hxc, -⟩ := h1 i hi
    rw [← hxc, decE_codeE]
    exact (mem_Cs_iff x).2 hx
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, decL, List.length_map, List.length_range, List.card_toFinset]
    at hc
  have hlen : Cs.dedup.length = Cs.length := by
    have := (List.dedup_sublist Cs).length_le
    rw [length_Cs] at this ⊢
    omega
  rw [← (List.dedup_sublist Cs).eq_of_length hlen]
  exact List.nodup_dedup Cs

theorem sorted_codes (hnd : Cs.Nodup) : ((Cs.map codeE).mergeSort (· ≤ ·)).Pairwise (· < ·) := by
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (Cs.map codeE)
  have hn : ((Cs.map codeE).mergeSort fun a b => decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm (Cs.map codeE) _).nodup_iff.2 (hnd.map codeE_injective)
  refine (hs.and hn).imp fun hab => ?_
  simp only [decide_eq_true_eq] at hab
  omega

end CFSG.KC.FiveStdK

end
