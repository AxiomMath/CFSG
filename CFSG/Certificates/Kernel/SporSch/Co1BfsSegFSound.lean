module

public import Certificates.Data.Kernel.SporSch.Co1BfsSegF
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSegSound

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS

theorem bfsHeadK_root {P PAR LAB : Nat → Nat} {N K m R : Nat}
    (hh : bfsHeadK P PAR LAB N K m R = true) : P 0 = R ∧ PAR 0 = 0 ∧ LAB 0 = 0 := by
  unfold bfsHeadK at hh
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hh
  exact ⟨hh.2.1, hh.2.2.1, hh.2.2.2.1⟩

theorem bfsK_of_seg {F : Nat → Nat → Nat} {ng cap N R : Nat} {P PAR LAB W S : Nat → Nat}
    {K m : Nat} (hh : bfsHeadK P PAR LAB N K m R = true)
    (hs : ∀ i < m, bfsSegFK F ng cap N P PAR LAB W S K i = true) :
    bfsK F P PAR LAB W S ng cap N R = true := by
  unfold bfsHeadK at hh
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hh
  obtain ⟨hN, hP0, hpar0, hlab0, hc0, hcN, hmK⟩ := hh
  change m * K = N at hmK
  have hseg : ∀ i < m,
      bfsSegK F P PAR LAB W ng cap K (i * K) (cAtK PAR N (i * K)) = cAtK PAR N (i * K + K) ∧
      ∀ l < K, distAtK P S N (i * K + l) = true := by
    intro i hi
    have h := hs i hi
    unfold bfsSegFK at h
    rw [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, MatL.allBlk_eq,
      List.all_eq_true] at h
    exact ⟨h.1, fun l hl => h.2 l (List.mem_range.2 hl)⟩
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0, Nat.mul_zero] at hmK; omega
    · exact h0
  have hpos : ∀ j, cAtK PAR N (j * K + K) ≠ 0 := fun j =>
    Nat.pos_iff_ne_zero.1 (cBsK_pos PAR _ _ _ _ Nat.one_pos)
  have hdiv : ∀ k < N, k / K < m ∧ k / K * K + k % K = k := fun k hk =>
    ⟨by rw [Nat.div_lt_iff_lt_mul hK, hmK]; exact hk, Nat.div_add_mod' k K⟩
  have hdist : ∀ k < N, distAtK P S N k = true := by
    intro k hk
    have := (hseg (k / K) (hdiv k hk).1).2 (k % K) (Nat.mod_lt _ hK)
    rwa [(hdiv k hk).2] at this
  have hrun : ∀ j ≤ m, bfsRunK F P PAR LAB W ng cap (N + 1) 0 1 =
      bfsRunK F P PAR LAB W ng cap (N + 1 - j * K) (j * K) (cAtK PAR N (j * K)) := by
    intro j
    induction j with
    | zero => intro _; simp [hc0]
    | succ j ih =>
      intro hj
      rw [ih (by omega)]
      obtain ⟨e, -⟩ := hseg j (by omega)
      have hle : (j + 1) * K ≤ N := by rw [← hmK]; exact Nat.mul_le_mul_right K hj
      have hne : bfsSegK F P PAR LAB W ng cap K (j * K) (cAtK PAR N (j * K)) ≠ 0 := by
        rw [e]; exact hpos j
      have hf : N + 1 - j * K = K + (N + 1 - (j + 1) * K) := by
        rw [Nat.succ_mul] at hle ⊢; omega
      rw [hf, bfsRunK_of_seg _ _ _ _ hne, e, Nat.succ_mul]
  have htail : bfsRunK F P PAR LAB W ng cap (0 + 1) N N = N := by
    rw [bfsRunK_succ_eq, if_neg (fun h => Nat.lt_irrefl N h.1)]
  have hfin : bfsRunK F P PAR LAB W ng cap (N + 1) 0 1 = N := by
    have e1 : N + 1 - N = 0 + 1 := by omega
    rw [hrun m (Nat.le_refl m), hmK, hcN, e1, htail]
  unfold bfsK
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  refine ⟨hN, hP0, hpar0, hlab0, ?_, hfin⟩
  change allN N (distAtK P S N) = true
  exact MatL.allN_iff.2 hdist

end CFSG.KS.SporSch.M24

end
