module

public import CFSG.Certificates.Kernel.Co1Sub.SlpSound
import CFSG.Certificates.Kernel.Co1DceLemmas

public section

namespace CFSG.KC.Co1Sub

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by
  cases a <;> rfl

theorem treeAt_spec {gens : List Nat} {x0 N : Nat} {C : List Nat} {k : Nat}
    (h : treeAt gens x0 N C k = true) :
    (Nat.succ k < N → ptT (recT C k) < ptT (recT C (Nat.succ k))) ∧
    (depT (recT C k) = 0 → ptT (recT C k) = x0) ∧
    (depT (recT C k) ≠ 0 → parT (recT C k) < N ∧ genT (recT C k) < gens.length ∧
      Nat.succ (depT (recT C (parT (recT C k)))) = depT (recT C k) ∧
      vmS (gens.getD (genT (recT C k)) 0) (ptT (recT C (parT (recT C k)))) = ptT (recT C k)) := by
  unfold treeAt at h
  rw [strictB_eq, andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hk => ?_, fun hd => ?_, fun hd => ?_⟩
  · have hc : Nat.blt (Nat.succ k) N = true := Nat.blt_eq.mpr hk
    rw [hc] at h1
    exact Nat.blt_eq.mp h1
  · have hc : Nat.beq (depT (recT C k)) (nat_lit 0) = true := Nat.beq_eq_true_eq _ _ ▸ hd
    rw [hc] at h2
    exact Nat.eq_of_beq_eq_true h2
  · have hc : Nat.beq (depT (recT C k)) (nat_lit 0) = false := by
      cases h' : Nat.beq (depT (recT C k)) (nat_lit 0)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') hd
    rw [hc] at h2
    change strictB (parT (recT C k)) _ = true at h2
    rw [strictB_eq, strictB_eq, andB_eq, andB_eq, andB_eq] at h2
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, lenL_eq_length, getL_zero_eq] at h2
    exact h2

theorem treeK_sound {gens : List Nat} {x0 N : Nat} {C : List Nat} (h : treeK gens x0 N C = true)
    (S : Set Nat) (h0 : x0 ∈ S) (hS : ∀ x ∈ S, ∀ i < gens.length, vmS (gens.getD i 0) x ∈ S) :
    (∀ k < N, ptT (recT C k) ∈ S) ∧
      ∀ k k', k < k' → k' < N → ptT (recT C k) < ptT (recT C k') := by
  unfold treeK at h
  have hN : N ≤ 64 * Nat.succ (N >>> 6) := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hall := CFSG.Certificates.Co1D.allBelow_spec h hN
  have hsp : ∀ k < N, _ := fun k hk => treeAt_spec (hall k hk)
  refine ⟨fun k hk => ?_, fun k k' hkk hk' => ?_⟩
  · suffices ∀ d, ∀ k < N, depT (recT C k) = d → ptT (recT C k) ∈ S from this _ k hk rfl
    intro d
    induction d with
    | zero => exact fun k hk hd => by rw [(hsp k hk).2.1 hd]; exact h0
    | succ d ih =>
      intro k hk hd
      obtain ⟨hp, hg, hdp, hv⟩ := (hsp k hk).2.2 (by omega)
      rw [← hv]
      exact hS _ (ih _ hp (by omega)) _ hg
  · obtain ⟨m, rfl⟩ : ∃ m, k' = k + 1 + m := ⟨k' - (k + 1), by omega⟩
    induction m with
    | zero => exact (hsp k (by omega)).1 (by omega)
    | succ m ih =>
      exact lt_trans (ih (by omega) (by omega)) ((hsp _ (by omega)).1 (by omega))

end CFSG.KC.Co1Sub

end
