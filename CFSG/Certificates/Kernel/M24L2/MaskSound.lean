
module

public import CFSG.Certificates.Kernel.M24L2.ReachSound
public import Certificates.Data.Kernel.M24L2.L2

public section

namespace CFSG.KC.M24L2

open CFSG.CGT.M24R

theorem mask_contains {G : Nat} {ES : List (List (Nat × Nat × Nat))}
    (hinv : ∀ k < 16, invChk G (Nat.mul 4096 k) 4096 = true)
    (htree : Nat.beq (Nat.shiftRight (treeS ES (Nat.shiftLeft 1 (Nat.add 33825 64))) 64) G = true) :
    ∀ k, G.testBit k = (33825 :: ES.flatten.map Prod.fst).contains k := by
  have hG : G.testBit 33825 = true :=
    invChk_spec (hinv 8 (by norm_num)) (by norm_num) (by norm_num) invL_id
  have ht := treeS_inv ES _ [33825] treeInv_root
  rw [List.singleton_append] at ht
  have htG := Nat.eq_of_beq_eq_true htree
  rcases ht with h0 | ⟨hb, _, _⟩
  · rw [h0] at htG
    rw [← htG] at hG
    simp at hG
  · intro k
    rw [← htG, ← hb k]
    change ((treeS ES (Nat.shiftLeft 1 (Nat.add 33825 64))) >>> 64).testBit k = _
    rw [Nat.testBit_shiftRight, Nat.add_comm]

theorem mem_of_validK {L : List Nat} (hR : ReachL L) {G : Nat}
    (hGL : ∀ k, G.testBit k = L.contains k) {n : Nat} (h : validK G n = true) :
    n ∈ (mkCtx ()).codes := by
  unfold validK at h
  rw [Bool.and_eq_true, Nat.blt_eq, land_pow_beq, Bool.not_not] at h
  rw [mem_codes_iff hR]
  refine ⟨h.1, ?_⟩
  rw [← hGL, ← Nat.shiftRight_eq_div_pow n 4]
  exact h.2

end CFSG.KC.M24L2
