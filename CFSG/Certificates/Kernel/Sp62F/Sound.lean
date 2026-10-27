module

public import Certificates.Data.Kernel.Sp62F.Defs
public import CFSG.Certificates.Kernel.Sp62W.Sound

public section

namespace CFSG.KC.Sp62F

open CFSG.KD.Sp62F CFSG.KD.Sp62W CFSG.KD.BfsK CFSG.KC.Sp62W CFSG.KGroups.Sp6
  CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U

theorem decC_numC {c : List ℕ} (h : validB c = true) : decC (numC c) = c := by
  unfold decC
  rw [unpackM_numC h, List.take_left' (validB_iff.1 h).1]

theorem of_blkAll {f : ℕ → Bool} {a : ℕ} :
    ∀ {len : ℕ}, blkAll f a len = true → ∀ i < len, f (a + i) = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | len + 1, h, i, hi => by
    change (f (Nat.add a len) && blkAll f a len) = true at h
    rw [Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact of_blkAll h.2 i hi
    · exact h.1

theorem forall_of_blk {f : ℕ → Bool} {B S : ℕ} (h : ∀ j < S, blkAll f (j * B) B = true) :
    ∀ t < S * B, f t = true := by
  intro t ht
  have hB : 0 < B := Nat.pos_of_ne_zero (by rintro rfl; simp at ht)
  have hj : t / B < S := (Nat.div_lt_iff_lt_mul hB).2 ht
  have := of_blkAll (h _ hj) (t % B) (Nat.mod_lt _ hB)
  rwa [Nat.mul_comm, Nat.div_add_mod] at this

theorem allCheck_of_recs {R : ℕ → ℕ} {o n : ℕ} {tab : Array (List ℕ)} (hsz : tab.size = n)
    (hrec : ∀ t < n, validB (tab.getD t []) = true ∧ numC (tab.getD t []) = recX R o t)
    {p : List ℕ → Bool} (h : ∀ t < n, p (decC (recX R o t)) = true) : allCheck p tab = true := by
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hsz] at ht
  obtain ⟨hv, hx⟩ := hrec t ht
  have := h t ht
  rwa [← hx, decC_numC hv] at this

end CFSG.KC.Sp62F

end
