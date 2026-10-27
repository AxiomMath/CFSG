module

public import CFSG.Certificates.Kernel.SortTreeSound

public section

namespace CFSG.KC.SortTree

open CFSG.KLie.CT CFSG.KC.Bfs

variable {act : ℕ → ℕ → ℕ} {ng : ℕ} {valid : ℕ → Bool} {root : ℕ} {rec : ℕ → ℕ}
  {n wv wl wp : ℕ}

theorem treeOK_of_chunks {B C : ℕ} (hcov : n ≤ C * B)
    (hc : ∀ c < C, chunkOK act ng valid root rec n wv wl wp B c = true) :
    treeOK act ng valid root rec n wv wl wp B C = true := by
  rw [treeOK, andB_true_iff, ble_iff, allN_iff]
  exact ⟨hcov, hc⟩

theorem tree_sound_chunks {B C : ℕ} (hcov : n ≤ C * B)
    (hc : ∀ c < C, chunkOK act ng valid root rec n wv wl wp B c = true) :
    (∀ i < n, Reach act ng root (valF wv (rec i))) ∧ (∀ i < n, valid (valF wv (rec i)) = true) ∧
    (∀ i j, i < j → j < n → valF wv (rec i) < valF wv (rec j)) ∧
    (0 < n → ∃ j < n, valF wv (rec j) = root) :=
  tree_sound (treeOK_of_chunks hcov hc)

theorem forall_lt_one {P : ℕ → Prop} (h : P 0) : ∀ c < 1, P c := fun c hc => by
  rw [Nat.lt_one_iff.1 hc]
  exact h

theorem forall_lt_succ {P : ℕ → Prop} {m : ℕ} (h : ∀ c < m, P c) (hm : P m) :
    ∀ c < m + 1, P c := fun c hc => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
  · exact h c hc
  · exact hm

theorem forall_lt_add {P : ℕ → Prop} {a b : ℕ} (ha : ∀ c < a, P c) (hb : ∀ c < b, P (a + c)) :
    ∀ c < a + b, P c := fun c hc => by
  by_cases h : c < a
  · exact ha c h
  · have e : a + (c - a) = c := by omega
    have := hb (c - a) (by omega)
    rwa [e] at this

end CFSG.KC.SortTree

end
