module

public import CFSG.Certificates.Kernel.SortTreeChunks

public section

namespace CFSG.KC.SortTree

open CFSG.KLie.CT CFSG.KC.Bfs

@[expose] noncomputable def treeSl (act : ℕ → ℕ → ℕ) (ng : ℕ) (valid : ℕ → Bool) (root : ℕ)
    (rec : ℕ → ℕ) (n wv wl wp B o m : ℕ) : Bool :=
  allN m fun j => chunkOK act ng valid root rec n wv wl wp B (Nat.add o j)

@[expose] noncomputable def closeSl (act : ℕ → ℕ → ℕ) (ng : ℕ) (rec : ℕ → ℕ)
    (E : ℕ → ℕ → ℕ) (n wv B o m : ℕ) : Bool :=
  allN m fun j => closeChunk act ng rec E n wv B (Nat.add o j)

theorem none_lt {P : ℕ → Bool} : ∀ c < 0, P c = true := fun _ h => absurd h (Nat.not_lt_zero _)

theorem sl_add {P : ℕ → Bool} {a m b : ℕ} (ha : ∀ c < a, P c = true)
    (h : allN m (fun j => P (Nat.add a j)) = true) (hb : a + m = b) : ∀ c < b, P c = true := by
  subst hb
  exact forall_lt_add ha ((allN_iff _ _).1 h)

theorem closeOK_of_chunks {act : ℕ → ℕ → ℕ} {ng : ℕ} {rec : ℕ → ℕ} {E : ℕ → ℕ → ℕ}
    {n wv B C : ℕ} (hcov : n ≤ C * B) (hc : ∀ c < C, closeChunk act ng rec E n wv B c = true) :
    closeOK act ng rec E n wv B C = true := by
  rw [closeOK, andB_true_iff, ble_iff, allN_iff]
  exact ⟨hcov, hc⟩

end CFSG.KC.SortTree

end
