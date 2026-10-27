module

public import Certificates.Data.Kernel.SortTreeKey
public import CFSG.Certificates.Kernel.SortTreeSound

public section

namespace CFSG.KC.SortTree

open CFSG.KLie.CT

theorem lt_of_succ_lt {f : ℕ → ℕ} {n : ℕ} (hs : ∀ i, i + 1 < n → f i < f (i + 1)) :
    ∀ {i j : ℕ}, i < j → j < n → f i < f j
  | _, 0, h, _ => absurd h (Nat.not_lt_zero _)
  | i, j + 1, h, hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact lt_trans (lt_of_succ_lt hs h (by omega)) (hs j hj)
    · exact hs i hj

theorem hiIncK_sound {rec : ℕ → ℕ} {n wv s : ℕ} (h : hiIncK rec n wv s = true) {i j : ℕ}
    (hi : i < n) (hj : j < n) (e : valF wv (rec i) >>> s = valF wv (rec j) >>> s) : i = j := by
  rw [hiIncK, allN_iff] at h
  have hs : ∀ i, i + 1 < n → valF wv (rec i) >>> s < valF wv (rec (i + 1)) >>> s :=
    fun i hi => blt_iff.1 (h i (by change i < n - 1; omega))
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd e (ne_of_lt (lt_of_succ_lt (f := fun i => valF wv (rec i) >>> s) hs hij hj))
  · rfl
  · exact absurd e (ne_of_gt (lt_of_succ_lt (f := fun i => valF wv (rec i) >>> s) hs hij hi))

end CFSG.KC.SortTree

end
