module

public import CFSG.Certificates.Kernel.KeyTreeChunksSound
public import Certificates.Data.SmithD6Model

public section

namespace CFSG.KC.SmithD6Search

open CFSG.KC.KeyTree CFSG.SmithD6

theorem lowerBoundGo_spec (A : Array Nat) (x : Nat)
    (hA : ∀ i j (hi : i < A.size) (hj : j < A.size), i ≤ j → A[i] ≤ A[j]) :
    ∀ fuel lo hi, lo ≤ hi → hi ≤ A.size → hi - lo < 2 ^ fuel →
      (∀ j (h : j < A.size), j < lo → A[j] < x) → (∀ j (h : j < A.size), hi ≤ j → x ≤ A[j]) →
      lowerBoundGo A x fuel lo hi ≤ A.size ∧
      (∀ j (h : j < A.size), j < lowerBoundGo A x fuel lo hi → A[j] < x) ∧
      (∀ j (h : j < A.size), lowerBoundGo A x fuel lo hi ≤ j → x ≤ A[j])
  | 0, lo, hi, h1, h2, h3, h4, h5 => by
    have e : hi = lo := by simp at h3; omega
    subst e
    exact ⟨h2, h4, h5⟩
  | fuel + 1, lo, hi, h1, h2, h3, h4, h5 => by
    simp only [lowerBoundGo]
    by_cases hlt : lo < hi
    · rw [if_pos hlt]
      have hm : (lo + hi) / 2 < A.size := by omega
      have e : A[(lo + hi) / 2]! = A[(lo + hi) / 2] := by simp [hm]
      rw [e]
      have hp : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [Nat.pow_succ]; omega
      by_cases hc : A[(lo + hi) / 2] < x
      · rw [if_pos hc]
        exact lowerBoundGo_spec A x hA fuel _ _ (by omega) h2 (by omega)
          (fun j hj hjl => by
            by_cases hjm : j < lo
            · exact h4 j hj hjm
            · exact Nat.lt_of_le_of_lt (hA j _ hj hm (by omega)) hc) h5
      · rw [if_neg hc]
        exact lowerBoundGo_spec A x hA fuel _ _ (by omega) (by omega) (by omega) h4
          (fun j hj hjl => Nat.le_trans (Nat.le_of_not_lt hc) (hA _ j hm hj hjl))
    · rw [if_neg hlt]
      have e : hi = lo := by omega
      subst e
      exact ⟨h2, h4, h5⟩

theorem search_eq_idx {A : Array Nat} {L : List Nat} {t : KT} {n : Nat} (hL : A.toList = L)
    (hn : L.length = n) (hfuel : n < 2 ^ 40) (hp : L.Pairwise (· < ·))
    (hf : ∀ i (hi : i < L.length), t.find L[i] = i + 1)
    (hs : ∀ x v, t.find x = v + 1 → ∃ hv : v < L.length, L[v] = x) (x : Nat) :
    (if lowerBoundGo A x 40 0 A.size < n && A[lowerBoundGo A x 40 0 A.size]! == x then
      lowerBoundGo A x 40 0 A.size else n) = KT.idx n x t := by
  subst hL hn
  have hsize : A.toList.length = A.size := Array.length_toList
  have hget : ∀ i (hi : i < A.size), A.toList[i]'(by omega) = A[i] := fun i hi =>
    Array.getElem_toList (h := hi)
  have hlt : ∀ i j (hi : i < A.size) (hj : j < A.size), i < j → A[i] < A[j] := by
    intro i j hi hj hij
    rw [← hget i hi, ← hget j hj]
    exact List.pairwise_iff_getElem.mp hp i j (by omega) (by omega) hij
  obtain ⟨r1, r2, r3⟩ := lowerBoundGo_spec A x
    (fun i j hi hj hij => by
      rcases Nat.lt_or_eq_of_le hij with h | rfl
      · exact Nat.le_of_lt (hlt i j hi hj h)
      · exact Nat.le_refl _)
    40 0 A.size (Nat.zero_le _) (Nat.le_refl _) (by omega) (fun j _ h => absurd h (by omega))
    (fun j hj h => absurd hj (by omega))
  obtain ⟨i1, i2⟩ := KT.idx_eq (N := A.toList.length) hf hs x
  generalize lowerBoundGo A x 40 0 A.size = r at r1 r2 r3
  by_cases hx : ∃ i, ∃ hi : i < A.size, A[i] = x
  · obtain ⟨i, hi, hix⟩ := hx
    have hr : r = i := by
      rcases Nat.lt_trichotomy r i with h | h | h
      · exact absurd hix (Nat.ne_of_lt (Nat.lt_of_le_of_lt (r3 r (by omega) (Nat.le_refl _))
          (hlt r i (by omega) hi h)) ∘ Eq.symm)
      · exact h
      · exact absurd hix (Nat.ne_of_lt (r2 i hi h))
    subst hr
    rw [i1 r (by omega) (by rw [hget r hi]; exact hix)]
    have e : A[r]! = A[r] := by simp [hi]
    simp [hsize, hi, e, hix]
  · rw [i2 (fun i hi hix => hx ⟨i, by omega, by rw [← hget i (by omega)]; exact hix⟩)]
    rw [hsize]
    by_cases hr : r < A.size
    · have e : A[r]! = A[r] := by simp [hr]
      have hne : A[r] ≠ x := fun h => hx ⟨r, hr, h⟩
      simp [hr, e, hne]
    · simp [hr]

end CFSG.KC.SmithD6Search

end
