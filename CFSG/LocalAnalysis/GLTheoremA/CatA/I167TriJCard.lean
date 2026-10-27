module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172V2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)

private theorem card_gt_of_type167_aux1 (r : ℕ) (hr : 4 ≤ r) : 12096 < orderA r 2 := by
  have hg : Nat.gcd (r + 1) (2 - 1) = 1 := by simp
  have hexp : 10 ≤ r * (r + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    have h20 : 20 ≤ r * (r + 1) := by
      have := Nat.mul_le_mul hr (by omega : 5 ≤ r + 1)
      simpa using this
    omega
  have hpow : 2 ^ 10 ≤ 2 ^ (r * (r + 1) / 2) := Nat.pow_le_pow_right (by norm_num) hexp
  have hsub : Finset.Icc 2 5 ⊆ Finset.Icc 2 (r + 1) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  have hprod : (∏ i ∈ Finset.Icc 2 5, (2 ^ i - 1)) ≤
      ∏ i ∈ Finset.Icc 2 (r + 1), (2 ^ i - 1) :=
    Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun i hi _ => by
        have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
        have h := Nat.one_lt_two_pow (by omega : i ≠ 0)
        omega)
  have h5 : (∏ i ∈ Finset.Icc 2 5, (2 ^ i - 1)) = 9765 := by decide
  unfold orderA
  rw [hg, Nat.div_one]
  calc 12096 < 2 ^ 10 * 9765 := by norm_num
    _ = 2 ^ 10 * (∏ i ∈ Finset.Icc 2 5, (2 ^ i - 1)) := by rw [h5]
    _ ≤ 2 ^ (r * (r + 1) / 2) * (∏ i ∈ Finset.Icc 2 (r + 1), (2 ^ i - 1)) :=
        Nat.mul_le_mul hpow hprod

private theorem card_gt_of_type167_aux2 {Q : Type} [Group Q] [Finite Q] {v : ℕ}
    (hv : 18 ≤ v) (h : padicValNat 2 (Nat.card Q) = v) : 12096 < Nat.card Q := by
  have hdvd : 2 ^ v ∣ Nat.card Q := by simpa [h] using pow_padicValNat_dvd (p := 2) (n := Nat.card Q)
  have hle : 2 ^ v ≤ Nat.card Q := Nat.le_of_dvd Nat.card_pos hdvd
  have h18 : 2 ^ 18 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
  exact lt_of_lt_of_le (by norm_num : 12096 < 2 ^ 18) (le_trans h18 hle)

private theorem card_gt_of_type167_aux3 (hB : LieOrderBridge) {Q : Type} [Group Q] [Finite Q]
    {n : ℕ} (hn : 5 ≤ n) (h : catalogIs Q (isLnA n 2)) : 12096 < Nat.card Q := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨hn2, _, _⟩ | ⟨hn2, _, _⟩ | ⟨hn3, _, _⟩ | ⟨hn4, _, _⟩
  · cases i with
    | cyclic p hp => simp [onLie] at h1
    | alternating m hm => simp [onLie] at h1
    | sporadic s => simp [onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r q =>
        obtain ⟨hrn, hqc⟩ := h1
        have hcard := hB ⟨.A r q, hv⟩ Q ⟨e⟩
        change Nat.card Q = orderA r q.card at hcard
        rw [hqc] at hcard
        rw [hcard]
        exact card_gt_of_type167_aux1 r (by omega)
      | _ => simp [onLie, isLnEps] at h1
  · omega
  · omega
  · omega
  · omega

private theorem card_gt_of_type167_aux4 (hB : LieOrderBridge) {Q : Type} [Group Q] [Finite Q]
    {n : ℕ} (hn : 6 ≤ n) (h : catalogIs Q (isOmMA n 2)) : 12096 < Nat.card Q := by
  obtain ⟨-, hv⟩ := S172.v2_isOmMA hB (S := Q) (f := 1) le_rfl (by rw [pow_one]; exact h)
  rw [one_mul] at hv
  refine card_gt_of_type167_aux2 ?_ hv
  have h30 : 30 ≤ n * (n - 1) := by
    have := Nat.mul_le_mul hn (by omega : 5 ≤ n - 1)
    simpa using this
  omega

private theorem card_gt_of_type167_aux5 (hB : LieOrderBridge) {Q : Type} [Group Q] [Finite Q]
    {n k : ℕ} (hn3 : 3 ≤ n) (hk1 : 1 ≤ k) (hk : k = 1 → 5 ≤ n)
    (hdvd : 3 ∣ 2 ^ k + 1) (h : catalogIs Q (isOmPA n (2 ^ k))) : 12096 < Nat.card Q := by
  obtain ⟨-, hv⟩ := S172.v2_isOmPA hB (S := Q) (f := k) hk1 h
  refine card_gt_of_type167_aux2 ?_ hv
  have hk2 : k ≠ 2 := by intro h2; subst h2; norm_num at hdvd
  have h6 : 6 ≤ n * (n - 1) := by
    have := Nat.mul_le_mul hn3 (by omega : 2 ≤ n - 1)
    simpa using this
  rcases (by omega : k = 1 ∨ 3 ≤ k) with h1 | h3
  · subst h1
    have hn5 : 5 ≤ n := hk rfl
    have h20 : 20 ≤ n * (n - 1) := by
      have := Nat.mul_le_mul hn5 (by omega : 4 ≤ n - 1)
      simpa using this
    omega
  · simpa using Nat.mul_le_mul h3 h6

theorem card_gt_of_type167 (hB : LieOrderBridge) {Q : Type} [Group Q] [Finite Q]
    (h : Type167Grp 3 Q) : 12096 < Nat.card Q := by
  rcases h with ⟨-, n, _, hn5, h⟩ | ⟨-, n, _, hn6, h⟩ | ⟨n, k, _, hn3, hk, hk1, hdvd, h⟩
  · exact card_gt_of_type167_aux3 hB hn5 h
  · exact card_gt_of_type167_aux4 hB hn6 h
  · exact card_gt_of_type167_aux5 hB hn3 hk1 hk hdvd h

end CFSG.LocalAnalysis.GLTheoremA.I167

end
