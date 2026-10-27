module

public import CFSG.GroupTheory.InvolutionHexagonIncidence
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.GroupTheory.InvolutionHexagon

variable {P L : Type*} {inc : P → L → Prop}

theorem getVert_inl_or_inr {p₀ : P} {v : P ⊕ L} (c : (incidenceGraph inc).Walk (Sum.inl p₀) v)
    (i : ℕ) (hi : i ≤ c.length) :
    (Even i → ∃ p, c.getVert i = Sum.inl p) ∧ (Odd i → ∃ ℓ, c.getVert i = Sum.inr ℓ) := by
  have hpar := (incidenceColoring inc).even_length_iff_congr (c.take i)
  rw [SimpleGraph.Walk.take_length, min_eq_left hi] at hpar
  rcases hv : c.getVert i with p | ℓ
  · rw [hv] at hpar
    refine ⟨fun _ => ⟨p, rfl⟩, fun hodd => absurd (hpar.mpr ?_) (Nat.not_even_iff_odd.mpr hodd)⟩
    simp
  · rw [hv] at hpar
    refine ⟨fun heven => absurd (hpar.mp heven) ?_, fun _ => ⟨ℓ, rfl⟩⟩
    simp

theorem HexagonData.twelve_le_length_of_inl (H : HexagonData inc) {p₀ : P}
    (c : (incidenceGraph inc).Walk (Sum.inl p₀) (Sum.inl p₀)) (hc : c.IsCycle) :
    12 ≤ c.length := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ : ∃ k, c.length = 2 * k := by
    obtain ⟨n, hn⟩ := ((incidenceColoring inc).even_length_iff_congr c).mpr Iff.rfl
    exact ⟨n, by omega⟩
  have h3 := hc.three_le_length
  have := H.finite_lines
  obtain ⟨T₀⟩ : Nonempty L := (Nat.card_pos_iff.mp (by rw [H.card_lines]; norm_num)).1
  set q : ℕ → P := fun j => Sum.elim id (fun _ => p₀) (c.getVert (2 * j)) with hq
  set m : ℕ → L := fun j => Sum.elim (fun _ => T₀) id (c.getVert (2 * j + 1)) with hm
  have hqv : ∀ j, j ≤ k → c.getVert (2 * j) = Sum.inl (q j) := by
    intro j hj
    obtain ⟨p, hp⟩ := (getVert_inl_or_inr c (2 * j) (by omega)).1 (even_two_mul j)
    simp only [hq, hp, Sum.elim_inl, id]
  have hmv : ∀ j, j < k → c.getVert (2 * j + 1) = Sum.inr (m j) := by
    intro j hj
    obtain ⟨ℓ, hℓ⟩ := (getVert_inl_or_inr c (2 * j + 1) (by omega)).2 (odd_two_mul_add_one j)
    simp only [hm, hℓ, Sum.elim_inr, id]
  have hin1 : ∀ j, j < k → inc (q j) (m j) := by
    intro j hj
    have hadj := c.adj_getVert_succ (i := 2 * j) (by omega)
    rw [hqv j (by omega), hmv j hj] at hadj
    exact (incidenceGraph_adj_inl_inr _ _).mp hadj
  have hin2 : ∀ j, j < k → inc (q (j + 1)) (m j) := by
    intro j hj
    have hadj := c.adj_getVert_succ (i := 2 * j + 1) (by omega)
    rw [hmv j hj, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, hqv (j + 1) (by omega)] at hadj
    exact (incidenceGraph_adj_inr_inl _ _).mp hadj
  have hqk : q k = q 0 := by
    have h0 := hqv 0 (by omega)
    have hk' := hqv k le_rfl
    rw [Nat.mul_zero, SimpleGraph.Walk.getVert_zero, Sum.inl.injEq] at h0
    rw [← hk, SimpleGraph.Walk.getVert_length, Sum.inl.injEq] at hk'
    rw [← hk', ← h0]
  have hlast : inc (q 0) (m (k - 1)) := by
    have := hin2 (k - 1) (by omega)
    rwa [show k - 1 + 1 = k by omega, hqk] at this
  have hinj := hc.getVert_injOn'
  have hqinj : ∀ i j, i < k → j < k → q i = q j → i = j := by
    intro i j hi hj hij
    have := hinj (show 2 * i ≤ c.length - 1 by omega) (show 2 * j ≤ c.length - 1 by omega)
      (by rw [hqv i hi.le, hqv j hj.le, hij])
    omega
  have hminj : ∀ i j, i < k → j < k → m i = m j → i = j := by
    intro i j hi hj hij
    have := hinj (show 2 * i + 1 ≤ c.length - 1 by omega)
      (show 2 * j + 1 ≤ c.length - 1 by omega) (by rw [hmv i hi, hmv j hj, hij])
    omega
  have hd : ∀ i j, i < k → j < k → i ≠ j → q i ≠ q j := fun i j hi hj hij e =>
    hij (hqinj i j hi hj e)
  have hmd : ∀ i j, i < k → j < k → i ≠ j → m i ≠ m j := fun i j hi hj hij e =>
    hij (hminj i j hi hj e)
  have hC : ∀ j, j < k → Collinear inc (q j) (q (j + 1)) := fun j hj =>
    ⟨m j, hin1 j hj, hin2 j hj⟩
  have hnd : ((List.range k).map q).Nodup :=
    List.nodup_range.map_on fun x hx y hy e =>
      hqinj x y (List.mem_range.mp hx) (List.mem_range.mp hy) e
  have hk2 : 2 ≤ k := by omega
  have hk5 : k ≤ 5 := by omega
  interval_cases k
  ·
    exact hmd 0 1 (by norm_num) (by norm_num) (by norm_num) (H.eq_of_inc
      (hd 0 1 (by norm_num) (by norm_num) (by norm_num)) (hin1 0 (by norm_num))
      (hin2 0 (by norm_num)) hlast (hin1 1 (by norm_num)))
  ·
    exact hmd 0 1 (by norm_num) (by norm_num) (by norm_num) (H.eq_of_triangle
      (hd 0 1 (by norm_num) (by norm_num) (by norm_num))
      (hd 1 2 (by norm_num) (by norm_num) (by norm_num))
      (hd 0 2 (by norm_num) (by norm_num) (by norm_num)) (hin1 0 (by norm_num))
      (hin2 0 (by norm_num)) (hin1 1 (by norm_num)) (hin2 1 (by norm_num))
      ⟨m 2, hlast, hin1 2 (by norm_num)⟩)
  ·
    have hc : ∀ j, j < 2 → ¬ Collinear inc (q j) (q (j + 2)) := fun j hj hC' =>
      hmd j (j + 1) (by omega) (by omega) (by omega) (H.eq_of_triangle
        (hd j (j + 1) (by omega) (by omega) (by omega))
        (hd (j + 1) (j + 2) (by omega) (by omega) (by omega))
        (hd j (j + 2) (by omega) (by omega) (by omega)) (hin1 j (by omega))
        (hin2 j (by omega)) (hin1 (j + 1) (by omega)) (hin2 (j + 1) (by omega)) hC')
    exact H.not_square ⟨q 0, q 1, q 2, q 3, hnd, hC 0 (by norm_num), hC 1 (by norm_num),
      hC 2 (by norm_num), ⟨m 3, hin1 3 (by norm_num), hlast⟩, hc 0 (by norm_num),
      hc 1 (by norm_num)⟩
  ·
    have hc : ∀ j, j < 3 → ¬ Collinear inc (q j) (q (j + 2)) := fun j hj hC' =>
      hmd j (j + 1) (by omega) (by omega) (by omega) (H.eq_of_triangle
        (hd j (j + 1) (by omega) (by omega) (by omega))
        (hd (j + 1) (j + 2) (by omega) (by omega) (by omega))
        (hd j (j + 2) (by omega) (by omega) (by omega)) (hin1 j (by omega))
        (hin2 j (by omega)) (hin1 (j + 1) (by omega)) (hin2 (j + 1) (by omega)) hC')
    have h03 : ¬ Collinear inc (q 0) (q 3) := fun hC' =>
      hmd 3 4 (by norm_num) (by norm_num) (by norm_num) (H.eq_of_triangle
        (hd 3 4 (by norm_num) (by norm_num) (by norm_num))
        (hd 4 0 (by norm_num) (by norm_num) (by norm_num))
        (hd 3 0 (by norm_num) (by norm_num) (by norm_num)) (hin1 3 (by norm_num))
        (hin2 3 (by norm_num)) (hin1 4 (by norm_num)) hlast hC'.symm)
    have h14 : ¬ Collinear inc (q 1) (q 4) := fun hC' =>
      hmd 4 0 (by norm_num) (by norm_num) (by norm_num) (H.eq_of_triangle
        (hd 4 0 (by norm_num) (by norm_num) (by norm_num))
        (hd 0 1 (by norm_num) (by norm_num) (by norm_num))
        (hd 4 1 (by norm_num) (by norm_num) (by norm_num)) (hin1 4 (by norm_num)) hlast
        (hin1 0 (by norm_num)) (hin2 0 (by norm_num)) hC'.symm)
    exact H.not_pentagon ⟨q 0, q 1, q 2, q 3, q 4, hnd, hC 0 (by norm_num),
      hC 1 (by norm_num), hC 2 (by norm_num), hC 3 (by norm_num),
      ⟨m 4, hin1 4 (by norm_num), hlast⟩, hc 0 (by norm_num), h03, hc 1 (by norm_num), h14,
      hc 2 (by norm_num)⟩

theorem HexagonData.twelve_le_length (H : HexagonData inc) {v : P ⊕ L}
    (c : (incidenceGraph inc).Walk v v) (hc : c.IsCycle) : 12 ≤ c.length := by
  classical
  rcases v with p | ℓ
  · exact H.twelve_le_length_of_inl c hc
  · have hadj := c.adj_getVert_succ (i := 0) (by have := hc.three_le_length; omega)
    rw [SimpleGraph.Walk.getVert_zero, zero_add] at hadj
    obtain ⟨p, hp⟩ : ∃ p, c.getVert 1 = Sum.inl p := by
      rcases h1 : c.getVert 1 with p | ℓ'
      · exact ⟨p, rfl⟩
      · rw [h1] at hadj
        exact absurd hadj (not_incidenceGraph_adj_inr_inr _ _)
    have hmem : Sum.inl p ∈ c.support := hp ▸ c.getVert_mem_support 1
    have := H.twelve_le_length_of_inl (c.rotate _ hmem) (hc.rotate hmem)
    rwa [SimpleGraph.Walk.length_rotate] at this

end CFSG.GroupTheory.InvolutionHexagon
