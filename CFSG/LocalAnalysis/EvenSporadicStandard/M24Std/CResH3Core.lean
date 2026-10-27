module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH3Block
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH3Unit
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH3Diag

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH3

open Matrix CFSG.RankThree.PartOne.KFSU5 CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem eq_one_or_eq_or_eq_sq {ω : K} (hω : IsPrimitiveRoot ω 3) {c : K} (hc : c ^ 3 = 1) :
    c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
  have hsum : 1 + ω + ω ^ 2 = 0 := by
    have := hω.geom_sum_eq_zero (by norm_num : 1 < 3)
    simpa [Finset.sum_range_succ, add_assoc] using this
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have h : (c - 1) * ((c - ω) * (c - ω ^ 2)) = 0 := by
    linear_combination hc - (c - 1) * c * hsum + (c - 1) * hω3
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Or.inl (sub_eq_zero.mp h1)
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h2))

theorem card_level_le_three {n : ℕ} (hn : n ≤ 5) {T : Type} [Group T] (hT : commutator T = ⊤)
    (ρ : T →* Matrix (Fin n) (Fin n) K) {w : T} {d : Fin n → K} (hw : ρ w = diagonal d)
    (hvan : ∀ t j k, d j ≠ d k → ρ t j k = 0) {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hd3 : ∀ i, d i ^ 3 = 1) (hne : ∃ i, d i ≠ 1) :
    ∀ c : K, c ^ 3 = 1 → (level d c).card ≤ 3 := by
  classical
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hω2 : IsPrimitiveRoot (ω ^ 2) 3 := hω.pow_of_coprime 2 (by norm_num)
  have hω21 : ω ^ 2 ≠ 1 := hω2.ne_one (by norm_num)
  have hωω : ω ≠ ω ^ 2 := by
    intro h
    apply hω1
    have : ω * ω = ω * 1 := by rw [mul_one, ← sq]; exact h.symm
    exact mul_left_cancel₀ hω0 this
  have hdet : ∀ c : K, c ^ (level d c).card = 1 := by
    intro c
    have hJ : ∀ t, ∀ j ∈ level d c, ∀ k ∉ level d c, ρ t j k = 0 := by
      intro t j hj k hk
      refine hvan t j k ?_
      rw [mem_level.1 hj]
      exact fun h' => hk (mem_level.2 h'.symm)
    have h1 := eq_one_of_perfect hT ((Matrix.detMonoidHom).comp (blockHom (level d c) ρ hJ)) w
    have h2 : (blockOf (level d c) (ρ w)).det = 1 := h1
    rw [hw, det_blockOf_of_isDiag _ (isDiag_diagonal d)] at h2
    rw [← h2, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Matrix.diagonal_apply_eq, mem_level.1 hj]
  have h3a : 3 ∣ (level d ω).card := (hω.pow_eq_one_iff_dvd _).1 (hdet ω)
  have h3b : 3 ∣ (level d (ω ^ 2)).card := by
    have := (hω.pow_eq_one_iff_dvd (2 * (level d (ω ^ 2)).card)).1
      (by rw [pow_mul]; exact hdet (ω ^ 2))
    omega
  have hsum : (level d 1).card + (level d ω).card + (level d (ω ^ 2)).card ≤ n := by
    have hd1 : Disjoint (level d 1) (level d ω) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      exact hω1 ((mem_level.1 hi2).symm.trans (mem_level.1 hi1))
    have hd2 : Disjoint (level d 1 ∪ level d ω) (level d (ω ^ 2)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      rcases Finset.mem_union.1 hi1 with hi | hi
      · exact hω21 ((mem_level.1 hi2).symm.trans (mem_level.1 hi))
      · exact hωω ((mem_level.1 hi).symm.trans (mem_level.1 hi2))
    calc (level d 1).card + (level d ω).card + (level d (ω ^ 2)).card
        = (level d 1 ∪ level d ω ∪ level d (ω ^ 2)).card := by
          rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
      _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  have hnot : ¬ ((level d ω).card = 0 ∧ (level d (ω ^ 2)).card = 0) := by
    rintro ⟨ha, hb⟩
    obtain ⟨i, hi⟩ := hne
    rcases eq_one_or_eq_or_eq_sq hω (hd3 i) with h1 | h1 | h1
    · exact hi h1
    · have : i ∈ level d ω := mem_level.2 h1
      rw [Finset.card_eq_zero] at ha
      rw [ha] at this
      exact absurd this (Finset.notMem_empty i)
    · have : i ∈ level d (ω ^ 2) := mem_level.2 h1
      rw [Finset.card_eq_zero] at hb
      rw [hb] at this
      exact absurd this (Finset.notMem_empty i)
  intro c hc
  rcases eq_one_or_eq_or_eq_sq hω hc with h1 | h1 | h1 <;> rw [h1] <;> omega

theorem false_of_diagonal (h : UnitaryFieldData 2 1 K) {n : ℕ} (hn : n ≤ 5) {T : Type} [Group T]
    (hT : commutator T = ⊤) (ρ : T →* Matrix (Fin n) (Fin n) K) (hρ : Function.Injective ρ)
    (hu : ∀ t, ((ρ t).map h.bar).transpose * ρ t = 1) {w x : T} {d : Fin n → K}
    (hw : ρ w = diagonal d) (hw3 : orderOf w = 3) (hwc : ∀ t, t * w = w * t)
    (hx5 : orderOf x = 5) : False := by
  classical
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_three h
  have hw3' : w ^ 3 = 1 := hw3 ▸ pow_orderOf_eq_one w
  have hx5' : x ^ 5 = 1 := hx5 ▸ pow_orderOf_eq_one x
  have hcomm : ∀ t, ρ t * diagonal d = diagonal d * ρ t := fun t => by
    rw [← hw, ← map_mul, ← map_mul, hwc t]
  have hvan : ∀ t j k, d j ≠ d k → ρ t j k = 0 := fun t j k hjk =>
    entry_eq_zero_of_commute (hcomm t) hjk
  have hd3 : ∀ i, d i ^ 3 = 1 := by
    intro i
    have h1 : (diagonal d) ^ 3 = 1 := by rw [← hw, ← map_pow, hw3', map_one]
    rw [Matrix.diagonal_pow] at h1
    have h2 := congrFun (congrFun h1 i) i
    simpa using h2
  have hne : ∃ i, d i ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : w = 1 := by
      apply hρ
      rw [hw, map_one]
      have : d = fun _ => 1 := funext hcon
      rw [this]
      exact Matrix.diagonal_one
    rw [h1, orderOf_one] at hw3
    omega
  have hsize := card_level_le_three hn hT ρ hw hvan hω hd3 hne
  have hxone : ρ x = 1 := by
    ext j k
    by_cases hjk : d j = d k
    · have hJ : ∀ t, ∀ a ∈ level d (d j), ∀ b ∉ level d (d j), ρ t a b = 0 := fun t a ha b hb =>
        hvan t a b (by rw [mem_level.1 ha]; exact fun h' => hb (mem_level.2 h'.symm))
      have hJ' : ∀ t, ∀ a ∈ level d (d j), ∀ b ∉ level d (d j), ρ t b a = 0 :=
        fun t a ha b hb => hvan t b a (by rw [mem_level.1 ha]; exact fun h' => hb (mem_level.2 h'))
      have hblock : blockOf (level d (d j)) (ρ x) = 1 := by
        refine eq_one_of_pow_five_eq_one h ?_ ?_ ?_
        · rw [Fintype.card_coe]
          exact hsize (d j) (hd3 j)
        · exact blockOf_unitary h.bar _ (hu x) (fun a ha b hb => hJ' x a ha b hb)
        · have h5 := map_pow (blockHom (level d (d j)) ρ hJ) x 5
          rw [hx5', map_one] at h5
          exact h5.symm
      have hj : j ∈ level d (d j) := mem_level.2 rfl
      have hk : k ∈ level d (d j) := mem_level.2 hjk.symm
      have := congrFun (congrFun hblock ⟨j, hj⟩) ⟨k, hk⟩
      simpa [blockOf, Matrix.one_apply] using this
    · rw [hvan x j k hjk, Matrix.one_apply_ne]
      exact fun h' => hjk (h' ▸ rfl)
  have hx1 : x = 1 := hρ (by rw [hxone, map_one])
  rw [hx1, orderOf_one] at hx5
  omega

theorem adj_mul (h : UnitaryFieldData 2 1 K) {ι : Type} [Fintype ι] (M N : Matrix ι ι K) :
    ((M * N).map h.bar).transpose = (N.map h.bar).transpose * (M.map h.bar).transpose := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem adj_adj (h : UnitaryFieldData 2 1 K) {ι : Type} (M : Matrix ι ι K) :
    (((M.map h.bar).transpose).map h.bar).transpose = M := by
  ext i j
  simp [h.bar_bar]

theorem false_of_perfect_unitary (h : UnitaryFieldData 2 1 K) {n : ℕ} (hn : n ≤ 5) {T : Type}
    [Group T] (hT : commutator T = ⊤) (ρ : T →* Matrix (Fin n) (Fin n) K)
    (hρ : Function.Injective ρ) (hu : ∀ t, ((ρ t).map h.bar).transpose * ρ t = 1) {w x : T}
    (hw3 : orderOf w = 3) (hwc : ∀ t, t * w = w * t) (hx5 : orderOf x = 5) : False := by
  have hw3' : w ^ 3 = 1 := hw3 ▸ pow_orderOf_eq_one w
  have h3 : ρ w ^ 3 = 1 := by rw [← map_pow, hw3', map_one]
  obtain ⟨P, d, hP, hPd⟩ := exists_unitary_diag h (hu w) h3
  have hPP : P * (P.map h.bar).transpose = 1 := mul_eq_one_comm.mp hP
  let ρ' : T →* Matrix (Fin n) (Fin n) K :=
    { toFun := fun t => (P.map h.bar).transpose * ρ t * P
      map_one' := by rw [map_one, Matrix.mul_one, hP]
      map_mul' := fun s t => by
        calc (P.map h.bar).transpose * ρ (s * t) * P
            = (P.map h.bar).transpose * ρ s * (P * (P.map h.bar).transpose) * ρ t * P := by
              rw [hPP, Matrix.mul_one, map_mul]; simp only [Matrix.mul_assoc]
          _ = ((P.map h.bar).transpose * ρ s * P) * ((P.map h.bar).transpose * ρ t * P) := by
              simp only [Matrix.mul_assoc] }
  have hρ' : Function.Injective ρ' := by
    intro s t hst
    apply hρ
    have h1 : (P.map h.bar).transpose * ρ s * P = (P.map h.bar).transpose * ρ t * P := hst
    have h2 : ρ s = P * ((P.map h.bar).transpose * ρ s * P) * (P.map h.bar).transpose := by
      calc ρ s = (P * (P.map h.bar).transpose) * ρ s * (P * (P.map h.bar).transpose) := by
            rw [hPP, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [h2, h1]
    calc P * ((P.map h.bar).transpose * ρ t * P) * (P.map h.bar).transpose
        = (P * (P.map h.bar).transpose) * ρ t * (P * (P.map h.bar).transpose) := by
          simp only [Matrix.mul_assoc]
      _ = ρ t := by rw [hPP, Matrix.one_mul, Matrix.mul_one]
  have hu' : ∀ t, ((ρ' t).map h.bar).transpose * ρ' t = 1 := by
    intro t
    show (((P.map h.bar).transpose * ρ t * P).map h.bar).transpose *
      ((P.map h.bar).transpose * ρ t * P) = 1
    rw [adj_mul h, adj_mul h, adj_adj h]
    calc (P.map h.bar).transpose * (((ρ t).map h.bar).transpose * P) *
          ((P.map h.bar).transpose * ρ t * P)
        = (P.map h.bar).transpose * (((ρ t).map h.bar).transpose * (P * (P.map h.bar).transpose) *
          ρ t) * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPP, Matrix.mul_one, hu t, Matrix.mul_one, hP]
  have hw' : ρ' w = diagonal d := by
    show (P.map h.bar).transpose * ρ w * P = diagonal d
    calc (P.map h.bar).transpose * ρ w * P = (P.map h.bar).transpose * (ρ w * P) :=
          Matrix.mul_assoc _ _ _
      _ = (P.map h.bar).transpose * (P * diagonal d) := by rw [hPd]
      _ = diagonal d := by rw [← Matrix.mul_assoc, hP, Matrix.one_mul]
  exact false_of_diagonal h hn hT ρ' hρ' hu' hw' hw3 hwc hx5

end CFSG.EvenSporadicStandard.M24Std.CResH3
