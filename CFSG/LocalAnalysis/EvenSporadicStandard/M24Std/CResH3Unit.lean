module

public import CFSG.GroupTheory.WeirSylow.UnitaryBridge

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH3

open CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem not_five_dvd_card_statedGU [Fintype K] (hK : Fintype.card K = 2 ^ 2) {m : ℕ}
    (hm1 : 1 ≤ m) (hm3 : m ≤ 3) : ¬ 5 ∣ Nat.card (StatedGU m 2 K) := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_statedGU_cast hK hm1
  interval_cases m
  · have h' : (Nat.card (StatedGU 1 2 K) : ℤ) = 3 := by
      rw [h]; norm_num [Finset.prod_Icc_succ_top]
    have h'' : Nat.card (StatedGU 1 2 K) = 3 := by exact_mod_cast h'
    omega
  · have h' : (Nat.card (StatedGU 2 2 K) : ℤ) = 18 := by
      rw [h]; norm_num [Finset.prod_Icc_succ_top]
    have h'' : Nat.card (StatedGU 2 2 K) = 18 := by exact_mod_cast h'
    omega
  · have h' : (Nat.card (StatedGU 3 2 K) : ℤ) = 648 := by
      rw [h]; norm_num [Finset.prod_Icc_succ_top]
    have h'' : Nat.card (StatedGU 3 2 K) = 648 := by exact_mod_cast h'
    omega

theorem eq_one_of_pow_five_eq_one (h : UnitaryFieldData 2 1 K) {ι : Type} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι ≤ 3) {B : Matrix ι ι K}
    (hu : (B.map h.bar).transpose * B = 1) (h5 : B ^ 5 = 1) : B = 1 := by
  classical
  have hfin := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h.card]
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let R := Matrix.reindexAlgEquiv ℤ K e
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
    exact Matrix.ext fun i => isEmptyElim i
  have hB1 : R B ^ 5 = 1 := by rw [← map_pow, h5, map_one]
  have hRB : R B = B.submatrix e.symm e.symm := by
    simp [R, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  have hBu : ((R B).map h.bar).transpose * R B = 1 := by
    rw [hRB, ← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hu]
    exact Matrix.submatrix_one_equiv e.symm
  let u : GL (Fin (Fintype.card ι)) K :=
    ⟨R B, R B ^ 4, by rw [← pow_succ']; exact hB1, by rw [← pow_succ]; exact hB1⟩
  have hmem : u ∈ StatedGU (Fintype.card ι) 2 K := by
    refine Subgroup.subset_closure ?_
    have : (R B).map (fun x : K => x ^ 2) = (R B).map h.bar := by
      ext i j
      simp [UnitaryFieldData.bar_apply]
    show ((R B).map (fun x : K => x ^ 2)).transpose * R B = 1
    rw [this]
    exact hBu
  let g : StatedGU (Fintype.card ι) 2 K := ⟨u, hmem⟩
  have hg5 : g ^ 5 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show (R B) ^ 5 = 1
    exact hB1
  have hdvd5 : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one hg5
  have hdvdc : orderOf g ∣ Nat.card (StatedGU (Fintype.card ι) 2 K) := orderOf_dvd_natCard g
  have hnd := not_five_dvd_card_statedGU hK hpos hι
  have hord : orderOf g = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd5 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hdvdc) hnd
  have hg1 : g = 1 := orderOf_eq_one_iff.mp hord
  have hu1 : R B = 1 := by
    have := congrArg (fun x : StatedGU (Fintype.card ι) 2 K => ((x : GL (Fin (Fintype.card ι)) K) :
      Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K)) hg1
    simpa [g, u] using this
  exact R.injective (by rw [hu1, map_one])

end CFSG.EvenSporadicStandard.M24Std.CResH3
