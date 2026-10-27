module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)

variable {K : Type} [Field K] {n : ℕ}

section Rows

theorem mat_nsElt_apply_of_not_mem_left {k : Fin n} {r : Fin n ⊕ Fin n} (hr : r ∉ coords k)
    (v : Fin n ⊕ Fin n) :
    mat n K (nsElt k) r v = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r v := by
  rw [mat_nsElt]
  exact blockMat_apply_of_not_mem k _ (fun h => hr h.1)

theorem mat_nsElt_apply_of_not_mem_right {k : Fin n} {t : Fin n ⊕ Fin n} (ht : t ∉ coords k)
    (v : Fin n ⊕ Fin n) :
    mat n K (nsElt k) v t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) v t := by
  rw [mat_nsElt]
  exact blockMat_apply_of_not_mem k _ (fun h => ht h.2)

theorem mul_mat_nsElt_apply_of_not_mem {k : Fin n}
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (r : Fin n ⊕ Fin n) {t : Fin n ⊕ Fin n}
    (ht : t ∉ coords k) : (X * mat n K (nsElt k)) r t = X r t := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl
    (fun s _ => by rw [mat_nsElt_apply_of_not_mem_right ht]), ← Matrix.mul_apply, Matrix.mul_one]

theorem mat_nsElt_mul_apply_of_not_mem {k : Fin n}
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) {r : Fin n ⊕ Fin n} (hr : r ∉ coords k)
    (t : Fin n ⊕ Fin n) : (mat n K (nsElt k) * X) r t = X r t := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl
    (fun s _ => by rw [mat_nsElt_apply_of_not_mem_left hr]), ← Matrix.mul_apply, Matrix.one_mul]

theorem not_mem_coords_of_mem_coords {p p' : Fin n} (hpp : p ≠ p') {t : Fin n ⊕ Fin n}
    (ht : t ∈ coords p) : t ∉ coords p' := by
  intro h
  rcases mem_coords.1 ht with rfl | rfl <;> rcases mem_coords.1 h with h' | h'
  · exact hpp (Sum.inl.inj h')
  · exact Sum.inl_ne_inr h'
  · exact Sum.inr_ne_inl h'
  · exact hpp (Sum.inr.inj h')

theorem commute_nsElt_of_ne {p p' : Fin n} (hpp : p ≠ p') :
    Commute (nsElt (K := K) p) (nsElt p') := by
  have hmem : ∀ k : Fin n, nsElt (K := K) k ∈ spBlock K ({k} : Finset (Fin n)) := fun k => by
    rw [spBlock_singleton]
    exact nsTorusSp_le_longRootSp2 k (nsElt_mem_nsTorusSp k)
  exact commute_of_mem_spBlock_of_disjoint (Finset.disjoint_singleton.2 hpp) (hmem p) (hmem p')

end Rows

section Commute

variable {p p' : Fin n}

theorem mat_commute_nsElt_mul_aux [CharP K 2] (hpp : p ≠ p')
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hM : M * (mat n K (nsElt p) * mat n K (nsElt p')) =
      mat n K (nsElt p) * mat n K (nsElt p') * M) :
    (∀ r, r ∉ coords p → r ∉ coords p' → ∀ t ∈ coords p, M r t = 0 ∧ M t r = 0) ∧
    (∀ q, (q = p ∨ q = p') → M (Sum.inr q) (Sum.inl p) = -M (Sum.inl q) (Sum.inr p) ∧
      M (Sum.inr q) (Sum.inr p) = M (Sum.inl q) (Sum.inl p) - M (Sum.inl q) (Sum.inr p)) := by
  have hNN : mat n K (nsElt (K := K) p) * mat n K (nsElt p') =
      mat n K (nsElt p') * mat n K (nsElt p) := by
    rw [← map_mul, ← map_mul, (commute_nsElt_of_ne hpp).eq]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hcol : ∀ a t, t ∈ coords p → (M * mat n K (nsElt p)) a t =
      (mat n K (nsElt p) * mat n K (nsElt p') * M) a t := fun a t ht => by
    rw [← hM, ← Matrix.mul_assoc,
      mul_mat_nsElt_apply_of_not_mem _ _ (not_mem_coords_of_mem_coords hpp ht)]
  have hrow : ∀ a t, a ∈ coords p → (mat n K (nsElt p) * M) a t =
      (M * (mat n K (nsElt p) * mat n K (nsElt p'))) a t := fun a t ha => by
    rw [hM, hNN, Matrix.mul_assoc,
      mat_nsElt_mul_apply_of_not_mem _ (not_mem_coords_of_mem_coords hpp ha)]
  refine ⟨fun r hr hr' t ht => ?_, fun q hq => ?_⟩
  · have hR : ∀ s, (mat n K (nsElt p) * mat n K (nsElt p') * M) r s = M r s := fun s => by
      rw [Matrix.mul_assoc, mat_nsElt_mul_apply_of_not_mem _ hr,
        mat_nsElt_mul_apply_of_not_mem _ hr']
    have hC : ∀ a, (M * (mat n K (nsElt p) * mat n K (nsElt p'))) a r = M a r := fun a => by
      rw [← Matrix.mul_assoc, mul_mat_nsElt_apply_of_not_mem _ _ hr',
        mul_mat_nsElt_apply_of_not_mem _ _ hr]
    have e1 := mul_mat_nsElt_apply M r (inl_mem_coords p)
    have e2 := mul_mat_nsElt_apply M r (inr_mem_coords p)
    rw [hcol r _ (inl_mem_coords p), hR, mat_nsElt_inl_inl, mat_nsElt_inr_inl] at e1
    rw [hcol r _ (inr_mem_coords p), hR, mat_nsElt_inl_inr, mat_nsElt_inr_inr] at e2
    have hb : M r (Sum.inr p) = 0 := by
      linear_combination e1 + e2 - M r (Sum.inr p) * h2
    have ha : M r (Sum.inl p) = 0 := by linear_combination e1 - hb
    have f1 := mat_nsElt_mul_apply M (inl_mem_coords p) r
    have f2 := mat_nsElt_mul_apply M (inr_mem_coords p) r
    rw [hrow _ r (inl_mem_coords p), hC, mat_nsElt_inl_inl, mat_nsElt_inl_inr] at f1
    rw [hrow _ r (inr_mem_coords p), hC, mat_nsElt_inr_inl, mat_nsElt_inr_inr] at f2
    have hx : M (Sum.inl p) r = 0 := by
      linear_combination f2 - M (Sum.inr p) r * h2
    have hy : M (Sum.inr p) r = 0 := by linear_combination hx - f1
    rcases mem_coords.1 ht with rfl | rfl
    · exact ⟨ha, hx⟩
    · exact ⟨hb, hy⟩
  ·
    have hrowq : ∀ t, (mat n K (nsElt p) * mat n K (nsElt p') * M) (Sum.inl q) t =
        mat n K (nsElt q) (Sum.inl q) (Sum.inl q) * M (Sum.inl q) t +
          mat n K (nsElt q) (Sum.inl q) (Sum.inr q) * M (Sum.inr q) t := by
      intro t
      rcases hq with rfl | rfl
      · rw [← hM, ← hrow _ t (inl_mem_coords q), mat_nsElt_mul_apply _ (inl_mem_coords q)]
      · rw [Matrix.mul_assoc, mat_nsElt_mul_apply_of_not_mem _
            (not_mem_coords_of_mem_coords (Ne.symm hpp) (inl_mem_coords q)),
          mat_nsElt_mul_apply _ (inl_mem_coords q)]
    have e1 := mul_mat_nsElt_apply M (Sum.inl q) (inl_mem_coords p)
    have e2 := mul_mat_nsElt_apply M (Sum.inl q) (inr_mem_coords p)
    rw [hcol _ _ (inl_mem_coords p), hrowq, mat_nsElt_inl_inl, mat_nsElt_inl_inr,
      mat_nsElt_inl_inl, mat_nsElt_inr_inl] at e1
    rw [hcol _ _ (inr_mem_coords p), hrowq, mat_nsElt_inl_inl, mat_nsElt_inl_inr,
      mat_nsElt_inl_inr, mat_nsElt_inr_inr] at e2
    exact ⟨by linear_combination e1, by linear_combination e2⟩

theorem q2_monomial_of_relations [CharP K 2] (hK : Nat.card K = 2) {a b c d a' b' c' d' : K}
    (hN : a * (a - b) + b * b + (c * (c - d) + d * d) = 1)
    (hX1 : b * a' - a * b' + (d * c' - c * d') = 0)
    (hX2 : a * (a' - b') + b * b' + (c * (c' - d') + d * d') = 0) :
    (a' = 0 ∧ b' = 0 ∧ c = 0 ∧ d = 0) ∨ (a = 0 ∧ b = 0 ∧ c' = 0 ∧ d' = 0) := by
  have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hn : (-1 : K) = 1 := CharTwo.neg_eq 1
  rcases eq_zero_or_eq_one_of_natCard_two hK a with rfl | rfl <;>
  rcases eq_zero_or_eq_one_of_natCard_two hK b with rfl | rfl <;>
  rcases eq_zero_or_eq_one_of_natCard_two hK c with rfl | rfl <;>
  rcases eq_zero_or_eq_one_of_natCard_two hK d with rfl | rfl <;>
  rcases eq_zero_or_eq_one_of_natCard_two hK a' with rfl | rfl <;>
  rcases eq_zero_or_eq_one_of_natCard_two hK b' with rfl | rfl <;>
  rcases eq_zero_or_eq_one_of_natCard_two hK c' with rfl | rfl <;>
  rcases eq_zero_or_eq_one_of_natCard_two hK d' with rfl | rfl <;>
  simp [h11, hn] at hN hX1 hX2 ⊢

theorem sum_eq_of_support_planes {p p' : Fin n} (hpp : p ≠ p') (f : Fin n ⊕ Fin n → K)
    (hf : ∀ c, c ∉ coords p → c ∉ coords p' → f c = 0) :
    ∑ c, f c = f (Sum.inl p) + f (Sum.inr p) + (f (Sum.inl p') + f (Sum.inr p')) := by
  classical
  have hsub : ∑ c ∈ ({Sum.inl p, Sum.inr p, Sum.inl p', Sum.inr p'} :
      Finset (Fin n ⊕ Fin n)), f c = ∑ c, f c := by
    refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc => hf c ?_ ?_
    · intro h
      apply hc
      rcases mem_coords.1 h with rfl | rfl <;> simp
    · intro h
      apply hc
      rcases mem_coords.1 h with rfl | rfl <;> simp
  rw [← hsub, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · ring
  · simp
  · simp [hpp]
  · simp [hpp]

theorem monomial_of_commute_nsElt_mul [CharP K 2] (hK : Nat.card K = 2) (hpp : p ≠ p')
    {x : StatedSp n K} (hx : x * (nsElt p * nsElt p') = (nsElt p * nsElt p') * x) :
    (∀ i ∈ coords p, ∀ j ∈ coords p', mat n K x i j = 0 ∧ mat n K x j i = 0) ∨
      ((∀ i ∈ coords p, ∀ j ∈ coords p, mat n K x i j = 0) ∧
        ∀ i ∈ coords p', ∀ j ∈ coords p', mat n K x i j = 0) := by
  have hNN : mat n K (nsElt (K := K) p) * mat n K (nsElt p') =
      mat n K (nsElt p') * mat n K (nsElt p) := by
    rw [← map_mul, ← map_mul, (commute_nsElt_of_ne hpp).eq]
  have hM : mat n K x * (mat n K (nsElt p) * mat n K (nsElt p')) =
      mat n K (nsElt p) * mat n K (nsElt p') * mat n K x := by
    simpa only [map_mul] using congrArg (mat n K) hx
  have hM' : mat n K x * (mat n K (nsElt p') * mat n K (nsElt p)) =
      mat n K (nsElt p') * mat n K (nsElt p) * mat n K x := by
    rw [← hNN, hM]
  obtain ⟨hW, hB⟩ := mat_commute_nsElt_mul_aux hpp hM
  obtain ⟨-, hB'⟩ := mat_commute_nsElt_mul_aux (Ne.symm hpp) hM'
  set M := mat n K x with hMdef
  obtain ⟨r1, r2⟩ := hB p (Or.inl rfl)
  obtain ⟨r3, r4⟩ := hB p' (Or.inr rfl)
  obtain ⟨r5, r6⟩ := hB' p (Or.inr rfl)
  obtain ⟨r7, r8⟩ := hB' p' (Or.inl rfl)
  have key : ∀ j, M (Sum.inl p) (Sum.inl p) * (1 * M (Sum.inr p) j) +
      M (Sum.inr p) (Sum.inl p) * (-1 * M (Sum.inl p) j) +
      (M (Sum.inl p') (Sum.inl p) * (1 * M (Sum.inr p') j) +
        M (Sum.inr p') (Sum.inl p) * (-1 * M (Sum.inl p') j)) = gram K n (Sum.inl p) j := by
    intro j
    have h := congrFun (congrFun (mat_transpose_mul_gram_mul x) (Sum.inl p)) j
    rw [← hMdef] at h
    rw [transpose_mul_gram_mul_apply, sum_eq_of_support_planes hpp _ (fun c hc hc' => by
      rw [(hW c hc hc' _ (inl_mem_coords p)).1, zero_mul])] at h
    simpa only [sgn_inl, sgn_inr, par_inl, par_inr] using h
  have e1 := key (Sum.inr p)
  have e2 := key (Sum.inl p')
  have e3 := key (Sum.inr p')
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, par_inl, ite_eq_left rfl,
    sgn_inl] at e1
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, par_inl,
    ite_eq_right Sum.inl_ne_inr] at e2
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply, par_inl,
    ite_eq_right (fun h => hpp (Sum.inr.inj h).symm)] at e3
  rw [r1, r2, r3, r4] at e1
  rw [r1, r3, r5, r7] at e2
  rw [r1, r3, r6, r8] at e3
  rcases q2_monomial_of_relations hK (a := M (Sum.inl p) (Sum.inl p))
      (b := M (Sum.inl p) (Sum.inr p)) (c := M (Sum.inl p') (Sum.inl p))
      (d := M (Sum.inl p') (Sum.inr p)) (a' := M (Sum.inl p) (Sum.inl p'))
      (b' := M (Sum.inl p) (Sum.inr p')) (c' := M (Sum.inl p') (Sum.inl p'))
      (d' := M (Sum.inl p') (Sum.inr p')) (by linear_combination e1) (by linear_combination e2)
      (by linear_combination e3) with ⟨ha', hb', hc, hd⟩ | ⟨ha, hb, hc', hd'⟩
  · left
    intro i hi j hj
    rcases mem_coords.1 hi with rfl | rfl <;> rcases mem_coords.1 hj with rfl | rfl <;>
      simp [r3, r4, r5, r6, ha', hb', hc, hd]
  · right
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · rcases mem_coords.1 hi with rfl | rfl <;> rcases mem_coords.1 hj with rfl | rfl <;>
        simp [r1, r2, ha, hb]
    · rcases mem_coords.1 hi with rfl | rfl <;> rcases mem_coords.1 hj with rfl | rfl <;>
        simp [r7, r8, hc', hd']

theorem commute_nsElt_of_commute_nsElt_mul_of_block (hpp : p ≠ p') {y : StatedSp n K}
    (hy : y * (nsElt p * nsElt p') = (nsElt p * nsElt p') * y)
    (h1 : ∀ t ∈ coords p, ∀ r, r ∉ coords p → mat n K y t r = 0)
    (h2 : ∀ t ∈ coords p, ∀ r, r ∉ coords p → mat n K y r t = 0) :
    y * nsElt p = nsElt p * y := by
  have hNN : mat n K (nsElt (K := K) p) * mat n K (nsElt p') =
      mat n K (nsElt p') * mat n K (nsElt p) := by
    rw [← map_mul, ← map_mul, (commute_nsElt_of_ne hpp).eq]
  have hY : mat n K y * (mat n K (nsElt p) * mat n K (nsElt p')) =
      mat n K (nsElt p) * mat n K (nsElt p') * mat n K y := by
    simpa only [map_mul] using congrArg (mat n K) hy
  apply mat_injective
  rw [map_mul, map_mul]
  ext a b
  by_cases hb : b ∈ coords p
  · have e1 : (mat n K y * mat n K (nsElt p)) a b =
        (mat n K y * (mat n K (nsElt p) * mat n K (nsElt p'))) a b := by
      rw [← Matrix.mul_assoc,
        mul_mat_nsElt_apply_of_not_mem _ _ (not_mem_coords_of_mem_coords hpp hb)]
    have e2 : (mat n K (nsElt p) * mat n K (nsElt p') * mat n K y) a b =
        (mat n K (nsElt p) * mat n K y) a b := by
      rw [hNN, Matrix.mul_assoc]
      by_cases ha : a ∈ coords p'
      · have ha' : a ∉ coords p := not_mem_coords_of_mem_coords (Ne.symm hpp) ha
        rw [mat_nsElt_mul_apply _ ha,
          mat_nsElt_mul_apply_of_not_mem _
            (not_mem_coords_of_mem_coords (Ne.symm hpp) (inl_mem_coords p')),
          mat_nsElt_mul_apply_of_not_mem _
            (not_mem_coords_of_mem_coords (Ne.symm hpp) (inr_mem_coords p')),
          mat_nsElt_mul_apply_of_not_mem _ ha',
          h2 b hb _ (not_mem_coords_of_mem_coords (Ne.symm hpp) (inl_mem_coords p')),
          h2 b hb _ (not_mem_coords_of_mem_coords (Ne.symm hpp) (inr_mem_coords p')),
          h2 b hb a ha']
        ring
      · rw [mat_nsElt_mul_apply_of_not_mem _ ha]
    rw [e1, hY, e2]
  · rw [mul_mat_nsElt_apply_of_not_mem _ _ hb]
    by_cases ha : a ∈ coords p
    · rw [mat_nsElt_mul_apply _ ha, h1 _ (inl_mem_coords p) b hb, h1 _ (inr_mem_coords p) b hb,
        h1 a ha b hb]
      ring
    · rw [mat_nsElt_mul_apply_of_not_mem _ ha]

theorem sq_block_of_commute_nsElt_mul [CharP K 2] (hK : Nat.card K = 2) (hpp : p ≠ p')
    {k : StatedSp n K} (hk : k * (nsElt p * nsElt p') = (nsElt p * nsElt p') * k) :
    (∀ t ∈ coords p, ∀ r, r ∉ coords p → mat n K (k ^ 2) t r = 0) ∧
      (∀ t ∈ coords p, ∀ r, r ∉ coords p → mat n K (k ^ 2) r t = 0) := by
  have hNN : mat n K (nsElt (K := K) p) * mat n K (nsElt p') =
      mat n K (nsElt p') * mat n K (nsElt p) := by
    rw [← map_mul, ← map_mul, (commute_nsElt_of_ne hpp).eq]
  have hM : mat n K k * (mat n K (nsElt p) * mat n K (nsElt p')) =
      mat n K (nsElt p) * mat n K (nsElt p') * mat n K k := by
    simpa only [map_mul] using congrArg (mat n K) hk
  have hM' : mat n K k * (mat n K (nsElt p') * mat n K (nsElt p)) =
      mat n K (nsElt p') * mat n K (nsElt p) * mat n K k := by
    rw [← hNN, hM]
  obtain ⟨hW, -⟩ := mat_commute_nsElt_mul_aux hpp hM
  obtain ⟨hW', -⟩ := mat_commute_nsElt_mul_aux (Ne.symm hpp) hM'
  have hmon := monomial_of_commute_nsElt_mul hK hpp hk
  rw [pow_two, map_mul]
  refine ⟨fun t ht r hr => ?_, fun t ht r hr => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : s ∈ coords p
    · by_cases hr' : r ∈ coords p'
      · rcases hmon with hD | ⟨hA, -⟩
        · rw [(hD s hs r hr').1, mul_zero]
        · rw [hA t ht s hs, zero_mul]
      · rw [(hW r hr hr' s hs).2, mul_zero]
    · by_cases hs' : s ∈ coords p'
      · rcases hmon with hD | ⟨-, hA⟩
        · rw [(hD t ht s hs').1, zero_mul]
        · by_cases hr' : r ∈ coords p'
          · rw [hA s hs' r hr', mul_zero]
          · rw [(hW' r hr' hr s hs').2, mul_zero]
      · rw [(hW s hs hs' t ht).2, zero_mul]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : s ∈ coords p
    · by_cases hr' : r ∈ coords p'
      · rcases hmon with hD | ⟨hA, -⟩
        · rw [(hD s hs r hr').2, zero_mul]
        · rw [hA s hs t ht, mul_zero]
      · rw [(hW r hr hr' s hs).1, zero_mul]
    · by_cases hs' : s ∈ coords p'
      · rcases hmon with hD | ⟨-, hA⟩
        · rw [(hD t ht s hs').2, mul_zero]
        · by_cases hr' : r ∈ coords p'
          · rw [hA r hr' s hs', zero_mul]
          · rw [(hW' r hr' hr s hs').1, zero_mul]
      · rw [(hW s hs hs' t ht).1, mul_zero]

theorem commute_nsElt_sq_of_commute_nsElt_mul [CharP K 2] (hK : Nat.card K = 2) (hpp : p ≠ p')
    {k : StatedSp n K} (hk : k * (nsElt p * nsElt p') = (nsElt p * nsElt p') * k) :
    k ^ 2 * nsElt p = nsElt p * k ^ 2 := by
  obtain ⟨h1, h2⟩ := sq_block_of_commute_nsElt_mul hK hpp hk
  exact commute_nsElt_of_commute_nsElt_mul_of_block hpp
    ((show Commute k (nsElt p * nsElt p') from hk).pow_left 2).eq h1 h2

end Commute

end CFSG.SeitzReduction.SymplecticPilot
