module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSpinMat
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits SpinRank
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrth

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

noncomputable def ubarD (hn : 3 ≤ n) (k : Fin n) : spinGroup (quadPlus n F) :=
  rootD F hn k (.ofAdd 1) * negRootD F hn k (.ofAdd 1)

theorem spinMatrix_ubarD (hn : 3 ≤ n) (k : Fin n) :
    (spinMatrix (quadPlus n F) (ubarD hn k) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + nodeN F (Sum.inl (rootIdxD n k)) (Sum.inr (rootIdxD n k))
        (ix (rootIdxD' n k) (!rootSignD n k)) (ix (rootIdxD' n k) (rootSignD n k)) := by
  rw [ubarD, map_mul, Units.val_mul, spinMatrix_rootD hn, spinMatrix_negRootD hn]
  exact ubar_matrix_aux (distinct4_node hn k)

theorem rk1_ubarD (hn : 3 ≤ n) (k : Fin n) :
    rk1 (spinMatrix (quadPlus n F) (ubarD hn k) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 4 := by
  unfold rk1
  rw [spinMatrix_ubarD hn k, add_sub_cancel_left]
  exact rank_nodeN (distinct4_node hn k)

theorem sl2_cube : (upperSL2 (1 : F) * lowerSL2 1) ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [pow_three]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  have e1 : ((upperSL2 (1 : F) : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 1; 0, 1] := rfl
  have e2 : ((lowerSL2 (1 : F) : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; 1, 1] := rfl
  rw [e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem ubarD_pow_three (hn : 3 ≤ n) (k : Fin n) : (ubarD (F := F) hn k) ^ 3 = 1 := by
  have : ubarD (F := F) hn k = rankOneD F hn k (upperSL2 1 * lowerSL2 1) := by
    rw [map_mul, rankOneD_upperSL2, rankOneD_lowerSL2]; rfl
  rw [this, ← map_pow, sl2_cube, map_one]

theorem ubarD_ne_one (hn : 3 ≤ n) (k : Fin n) : ubarD (F := F) hn k ≠ 1 := by
  intro h
  have := rk1_ubarD (F := F) hn k
  rw [h, map_one, Units.val_one] at this
  simp [rk1] at this

theorem eq_zero_or_one_of_card_two (hF : Nat.card F = 2) (c : F) : c = 0 ∨ c = 1 := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
  by_cases hc : c = 0
  · exact Or.inl hc
  · exact Or.inr ((hy c hc).trans (hy 1 one_ne_zero).symm)

theorem hom_pow_three (φ : Multiplicative F →* spinGroup (quadPlus n F)) (c : F) :
    φ (.ofAdd c) ^ 3 = φ (.ofAdd c) := by
  have h3 : (3 : F) = 1 := by
    rw [show (3 : F) = 2 + 1 by norm_num, CharTwo.two_eq_zero, zero_add]
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul]
  simp [h3]

theorem mul_eq_ubarD (hF : Nat.card F = 2) (hn : 3 ≤ n) (k : Fin n)
    {x y : spinGroup (quadPlus n F)} (hx : x ∈ (rootD F hn k).range)
    (hy : y ∈ (negRootD F hn k).range) (h3 : (x * y) ^ 3 = 1) (h1 : x * y ≠ 1) :
    x * y = ubarD hn k := by
  obtain ⟨cx, rfl⟩ := hx
  obtain ⟨cy, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective cx
  obtain ⟨d, rfl⟩ := Multiplicative.ofAdd.surjective cy
  rcases eq_zero_or_one_of_card_two hF c with rfl | rfl <;>
    rcases eq_zero_or_one_of_card_two hF d with rfl | rfl
  · exact absurd (by simp) h1
  · simp only [ofAdd_zero, map_one, one_mul] at h3 h1 ⊢
    rw [hom_pow_three] at h3
    exact absurd h3 h1
  · simp only [ofAdd_zero, map_one, mul_one] at h3 h1 ⊢
    rw [hom_pow_three] at h3
    exact absurd h3 h1
  · rfl

theorem zpow_cases {G : Type*} [Group G] {u : G} (h : u ^ 3 = 1) (m : ℤ) :
    u ^ m = 1 ∨ u ^ m = u ∨ u ^ m = u⁻¹ := by
  obtain ⟨q, r, hm, hr0, hr3⟩ : ∃ q r : ℤ, m = 3 * q + r ∧ 0 ≤ r ∧ r < 3 :=
    ⟨m / 3, m % 3, by omega, by omega, by omega⟩
  have hq : u ^ (3 * q) = 1 := by
    rw [zpow_mul]
    simp [h]
  have : u ^ m = u ^ r := by rw [hm, zpow_add, hq, one_mul]
  rw [this]
  obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  · left; simp
  · right; left; simp
  · right; right
    have : u * u ^ 2 = 1 := by rw [← pow_succ']; exact h
    simp only [zpow_ofNat]
    exact (eq_inv_of_mul_eq_one_right this).symm.symm

theorem rk1_conj_zpow_ubarD (hn : 3 ≤ n) (k : Fin n) (m : ℤ) (g : spinGroup (quadPlus n F)) :
    rk1 (spinMatrix (quadPlus n F) (g * ubarD hn k ^ m * g⁻¹) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 0 ∨
    rk1 (spinMatrix (quadPlus n F) (g * ubarD hn k ^ m * g⁻¹) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 4 := by
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, map_inv, rk1_conj]
  rcases zpow_cases (ubarD_pow_three (F := F) hn k) m with h | h | h
  · left
    rw [h, map_one, Units.val_one]
    simp [rk1]
  · right
    rw [h]
    exact rk1_ubarD hn k
  · right
    rw [h, map_inv, rk1_inv]
    exact rk1_ubarD hn k

theorem rk1_zpow_ubarD (hn : 3 ≤ n) (k : Fin n) (m : ℤ) :
    rk1 (spinMatrix (quadPlus n F) (ubarD hn k ^ m) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 0 ∨
    rk1 (spinMatrix (quadPlus n F) (ubarD hn k ^ m) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 4 := by
  have := rk1_conj_zpow_ubarD (F := F) hn k m 1
  simpa using this

theorem val_spec (hn : 3 ≤ n) (k : Fin n) :
    (k.val + 1 < n ∧ (rootIdxD n k).val = k.val ∧ rootSignD n k = false) ∨
      (¬ k.val + 1 < n ∧ (rootIdxD n k).val = n - 2 ∧ rootSignD n k = true) := by
  by_cases h : k.val + 1 < n
  · left
    exact ⟨h, by rw [rootIdxD_of_lt n h], rootSignD_of_lt n h⟩
  · right
    exact ⟨h, val_rootIdxD_of_not_lt n h, rootSignD_of_not_lt n h⟩

theorem orth_cases (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (hc : cartanD n i j = 0) :
    ((rootIdxD n i).val + 2 ≤ (rootIdxD n j).val ∨ (rootIdxD n j).val + 2 ≤ (rootIdxD n i).val) ∨
      (rootIdxD n i = rootIdxD n j ∧ rootSignD n i = !rootSignD n j) := by
  simp only [cartanD, Matrix.of_apply, if_neg hij] at hc
  have hadj : ¬ ((i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
      (i.val + 3 = n ∧ j.val + 1 = n) ∨ (j.val + 3 = n ∧ i.val + 1 = n)) := by
    intro h
    rw [if_pos h] at hc
    norm_num at hc
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases val_spec hn i with ⟨hi1, hi2, hi3⟩ | ⟨hi1, hi2, hi3⟩ <;>
    rcases val_spec hn j with ⟨hj1, hj2, hj3⟩ | ⟨hj1, hj2, hj3⟩
  · left; omega
  · rcases Nat.lt_or_ge (i.val + 3) n with h | h
    · left; omega
    · right
      refine ⟨Fin.ext (by omega), by rw [hi3, hj3]; rfl⟩
  · rcases Nat.lt_or_ge (j.val + 3) n with h | h
    · left; omega
    · right
      refine ⟨Fin.ext (by omega), by rw [hi3, hj3]; rfl⟩
  · exact absurd (Fin.ext (by omega)) hij

theorem ix_cases (q : Fin n) (b : Bool) : ix q b = Sum.inl q ∨ ix q b = Sum.inr q := by
  cases b <;> simp [ix]

theorem mem_nodeS_node (hn : 3 ≤ n) (k : Fin n) {x : Fin n ⊕ Fin n}
    (hx : x ∈ nodeS (Sum.inl (rootIdxD n k) : Fin n ⊕ Fin n) (Sum.inr (rootIdxD n k))
      (ix (rootIdxD' n k) (!rootSignD n k)) (ix (rootIdxD' n k) (rootSignD n k))) :
    ∃ m : Fin n, (m.val = (rootIdxD n k).val ∨ m.val = (rootIdxD n k).val + 1) ∧
      (x = Sum.inl m ∨ x = Sum.inr m) := by
  have hq := val_rootIdxD' n (by omega) k
  simp only [nodeS, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨_, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨_, Or.inl rfl, Or.inr rfl⟩
  · rcases ix_cases (rootIdxD' n k) (!rootSignD n k) with h | h <;> rw [h]
    · exact ⟨_, Or.inr hq, Or.inl rfl⟩
    · exact ⟨_, Or.inr hq, Or.inr rfl⟩
  · rcases ix_cases (rootIdxD' n k) (rootSignD n k) with h | h <;> rw [h]
    · exact ⟨_, Or.inr hq, Or.inl rfl⟩
    · exact ⟨_, Or.inr hq, Or.inr rfl⟩

theorem disjoint_nodeS (hn : 3 ≤ n) {i j : Fin n}
    (h : (rootIdxD n i).val + 2 ≤ (rootIdxD n j).val ∨
      (rootIdxD n j).val + 2 ≤ (rootIdxD n i).val) :
    Disjoint (nodeS (Sum.inl (rootIdxD n i) : Fin n ⊕ Fin n) (Sum.inr (rootIdxD n i))
      (ix (rootIdxD' n i) (!rootSignD n i)) (ix (rootIdxD' n i) (rootSignD n i)))
      (nodeS (Sum.inl (rootIdxD n j) : Fin n ⊕ Fin n) (Sum.inr (rootIdxD n j))
      (ix (rootIdxD' n j) (!rootSignD n j)) (ix (rootIdxD' n j) (rootSignD n j))) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨m, hm, hxm⟩ := mem_nodeS_node hn i hx
  obtain ⟨m', hm', hxm'⟩ := mem_nodeS_node hn j hx'
  have : m = m' := by
    rcases hxm with rfl | rfl <;> rcases hxm' with h1 | h1 <;>
      first | exact Sum.inl_injective h1 | exact Sum.inr_injective h1 | cases h1
  subst this
  omega

theorem rk1_pair_ne (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (hc : cartanD n i j = 0) :
    rk1 (spinMatrix (quadPlus n F) (ubarD hn i * ubarD hn j) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ≠ 0 ∧
    rk1 (spinMatrix (quadPlus n F) (ubarD hn i * ubarD hn j) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ≠ 4 := by
  have hmat : (spinMatrix (quadPlus n F) (ubarD hn i * ubarD hn j) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1 =
      nodeN F (Sum.inl (rootIdxD n i)) (Sum.inr (rootIdxD n i))
        (ix (rootIdxD' n i) (!rootSignD n i)) (ix (rootIdxD' n i) (rootSignD n i)) +
      nodeN F (Sum.inl (rootIdxD n j)) (Sum.inr (rootIdxD n j))
        (ix (rootIdxD' n j) (!rootSignD n j)) (ix (rootIdxD' n j) (rootSignD n j)) +
      nodeN F (Sum.inl (rootIdxD n i)) (Sum.inr (rootIdxD n i))
        (ix (rootIdxD' n i) (!rootSignD n i)) (ix (rootIdxD' n i) (rootSignD n i)) *
      nodeN F (Sum.inl (rootIdxD n j)) (Sum.inr (rootIdxD n j))
        (ix (rootIdxD' n j) (!rootSignD n j)) (ix (rootIdxD' n j) (rootSignD n j)) := by
    rw [map_mul, Units.val_mul, spinMatrix_ubarD hn i, spinMatrix_ubarD hn j]
    noncomm_ring
  unfold rk1
  rw [hmat]
  rcases orth_cases hn hij hc with hsep | ⟨hp, ht⟩
  · have hd := disjoint_nodeS hn hsep
    rw [nodeN_mul_nodeN_disjoint (F := F) hd, add_zero]
    have := rank_add_nodeN_disjoint (F := F) (distinct4_node hn i) (distinct4_node hn j) hd
    omega
  · have hq : rootIdxD' n j = rootIdxD' n i := by
      refine Fin.ext ?_
      rw [val_rootIdxD' n (by omega) i, val_rootIdxD' n (by omega) j, hp]
    have ht' : rootSignD n j = !rootSignD n i := by rw [ht]; simp
    rw [← hp, hq, ht', Bool.not_not]
    have h1 := rank_swap_le (F := F) (distinct4_node hn i)
    have h2 := rank_swap_pos (F := F) (distinct4_node hn i)
    omega

theorem mem_rootGroup_ubarD_left (hn : 3 ≤ n) (k : Fin n) :
    rootD F hn k (.ofAdd 1) ∈ (plusDatum n F hn).rootGroup (Pi.single k 1) := by
  show _ ∈ plusRootGroup n F hn (Pi.single k 1)
  rw [plusRootGroup_single]
  exact ⟨_, rfl⟩

theorem mem_rootGroup_ubarD_right (hn : 3 ≤ n) (k : Fin n) :
    negRootD F hn k (.ofAdd 1) ∈ (plusDatum n F hn).rootGroup (-Pi.single k 1) := by
  show _ ∈ plusRootGroup n F hn (-Pi.single k 1)
  rw [plusRootGroup_neg_single]
  exact ⟨_, rfl⟩

theorem mem_range_rootD_of_mem (hn : 3 ≤ n) (k : Fin n) {x : spinGroup (quadPlus n F)}
    (hx : x ∈ (plusDatum n F hn).rootGroup (Pi.single k 1)) : x ∈ (rootD F hn k).range := by
  rw [← plusRootGroup_single]
  exact hx

theorem mem_range_negRootD_of_mem (hn : 3 ≤ n) (k : Fin n) {x : spinGroup (quadPlus n F)}
    (hx : x ∈ (plusDatum n F hn).rootGroup (-Pi.single k 1)) : x ∈ (negRootD F hn k).range := by
  rw [← plusRootGroup_neg_single]
  exact hx

theorem spin_orth (hF : Nat.card F = 2) (hn : 3 ≤ n) (i j : Fin n) (hij : i ≠ j)
    (hcart : (plusDatum n F hn).cartan i j = 0) :
    ∃ xi ∈ (plusDatum n F hn).rootGroup (Pi.single i 1),
    ∃ yi ∈ (plusDatum n F hn).rootGroup (-Pi.single i 1),
    ∃ xj ∈ (plusDatum n F hn).rootGroup (Pi.single j 1),
    ∃ yj ∈ (plusDatum n F hn).rootGroup (-Pi.single j 1),
      (xi * yi) ^ 3 = 1 ∧ xi * yi ≠ 1 ∧ (xj * yj) ^ 3 = 1 ∧ xj * yj ≠ 1 ∧
      xj * yj ∉ Subgroup.zpowers (xi * yi) ∧
      ∀ k, ∀ x ∈ (plusDatum n F hn).rootGroup (Pi.single k 1),
        ∀ y ∈ (plusDatum n F hn).rootGroup (-Pi.single k 1),
        (x * y) ^ 3 = 1 → x * y ≠ 1 → ∀ g : spinGroup (quadPlus n F),
          ∀ e : ℕ, g * (x * y) ^ e * g⁻¹ ≠ xi * yi * (xj * yj) := by
  have hc : cartanD n i j = 0 := hcart
  have hpair := rk1_pair_ne (F := F) hn hij hc
  refine ⟨rootD F hn i (.ofAdd 1), mem_rootGroup_ubarD_left hn i,
    negRootD F hn i (.ofAdd 1), mem_rootGroup_ubarD_right hn i,
    rootD F hn j (.ofAdd 1), mem_rootGroup_ubarD_left hn j,
    negRootD F hn j (.ofAdd 1), mem_rootGroup_ubarD_right hn j,
    ubarD_pow_three hn i, ubarD_ne_one hn i, ubarD_pow_three hn j, ubarD_ne_one hn j, ?_, ?_⟩
  · intro hmem
    change ubarD (F := F) hn j ∈ Subgroup.zpowers (ubarD hn i) at hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : ubarD (F := F) hn i * ubarD hn j = ubarD hn i ^ (1 + m) := by
      rw [zpow_one_add, hm]
    rcases rk1_zpow_ubarD (F := F) hn i (1 + m) with h | h
    · rw [← h1] at h; exact hpair.1 h
    · rw [← h1] at h; exact hpair.2 h
  · intro (k : Fin n) x hx y hy h3 h1' g e he
    have hx' : x ∈ (rootD F hn k).range := mem_range_rootD_of_mem hn k hx
    have hy' : y ∈ (negRootD F hn k).range := mem_range_negRootD_of_mem hn k hy
    rw [mul_eq_ubarD hF hn k hx' hy' h3 h1'] at he
    change g * ubarD hn k ^ e * g⁻¹ = ubarD hn i * ubarD hn j at he
    have := rk1_conj_zpow_ubarD (F := F) hn k (e : ℤ) g
    rw [zpow_natCast, he] at this
    rcases this with h | h
    · exact hpair.1 h
    · exact hpair.2 h

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
