module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2SwapOverlap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeGen

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic (equivStatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective elt mat_elt E)
open TauCeti.GLSymplecticFin
open scoped commutatorElement

variable {K : Type} [Field K] {n : ℕ}

theorem exists_ne_ne_of_three_planes {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j : Fin n) : ∃ k, (k = a ∨ k = b ∨ k = c) ∧ k ≠ i ∧ k ≠ j := by
  by_cases h1 : a ≠ i ∧ a ≠ j
  · exact ⟨a, Or.inl rfl, h1⟩
  by_cases h2 : b ≠ i ∧ b ≠ j
  · exact ⟨b, Or.inr (Or.inl rfl), h2⟩
  refine ⟨c, Or.inr (Or.inr rfl), ?_, ?_⟩
  · rintro rfl
    simp only [ne_eq, not_and_or, not_not] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hac h1
    · exact hac h1
    · exact hbc h2
    · exact hab (h1.trans h2.symm)
  · rintro rfl
    simp only [ne_eq, not_and_or, not_not] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hab (h1.trans h2.symm)
    · exact hbc h2
    · exact hac h1
    · exact hac h1

theorem spBlock_compl_pair_sup_sup_eq_top (hn : 4 ≤ n) {a b c : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    spBlock K ({a, b}ᶜ : Finset (Fin n)) ⊔ spBlock K ({a, c}ᶜ : Finset (Fin n)) ⊔
      spBlock K ({b, c}ᶜ : Finset (Fin n)) = ⊤ := by
  set H := spBlock K ({a, b}ᶜ : Finset (Fin n)) ⊔ spBlock K ({a, c}ᶜ : Finset (Fin n)) ⊔
      spBlock K ({b, c}ᶜ : Finset (Fin n)) with hH
  have hA : spBlock K ({a}ᶜ : Finset (Fin n)) ≤ H :=
    (spBlock_compl_singleton_le_sup hn hab hac hbc).trans
      (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left))
  have hB : spBlock K ({b}ᶜ : Finset (Fin n)) ≤ H := by
    have h := spBlock_compl_singleton_le_sup (F := K) hn hab.symm hbc hac
    rw [Finset.pair_comm b a] at h
    exact h.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  have hC : spBlock K ({c}ᶜ : Finset (Fin n)) ≤ H := by
    have h := spBlock_compl_singleton_le_sup (F := K) hn hac.symm hbc.symm hab
    rw [Finset.pair_comm c a, Finset.pair_comm c b] at h
    exact h.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  refine eq_top_of_adjacent_of_long_statedSp H b (fun i j hij x _ => ?_) (fun x => ?_)
    (fun x => ?_)
  · obtain ⟨k, hk, hki, hkj⟩ := exists_ne_ne_of_three_planes hab hac hbc i j
    have hmem : elt (.difference i j hij) x ∈ spBlock K ({k}ᶜ : Finset (Fin n)) :=
      elt_difference_mem_spBlock hij (mem_compl_singleton_iff'.2 (Ne.symm hki))
        (mem_compl_singleton_iff'.2 (Ne.symm hkj)) x
    rcases hk with rfl | rfl | rfl
    · exact hA hmem
    · exact hB hmem
    · exact hC hmem
  · exact hA (elt_positiveLong_mem_spBlock (mem_compl_singleton_iff'.2 hab.symm) x)
  · exact hA (elt_negativeLong_mem_spBlock (mem_compl_singleton_iff'.2 hab.symm) x)

theorem elt_positiveSum_mem_spBlock {N : Finset (Fin n)} {i j : Fin n} (hij : i < j)
    (hi : i ∈ N) (hj : j ∈ N) (c : K) : elt (.positiveSum i j hij) c ∈ spBlock K N := by
  intro a b hab
  have hi' : (Sum.inl i : Fin n ⊕ Fin n) ∈ planeCoords N := hi
  have hj' : (Sum.inl j : Fin n ⊕ Fin n) ∈ planeCoords N := hj
  have hi'' : (Sum.inr i : Fin n ⊕ Fin n) ∈ planeCoords N := hi
  have hj'' : (Sum.inr j : Fin n ⊕ Fin n) ∈ planeCoords N := hj
  rw [mat_elt]
  simp only [E, Matrix.add_apply, Matrix.smul_apply,
    single_apply_eq_zero_of_mem_planeCoords hi' hj'' hab,
    single_apply_eq_zero_of_mem_planeCoords hj' hi'' hab, add_zero, smul_zero]

theorem elt_negativeSum_mem_spBlock {N : Finset (Fin n)} {i j : Fin n} (hij : i < j)
    (hi : i ∈ N) (hj : j ∈ N) (c : K) : elt (.negativeSum i j hij) c ∈ spBlock K N := by
  intro a b hab
  have hi' : (Sum.inl i : Fin n ⊕ Fin n) ∈ planeCoords N := hi
  have hj' : (Sum.inl j : Fin n ⊕ Fin n) ∈ planeCoords N := hj
  have hi'' : (Sum.inr i : Fin n ⊕ Fin n) ∈ planeCoords N := hi
  have hj'' : (Sum.inr j : Fin n ⊕ Fin n) ∈ planeCoords N := hj
  rw [mat_elt]
  simp only [E, Matrix.add_apply, Matrix.smul_apply,
    single_apply_eq_zero_of_mem_planeCoords hi'' hj' hab,
    single_apply_eq_zero_of_mem_planeCoords hj'' hi' hab, add_zero, smul_zero]

theorem equivStatedSp_positiveLong_mem_spBlock {N : Finset (Fin n)} {k : Fin n} (hk : k ∈ N)
    (c : K) : equivStatedSp n K (positiveLongRootTransvectionUnit k c) ∈ spBlock K N := by
  have e : equivStatedSp n K (positiveLongRootTransvectionUnit k c) = elt (.positiveLong k) c := by
    simp only [elt, RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply,
      toAdd_ofAdd]
  rw [e]
  exact elt_positiveLong_mem_spBlock hk c

theorem equivStatedSp_negativeLong_mem_spBlock {N : Finset (Fin n)} {k : Fin n} (hk : k ∈ N)
    (c : K) : equivStatedSp n K (negativeLongRootTransvectionUnit k c) ∈ spBlock K N := by
  have e : equivStatedSp n K (negativeLongRootTransvectionUnit k c) = elt (.negativeLong k) c := by
    simp only [elt, RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply,
      toAdd_ofAdd]
  rw [e]
  exact elt_negativeLong_mem_spBlock hk c

theorem equivStatedSp_difference_mem_spBlock {N : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (hi : i ∈ N) (hj : j ∈ N) (c : K) :
    equivStatedSp n K (differenceShortRootUnit hij c) ∈ spBlock K N := by
  have e : equivStatedSp n K (differenceShortRootUnit hij c) = elt (.difference i j hij) c := by
    simp only [elt, RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd]
  rw [e]
  exact elt_difference_mem_spBlock hij hi hj c

theorem equivStatedSp_positiveSum_mem_spBlock {N : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (hi : i ∈ N) (hj : j ∈ N) (c : K) :
    equivStatedSp n K (positiveSumShortRootUnit hij c) ∈ spBlock K N := by
  rcases lt_or_gt_of_ne hij with h | h
  · have e : equivStatedSp n K (positiveSumShortRootUnit hij c) = elt (.positiveSum i j h) c := by
      simp only [elt, RootSubgroupIndex.hom_positiveSum, positiveSumShortRootHom_apply,
        toAdd_ofAdd]
    rw [e]
    exact elt_positiveSum_mem_spBlock h hi hj c
  · have hsw : positiveSumShortRootUnit hij c = positiveSumShortRootUnit hij.symm c := by
      have h1 := positiveSumShortRootHom_apply hij (Multiplicative.ofAdd c)
      have h2 := positiveSumShortRootHom_apply hij.symm (Multiplicative.ofAdd c)
      rw [toAdd_ofAdd] at h1 h2
      rw [← h1, ← h2, positiveSumShortRootHom_swap hij]
    have e : equivStatedSp n K (positiveSumShortRootUnit hij c) = elt (.positiveSum j i h) c := by
      rw [hsw]
      simp only [elt, RootSubgroupIndex.hom_positiveSum, positiveSumShortRootHom_apply,
        toAdd_ofAdd]
    rw [e]
    exact elt_positiveSum_mem_spBlock h hj hi c

theorem equivStatedSp_negativeSum_mem_spBlock {N : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (hi : i ∈ N) (hj : j ∈ N) (c : K) :
    equivStatedSp n K (negativeSumShortRootUnit hij c) ∈ spBlock K N := by
  rcases lt_or_gt_of_ne hij with h | h
  · have e : equivStatedSp n K (negativeSumShortRootUnit hij c) = elt (.negativeSum i j h) c := by
      simp only [elt, RootSubgroupIndex.hom_negativeSum, negativeSumShortRootHom_apply,
        toAdd_ofAdd]
    rw [e]
    exact elt_negativeSum_mem_spBlock h hi hj c
  · have hsw : negativeSumShortRootUnit hij c = negativeSumShortRootUnit hij.symm c := by
      have h1 := negativeSumShortRootHom_apply hij (Multiplicative.ofAdd c)
      have h2 := negativeSumShortRootHom_apply hij.symm (Multiplicative.ofAdd c)
      rw [toAdd_ofAdd] at h1 h2
      rw [← h1, ← h2, negativeSumShortRootHom_swap hij]
    have e : equivStatedSp n K (negativeSumShortRootUnit hij c) = elt (.negativeSum j i h) c := by
      rw [hsw]
      simp only [elt, RootSubgroupIndex.hom_negativeSum, negativeSumShortRootHom_apply,
        toAdd_ofAdd]
    rw [e]
    exact elt_negativeSum_mem_spBlock h hj hi c

theorem commute_of_equivStatedSp_mem_spBlock {I J : Finset (Fin n)} (h : Disjoint I J)
    {u v : TauCeti.GLSymplecticFin n K} (hu : equivStatedSp n K u ∈ spBlock K I)
    (hv : equivStatedSp n K v ∈ spBlock K J) : Commute u v := by
  show u * v = v * u
  apply (equivStatedSp n K).injective
  rw [map_mul, map_mul]
  exact (commute_of_mem_spBlock_of_disjoint h hu hv).eq

theorem commutatorElement_mul_mul_of_commute_aux {M : Type*} [Group M] {x x' y y' : M}
    (h1 : Commute x' y) (h2 : Commute x' y') (h3 : Commute y' x) :
    ⁅x * x', y * y'⁆ = ⁅x, y⁆ := by
  have h4 : x' * (y * y') * x'⁻¹ = y * y' := by
    rw [(h1.mul_right h2).eq, mul_inv_cancel_right]
  have h5 : y' * x⁻¹ * y'⁻¹ = x⁻¹ := by
    rw [h3.inv_right.eq, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc x * x' * (y * y') * (x * x')⁻¹ * (y * y')⁻¹
      = x * (x' * (y * y') * x'⁻¹) * x⁻¹ * y'⁻¹ * y⁻¹ := by group
    _ = x * y * (y' * x⁻¹ * y'⁻¹) * y⁻¹ := by rw [h4]; group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h5]

section Local

variable [CharP K 2]

theorem commutator_posSum_negLong_one {i j : Fin n} (hij : i ≠ j) :
    ⁅positiveSumShortRootUnit (R := K) hij 1, negativeLongRootTransvectionUnit (R := K) j 1⁆ =
      differenceShortRootUnit (R := K) hij 1 * positiveLongRootTransvectionUnit (R := K) i 1 := by
  rw [commutatorElement_positiveSumShortRootUnit_negativeLongRootTransvectionUnit]
  simp only [one_mul, one_pow, CharTwo.neg_eq]

theorem commutator_negSum_posLong_one {i j : Fin n} (hij : i ≠ j) :
    ⁅negativeSumShortRootUnit (R := K) hij 1, positiveLongRootTransvectionUnit (R := K) j 1⁆ =
      differenceShortRootUnit (R := K) hij.symm 1 *
        negativeLongRootTransvectionUnit (R := K) i 1 := by
  rw [commutatorElement_negativeSumShortRootUnit_positiveLongRootTransvectionUnit]
  simp only [one_mul, one_pow, CharTwo.neg_eq]

omit [CharP K 2] in
theorem commutator_diff_posLong_one {i j : Fin n} (hij : i ≠ j) :
    ⁅differenceShortRootUnit (R := K) hij 1, positiveLongRootTransvectionUnit (R := K) j 1⁆ =
      positiveSumShortRootUnit (R := K) hij 1 * positiveLongRootTransvectionUnit (R := K) i 1 := by
  rw [commutatorElement_differenceShortRootUnit_positiveLongRootTransvectionUnit]
  simp only [one_mul, one_pow]

omit [CharP K 2] in
theorem positiveSumShortRootUnit_symm {i j : Fin n} (hij : i ≠ j) (c : K) :
    positiveSumShortRootUnit hij c = positiveSumShortRootUnit hij.symm c := by
  have h1 := positiveSumShortRootHom_apply hij (Multiplicative.ofAdd c)
  have h2 := positiveSumShortRootHom_apply hij.symm (Multiplicative.ofAdd c)
  rw [toAdd_ofAdd] at h1 h2
  rw [← h1, ← h2, positiveSumShortRootHom_swap hij]

theorem mem_pair_left' (i j : Fin n) : i ∈ ({i, j} : Finset (Fin n)) :=
  Finset.mem_insert_self i {j}

theorem mem_pair_right' (i j : Fin n) : j ∈ ({i, j} : Finset (Fin n)) :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self j)

theorem disjoint_singleton_pair {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) :
    Disjoint ({i} : Finset (Fin n)) {j, k} := by
  rw [Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hij, hik⟩

theorem disjoint_singleton_singleton {i j : Fin n} (hij : i ≠ j) :
    Disjoint ({i} : Finset (Fin n)) {j} := by
  rw [Finset.disjoint_singleton]
  exact hij

theorem mem_of_commutator_spBlock_pair_le {H : Subgroup (StatedSp n K)} {a b j : Fin n}
    (hab : a ≠ b) (haj : a ≠ j) (hbj : b ≠ j)
    (hA : ⁅spBlock K ({a, j} : Finset (Fin n)), spBlock K ({a, j} : Finset (Fin n))⁆ ≤ H)
    (hB : ⁅spBlock K ({b, j} : Finset (Fin n)), spBlock K ({b, j} : Finset (Fin n))⁆ ≤ H) :
    equivStatedSp n K (differenceShortRootUnit hab 1) ∈ H ∧
      equivStatedSp n K (positiveLongRootTransvectionUnit a 1) ∈ H ∧
      equivStatedSp n K (positiveLongRootTransvectionUnit j 1) ∈ H ∧
      equivStatedSp n K (negativeLongRootTransvectionUnit j 1) ∈ H ∧
      equivStatedSp n K (differenceShortRootUnit haj 1) ∈ H ∧
      equivStatedSp n K (differenceShortRootUnit haj.symm 1) ∈ H := by
  set φ := equivStatedSp n K with hφ
  set H' : Subgroup (TauCeti.GLSymplecticFin n K) := H.comap φ.toMonoidHom with hH'
  change _ ∈ H' ∧ _ ∈ H' ∧ _ ∈ H' ∧ _ ∈ H' ∧ _ ∈ H' ∧ _ ∈ H'
  have cA : ∀ u v, φ u ∈ spBlock K ({a, j} : Finset (Fin n)) →
      φ v ∈ spBlock K ({a, j} : Finset (Fin n)) → ⁅u, v⁆ ∈ H' := by
    intro u v hu hv
    change φ ⁅u, v⁆ ∈ H
    rw [map_commutatorElement]
    exact hA (commutator_mem_commutator hu hv)
  have cB : ∀ u v, φ u ∈ spBlock K ({b, j} : Finset (Fin n)) →
      φ v ∈ spBlock K ({b, j} : Finset (Fin n)) → ⁅u, v⁆ ∈ H' := by
    intro u v hu hv
    change φ ⁅u, v⁆ ∈ H
    rw [map_commutatorElement]
    exact hB (commutator_mem_commutator hu hv)
  have cm : ∀ {x y}, x ∈ H' → y ∈ H' → ⁅x, y⁆ ∈ H' := fun hx hy => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  set la := positiveLongRootTransvectionUnit (R := K) a 1 with hla
  set lj := positiveLongRootTransvectionUnit (R := K) j 1 with hlj
  set lb := positiveLongRootTransvectionUnit (R := K) b 1 with hlb
  set la' := negativeLongRootTransvectionUnit (R := K) a 1 with hla'
  set lj' := negativeLongRootTransvectionUnit (R := K) j 1 with hlj'
  set lb' := negativeLongRootTransvectionUnit (R := K) b 1 with hlb'
  have pA : ∀ {k : Fin n}, k = a ∨ k = j → k ∈ ({a, j} : Finset (Fin n)) := by
    rintro k (rfl | rfl)
    · exact mem_pair_left' _ _
    · exact mem_pair_right' _ _
  have pB : ∀ {k : Fin n}, k = b ∨ k = j → k ∈ ({b, j} : Finset (Fin n)) := by
    rintro k (rfl | rfl)
    · exact mem_pair_left' _ _
    · exact mem_pair_right' _ _
  have sgl : ∀ k : Fin n, k ∈ ({k} : Finset (Fin n)) := Finset.mem_singleton_self
  have cdl : ∀ {I J : Finset (Fin n)} {u v : TauCeti.GLSymplecticFin n K}, Disjoint I J →
      φ u ∈ spBlock K I → φ v ∈ spBlock K J → Commute u v :=
    fun h hu hv => commute_of_equivStatedSp_mem_spBlock h hu hv
  have mLa : φ la ∈ spBlock K ({a} : Finset (Fin n)) :=
    equivStatedSp_positiveLong_mem_spBlock (sgl a) 1
  have mLj : φ lj ∈ spBlock K ({j} : Finset (Fin n)) :=
    equivStatedSp_positiveLong_mem_spBlock (sgl j) 1
  have mLb : φ lb ∈ spBlock K ({b} : Finset (Fin n)) :=
    equivStatedSp_positiveLong_mem_spBlock (sgl b) 1
  have mLb' : φ lb' ∈ spBlock K ({b} : Finset (Fin n)) :=
    equivStatedSp_negativeLong_mem_spBlock (sgl b) 1
  have hu : differenceShortRootUnit haj 1 * la ∈ H' := by
    rw [hla, ← commutator_posSum_negLong_one haj]
    exact cA _ _ (equivStatedSp_positiveSum_mem_spBlock haj (pA (Or.inl rfl)) (pA (Or.inr rfl)) 1)
      (equivStatedSp_negativeLong_mem_spBlock (pA (Or.inr rfl)) 1)
  have hv : differenceShortRootUnit hbj.symm 1 * lb' ∈ H' := by
    rw [hlb', ← commutator_negSum_posLong_one hbj]
    exact cB _ _ (equivStatedSp_negativeSum_mem_spBlock hbj (pB (Or.inl rfl)) (pB (Or.inr rfl)) 1)
      (equivStatedSp_positiveLong_mem_spBlock (pB (Or.inr rfl)) 1)
  have hd : differenceShortRootUnit hab 1 ∈ H' := by
    have h := cm hu hv
    rw [commutatorElement_mul_mul_of_commute_aux
      (cdl (disjoint_singleton_pair haj hab) mLa
        (equivStatedSp_difference_mem_spBlock hbj.symm (mem_pair_left' j b) (mem_pair_right' j b)
          1))
      (cdl (disjoint_singleton_singleton hab) mLa mLb')
      (cdl (disjoint_singleton_pair hab.symm hbj) mLb'
        (equivStatedSp_difference_mem_spBlock haj (mem_pair_left' a j) (mem_pair_right' a j) 1)),
      commutatorElement_differenceShortRootUnit_differenceShortRootUnit haj hbj.symm hab, one_mul]
      at h
    exact h
  have hv1 : positiveSumShortRootUnit haj 1 * la ∈ H' := by
    rw [hla, ← commutator_diff_posLong_one haj]
    exact cA _ _ (equivStatedSp_difference_mem_spBlock haj (pA (Or.inl rfl)) (pA (Or.inr rfl)) 1)
      (equivStatedSp_positiveLong_mem_spBlock (pA (Or.inr rfl)) 1)
  have hv2 : positiveSumShortRootUnit haj 1 * lj ∈ H' := by
    rw [positiveSumShortRootUnit_symm haj, hlj, ← commutator_diff_posLong_one haj.symm]
    exact cA _ _
      (equivStatedSp_difference_mem_spBlock haj.symm (pA (Or.inr rfl)) (pA (Or.inl rfl)) 1)
      (equivStatedSp_positiveLong_mem_spBlock (pA (Or.inl rfl)) 1)
  have haj' : la⁻¹ * lj ∈ H' := by
    have h := mul_mem (inv_mem hv1) hv2
    rwa [show (positiveSumShortRootUnit haj 1 * la)⁻¹ * (positiveSumShortRootUnit haj 1 * lj) =
      la⁻¹ * lj by group] at h
  have hw1 : positiveSumShortRootUnit hbj 1 * lb ∈ H' := by
    rw [hlb, ← commutator_diff_posLong_one hbj]
    exact cB _ _ (equivStatedSp_difference_mem_spBlock hbj (pB (Or.inl rfl)) (pB (Or.inr rfl)) 1)
      (equivStatedSp_positiveLong_mem_spBlock (pB (Or.inr rfl)) 1)
  have hw2 : positiveSumShortRootUnit hbj 1 * lj ∈ H' := by
    rw [positiveSumShortRootUnit_symm hbj, hlj, ← commutator_diff_posLong_one hbj.symm]
    exact cB _ _
      (equivStatedSp_difference_mem_spBlock hbj.symm (pB (Or.inr rfl)) (pB (Or.inl rfl)) 1)
      (equivStatedSp_positiveLong_mem_spBlock (pB (Or.inl rfl)) 1)
  have hbj' : lb⁻¹ * lj ∈ H' := by
    have h := mul_mem (inv_mem hw1) hw2
    rwa [show (positiveSumShortRootUnit hbj 1 * lb)⁻¹ * (positiveSumShortRootUnit hbj 1 * lj) =
      lb⁻¹ * lj by group] at h
  have hw3 : differenceShortRootUnit hbj.symm 1 * lj ∈ H' := by
    rw [hlj, ← commutator_posSum_negLong_one hbj.symm]
    exact cB _ _
      (equivStatedSp_positiveSum_mem_spBlock hbj.symm (pB (Or.inr rfl)) (pB (Or.inl rfl)) 1)
      (equivStatedSp_negativeLong_mem_spBlock (pB (Or.inl rfl)) 1)
  have hjb' : lj⁻¹ * lb' ∈ H' := by
    have h := mul_mem (inv_mem hw3) hv
    rwa [show (differenceShortRootUnit hbj.symm 1 * lj)⁻¹ * (differenceShortRootUnit hbj.symm 1 *
      lb') = lj⁻¹ * lb' by group] at h
  have hcj : ∀ {u : TauCeti.GLSymplecticFin n K}, φ u ∈ spBlock K ({a, b} : Finset (Fin n)) →
      Commute lj⁻¹ u := fun hu => (cdl (disjoint_singleton_pair haj.symm hbj.symm) mLj hu).inv_left
  have mDab : φ (differenceShortRootUnit hab 1) ∈ spBlock K ({a, b} : Finset (Fin n)) :=
    equivStatedSp_difference_mem_spBlock hab (mem_pair_left' a b) (mem_pair_right' a b) 1
  have mSab : φ (positiveSumShortRootUnit hab 1) ∈ spBlock K ({a, b} : Finset (Fin n)) :=
    equivStatedSp_positiveSum_mem_spBlock hab (mem_pair_left' a b) (mem_pair_right' a b) 1
  have hlbj : lb * lj⁻¹ ∈ H' := by
    have h := inv_mem hbj'
    rwa [mul_inv_rev, inv_inv, ((cdl (disjoint_singleton_singleton hbj) mLb mLj).inv_right).eq.symm]
      at h
  have hs : positiveSumShortRootUnit hab 1 * la ∈ H' := by
    have h := cm hd hlbj
    have e := commutatorElement_mul_mul_of_commute_aux (x := differenceShortRootUnit hab 1)
      (x' := 1) (y := lb) (y' := lj⁻¹) (Commute.one_left _) (Commute.one_left _) (hcj mDab)
    rw [mul_one] at e
    rwa [e, hlb, commutator_diff_posLong_one hab] at h
  have hlbj' : lb' * lj⁻¹ ∈ H' := by
    rwa [((cdl (disjoint_singleton_singleton hbj) mLb' mLj).inv_right).eq.symm] at hjb'
  have hdl : differenceShortRootUnit hab 1 * la ∈ H' := by
    have h := cm hs hlbj'
    rwa [commutatorElement_mul_mul_of_commute_aux (cdl (disjoint_singleton_singleton hab) mLa mLb')
      (cdl (disjoint_singleton_singleton haj) mLa mLj).inv_right (hcj mSab), hlb',
      commutator_posSum_negLong_one hab] at h
  have hla_mem : la ∈ H' := by
    have h := mul_mem (inv_mem hd) hdl
    rwa [inv_mul_cancel_left] at h
  have hlj_mem : lj ∈ H' := by
    have h := mul_mem hla_mem haj'
    rwa [mul_inv_cancel_left] at h
  have hm2 : differenceShortRootUnit haj 1 * lj' ∈ H' := by
    rw [hlj', ← commutator_negSum_posLong_one haj.symm]
    exact cA _ _
      (equivStatedSp_negativeSum_mem_spBlock haj.symm (pA (Or.inr rfl)) (pA (Or.inl rfl)) 1)
      (equivStatedSp_positiveLong_mem_spBlock (pA (Or.inl rfl)) 1)
  have hdaj : differenceShortRootUnit haj 1 ∈ H' := by
    have h := mul_mem hu (inv_mem hla_mem)
    rwa [mul_inv_cancel_right] at h
  have hlj'_mem : lj' ∈ H' := by
    have h := mul_mem (inv_mem hdaj) hm2
    rwa [inv_mul_cancel_left] at h
  have hm5 : differenceShortRootUnit haj.symm 1 * lj ∈ H' := by
    rw [hlj, ← commutator_posSum_negLong_one haj.symm]
    exact cA _ _
      (equivStatedSp_positiveSum_mem_spBlock haj.symm (pA (Or.inr rfl)) (pA (Or.inl rfl)) 1)
      (equivStatedSp_negativeLong_mem_spBlock (pA (Or.inl rfl)) 1)
  have hdja : differenceShortRootUnit haj.symm 1 ∈ H' := by
    have h := mul_mem hm5 (inv_mem hlj_mem)
    rwa [mul_inv_cancel_right] at h
  exact ⟨hd, hla_mem, hlj_mem, hlj'_mem, hdaj, hdja⟩

omit [CharP K 2] in
theorem differenceShortRootUnit_zero' {i k : Fin n} (hik : i ≠ k) :
    differenceShortRootUnit (R := K) hik 0 = 1 := by
  have h := differenceShortRootHom_apply (R := K) hik 1
  rw [map_one, toAdd_one] at h
  exact h.symm

omit [CharP K 2] in
theorem positiveLongRootTransvectionUnit_zero' (k : Fin n) :
    positiveLongRootTransvectionUnit (R := K) k 0 = 1 := by
  have h := positiveLongRootTransvectionHom_apply (R := K) k 1
  rw [map_one, toAdd_one] at h
  exact h.symm

omit [CharP K 2] in
theorem negativeLongRootTransvectionUnit_zero' (k : Fin n) :
    negativeLongRootTransvectionUnit (R := K) k 0 = 1 := by
  have h := negativeLongRootTransvectionHom_apply (R := K) k 1
  rw [map_one, toAdd_one] at h
  exact h.symm

theorem eq_top_of_commutator_spBlock_pair_le [Finite K] (hK : Nat.card K = 2) (hn : 3 ≤ n)
    (j : Fin n) {H : Subgroup (StatedSp n K)}
    (hH : ∀ a : Fin n, a ≠ j →
      ⁅spBlock K ({a, j} : Finset (Fin n)), spBlock K ({a, j} : Finset (Fin n))⁆ ≤ H) :
    H = ⊤ := by
  set φ := equivStatedSp n K with hφ
  set H' : Subgroup (TauCeti.GLSymplecticFin n K) := H.comap φ.toMonoidHom with hH'
  have hd1 : ∀ {i k : Fin n} (hik : i ≠ k), differenceShortRootUnit hik (1 : K) ∈ H' := by
    intro i k hik
    by_cases hi : i = j
    · subst hi
      obtain ⟨b, hbk, hbj⟩ := exists_ne_ne_of_three_le hn k i
      exact (mem_of_commutator_spBlock_pair_le (K := K) hbk.symm hik.symm hbj (hH k hik.symm)
        (hH b hbj)).2.2.2.2.2
    · by_cases hk : k = j
      · subst hk
        obtain ⟨b, hbi, hbj⟩ := exists_ne_ne_of_three_le hn i k
        exact (mem_of_commutator_spBlock_pair_le (K := K) hbi.symm hi hbj (hH i hi)
          (hH b hbj)).2.2.2.2.1
      · exact (mem_of_commutator_spBlock_pair_le (K := K) hik hi hk (hH i hi) (hH k hk)).1
  obtain ⟨a, ha, -⟩ := exists_ne_ne_of_three_le hn j j
  obtain ⟨b, hba, hbj⟩ := exists_ne_ne_of_three_le hn a j
  have key := mem_of_commutator_spBlock_pair_le (K := K) hba.symm ha hbj (hH a ha) (hH b hbj)
  have htop : H' = ⊤ := by
    refine TauCeti.GLSymplecticFin.eq_top_of_adjacent_of_long H' j (fun {i k} hik c _ => ?_)
      (fun c => ?_) (fun c => ?_)
    · rcases eq_zero_or_eq_one_of_natCard_two hK c with rfl | rfl
      · rw [differenceShortRootUnit_zero']
        exact one_mem _
      · exact hd1 hik
    · rcases eq_zero_or_eq_one_of_natCard_two hK c with rfl | rfl
      · rw [positiveLongRootTransvectionUnit_zero']
        exact one_mem _
      · exact key.2.2.1
    · rcases eq_zero_or_eq_one_of_natCard_two hK c with rfl | rfl
      · rw [negativeLongRootTransvectionUnit_zero']
        exact one_mem _
      · exact key.2.2.2.1
  rw [eq_top_iff]
  intro x _
  have hx : φ.symm x ∈ H' := by
    rw [htop]
    exact mem_top _
  change φ (φ.symm x) ∈ H at hx
  rwa [MulEquiv.apply_symm_apply] at hx

end Local

theorem perfectCore_spBlock_eq_self [Finite K] (hK : Nat.card K = 2) {N : Finset (Fin n)}
    (hN : 3 ≤ N.card) : CFSG.Quasithin.perfectCore (spBlock K N) = spBlock K N := by
  have hq : CFSG.IsQuasisimple (spBlock K N) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (spBlockEquiv N)
      (CFSG.LieType.Universal.Symplectic.isQuasisimple N.card K (by omega)
        (Or.inr (Or.inr ⟨hK, hN⟩)))
  exact CFSG.Quasithin.perfectCore_eq_self_of_perfect (isPerfect_iff.mp hq.1)

theorem perfectCore_spBlock_compl_pair_sup_sup_eq_top [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hn : 3 ≤ n) {a b c j : Fin (n + 1)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (haj : a ≠ j)
    (hbj : b ≠ j) (hcj : c ≠ j) :
    CFSG.Quasithin.perfectCore (spBlock K ({a, b}ᶜ : Finset (Fin (n + 1)))) ⊔
      CFSG.Quasithin.perfectCore (spBlock K ({a, c}ᶜ : Finset (Fin (n + 1)))) ⊔
        CFSG.Quasithin.perfectCore (spBlock K ({b, c}ᶜ : Finset (Fin (n + 1)))) = ⊤ := by
  rcases Nat.lt_or_ge n 4 with h3 | h4
  ·
    obtain rfl : n = 3 := by omega
    have hcover : ∀ x : Fin (3 + 1), x ≠ j → x = a ∨ x = b ∨ x = c := by
      revert a b c j
      decide
    refine eq_top_of_commutator_spBlock_pair_le hK (by omega) j fun x hx => ?_
    have hsub : ∀ {p q : Fin (3 + 1)}, x ≠ p → x ≠ q → j ≠ p → j ≠ q →
        ({x, j} : Finset (Fin (3 + 1))) ⊆ {p, q}ᶜ := by
      intro p q hxp hxq hjp hjq y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
      rcases hy with rfl | rfl
      · exact ⟨hxp, hxq⟩
      · exact ⟨hjp, hjq⟩
    have hcard : 2 ≤ ({x, j} : Finset (Fin (3 + 1))).card := by
      rw [Finset.card_pair hx]
    have hle := (perfectCore_spBlock_of_card_two hK hcard).2.2
    rcases hcover x hx with rfl | rfl | rfl
    · exact hle.trans ((CFSG.Quasithin.perfectCore_mono (spBlock_mono
        (hsub hab hac (Ne.symm hbj) (Ne.symm hcj)))).trans le_sup_right)
    · exact hle.trans ((CFSG.Quasithin.perfectCore_mono (spBlock_mono
        (hsub hab.symm hbc (Ne.symm haj) (Ne.symm hcj)))).trans (le_sup_right.trans le_sup_left))
    · exact hle.trans ((CFSG.Quasithin.perfectCore_mono (spBlock_mono
        (hsub hac.symm hbc.symm (Ne.symm haj) (Ne.symm hbj)))).trans
          (le_sup_left.trans le_sup_left))
  ·
    have hc : ∀ {p q : Fin (n + 1)}, p ≠ q → 3 ≤ (({p, q}ᶜ : Finset (Fin (n + 1)))).card := by
      intro p q hpq
      rw [card_compl_pair_planes hpq]
      omega
    rw [perfectCore_spBlock_eq_self hK (hc hab), perfectCore_spBlock_eq_self hK (hc hac),
      perfectCore_spBlock_eq_self hK (hc hbc)]
    exact spBlock_compl_pair_sup_sup_eq_top (by omega) hab hac hbc

end CFSG.SeitzReduction.SymplecticPilot
