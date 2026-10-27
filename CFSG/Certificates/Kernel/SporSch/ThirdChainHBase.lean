
module

public import CFSG.Sporadic.Co2Schreier.ThirdChainBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

structure ThirdFactsH : Prop where
  base_size : (thB.size == 13) = true
  base_lt : allLt 13 (fun j => decide (thB[j]! < 2300)) = true
  L_size : (thL.size == 13) = true
  sizes : ((thL.toList.map fun T => T.tr.size) ==
    [2300, 891, 896, 96, 30, 1, 4, 1, 1, 1, 1, 1, 2]) = true
  tr : allLt 13 (fun j => eqA 2300 thL[j]!.tr[0]! (idA 2300) &&
    allLt thL[j]!.tr.size (fun k => isInvA 2300 thL[j]!.tr[k]! (invCand 2300 thL[j]!.tr[k]!) &&
      fixesFirst thB thL[j]!.tr[k]! j &&
      siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 thL[j]!.tr[k]! &&
      allLt k (fun k' => (thL[j]!.tr[k]!)[thB[j]!]! != (thL[j]!.tr[k']!)[thB[j]!]!))) = true
  u_inv : isInvA 2300 uArr (invCand 2300 uArr) = true
  u_fix : fixesFirst thB uArr 12 = true

variable (h : ThirdFactsH)
include h

theorem thB_sizeH : thB.size = 13 := beq_iff_eq.1 h.base_size

theorem thB_ltH {j : ℕ} (hj : j < 13) : thB[j]! < 2300 := by
  have := allLt_iff.1 h.base_lt j hj
  simpa using this

theorem thL_sizeH : thL.size = 13 := beq_iff_eq.1 h.L_size

theorem tsz_listH : (List.range 13).map tsz = [2300, 891, 896, 96, 30, 1, 4, 1, 1, 1, 1, 1, 2] := by
  have e := beq_iff_eq.1 h.sizes
  rw [← e]
  apply List.ext_getElem
  · simp [thL_sizeH h]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, tsz]
    rw [getElem!_pos thL i (by rw [thL_sizeH h]; simpa using h1)]

theorem tsz_eqH {j : ℕ} (hj : j < 13) :
    tsz j = [2300, 891, 896, 96, 30, 1, 4, 1, 1, 1, 1, 1, 2].getD j 0 := by
  rw [← tsz_listH h, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem tsz_posH {j : ℕ} (hj : j < 13) : 0 < tsz j := by
  rw [tsz_eqH h hj]
  interval_cases j <;> decide

theorem prod_tszH : ∏ j ∈ Finset.range 13, tsz j = 42305421312000 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, tsz_eqH h (by norm_num : 0 < 13),
    tsz_eqH h (by norm_num : 1 < 13), tsz_eqH h (by norm_num : 2 < 13),
    tsz_eqH h (by norm_num : 3 < 13), tsz_eqH h (by norm_num : 4 < 13),
    tsz_eqH h (by norm_num : 5 < 13), tsz_eqH h (by norm_num : 6 < 13),
    tsz_eqH h (by norm_num : 7 < 13), tsz_eqH h (by norm_num : 8 < 13),
    tsz_eqH h (by norm_num : 9 < 13), tsz_eqH h (by norm_num : 10 < 13),
    tsz_eqH h (by norm_num : 11 < 13), tsz_eqH h (by norm_num : 12 < 13)]
  decide

theorem thFacts_trH {j k : ℕ} (hj : j < 13) (hk : k < tsz j) :
    isInvA 2300 thL[j]!.tr[k]! (invCand 2300 thL[j]!.tr[k]!) = true ∧
      fixesFirst thB thL[j]!.tr[k]! j = true ∧
      siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 thL[j]!.tr[k]! = true ∧
      ∀ k' < k, (thL[j]!.tr[k]!)[thB[j]!]! ≠ (thL[j]!.tr[k']!)[thB[j]!]! := by
  have h1 := allLt_iff.1 h.tr j hj
  rw [Bool.and_eq_true] at h1
  have h2 := allLt_iff.1 h1.2 k hk
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩ := h2
  refine ⟨h3, h4, h5, fun k' hk' => ?_⟩
  have := allLt_iff.1 h6 k' hk'
  simpa using this

theorem thFacts_zeroH {j : ℕ} (hj : j < 13) : eqA 2300 thL[j]!.tr[0]! (idA 2300) = true := by
  have h1 := allLt_iff.1 h.tr j hj
  rw [Bool.and_eq_true] at h1
  exact h1.1

theorem bpt_valH {j : ℕ} (hj : j < 13) : (bpt j : ℕ) = thB[j]! := Nat.mod_eq_of_lt (thB_ltH h hj)

theorem rep_thTH {j k : ℕ} (hj : j < 13) (hk : k < tsz j) : Rep 2300 thL[j]!.tr[k]! (thT j k) :=
  (rep_permOfArr (thFacts_trH h hj hk).1).1

theorem thT_memH {j k : ℕ}
    (hj : j < 13) (hk : k < tsz j) : thT j k ∈ co2P := by
  rw [← co2Q_originalSubgroup]
  exact (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1
    (rep_thTH h hj hk)).1 (thFacts_trH h hj hk).2.2.1

theorem rep_apply_bptH {t : Array ℕ} {g : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t g) {j : ℕ}
    (hj : j < 13) : (g (bpt j) : ℕ) = t[thB[j]!]! := by
  rw [← bpt_valH h hj]
  exact (ht (bpt j)).symm

theorem thT_fixH {j k i : ℕ} (hj : j < 13) (hk : k < tsz j) (hi : i < j) :
    thT j k (bpt i) = bpt i := by
  apply Fin.ext
  rw [rep_apply_bptH h (rep_thTH h hj hk) (j := i) (by omega), bpt_valH h (j := i) (by omega)]
  have := allLt_iff.1 (thFacts_trH h hj hk).2.1 i hi
  simpa using this

theorem thT_injH {j k k' : ℕ} (hj : j < 13) (hk : k < tsz j) (hk' : k' < tsz j)
    (he : thT j k (bpt j) = thT j k' (bpt j)) : k = k' := by
  have h' := congrArg Fin.val he
  rw [rep_apply_bptH h (rep_thTH h hj hk) hj, rep_apply_bptH h (rep_thTH h hj hk') hj] at h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact (thFacts_trH h hj hk').2.2.2 k hlt h'.symm
  · exact (thFacts_trH h hj hk).2.2.2 k' hlt h'

theorem thT_zeroH {j : ℕ} (hj : j < 13) : thT j 0 = 1 :=
  eq_of_eqA (rep_thTH h hj (tsz_posH h hj)) rep_idA (thFacts_zeroH h hj)

theorem thT_mem_stabBH {j k : ℕ}
    (hj : j < 13) (hk : k < tsz j) : thT j k ∈ stabB j :=
  ⟨thT_memH h hj hk, fun _ hi => thT_fixH h hj hk hi⟩

@[expose] def phiBH (j : ℕ)
    (hj : j < 13) : Fin (tsz j) × stabB (j + 1) → stabB j :=
  fun x => ⟨thT j x.1 * x.2, (stabB j).mul_mem (thT_mem_stabBH h hj x.1.2) (stabB_succ_le j x.2.2)⟩

theorem phiB_injectiveH {j : ℕ}
    (hj : j < 13) : Function.Injective (phiBH h j hj) := by
  rintro ⟨k, s⟩ ⟨k', s'⟩ he
  have h1 : thT j k * (s : Equiv.Perm (Fin 2300)) = thT j k' * s' := congrArg Subtype.val he
  have hs : (s : Equiv.Perm (Fin 2300)) (bpt j) = bpt j := s.2.2 j (by omega)
  have hs' : (s' : Equiv.Perm (Fin 2300)) (bpt j) = bpt j := s'.2.2 j (by omega)
  have h2 := congrArg (fun g : Equiv.Perm (Fin 2300) => g (bpt j)) h1
  simp only [Equiv.Perm.mul_apply, hs, hs'] at h2
  have hkk : k = k' := Fin.ext (thT_injH h hj k.2 k'.2 h2)
  subst hkk
  have : (s : Equiv.Perm (Fin 2300)) = s' := mul_left_cancel h1
  exact Prod.ext rfl (Subtype.ext this)

theorem card_stabB_leH {j : ℕ}
    (hj : j < 13) : tsz j * Nat.card (stabB (j + 1)) ≤ Nat.card (stabB j) := by
  have h1 := Nat.card_le_card_of_injective _ (phiB_injectiveH h hj)
  rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin] at h1

theorem card_stabBH {j : ℕ}
    (hj : j ≤ 13) : Nat.card (stabB j) = ∏ i ∈ Finset.Ico j 13, tsz i := by
  refine chain_card_eq (c := fun j => Nat.card (stabB j)) (t := tsz) (n := 13)
    (fun j hj => card_stabB_leH h hj) Nat.card_pos (fun j hj => tsz_posH h hj) ?_ j hj
  exact le_of_eq (by rw [stabB_zero, card_co2P, prod_tszH h])

theorem stabB_thirteenH :
    stabB 13 = ⊥ := by
  rw [← Subgroup.card_eq_one, card_stabBH h le_rfl, Finset.Ico_self, Finset.prod_empty]

theorem card_stabB_succH {j : ℕ}
    (hj : j < 13) : Nat.card (stabB j) = tsz j * Nat.card (stabB (j + 1)) := by
  rw [card_stabBH h hj.le, card_stabBH h (j := j + 1) (by omega),
    Finset.prod_eq_prod_Ico_succ_bot hj]

theorem phiB_bijectiveH {j : ℕ}
    (hj : j < 13) : Function.Bijective (phiBH h j hj) := by
  refine (Nat.bijective_iff_injective_and_card _).2 ⟨phiB_injectiveH h hj, ?_⟩
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, card_stabB_succH h hj]

theorem exists_thT_inv_mul_memH
    {j : ℕ} (hj : j < 13) {s : Equiv.Perm (Fin 2300)} (hs : s ∈ stabB j) :
    ∃ k < tsz j, (thT j k)⁻¹ * s ∈ stabB (j + 1) := by
  obtain ⟨⟨k, s'⟩, he⟩ := (phiB_bijectiveH h hj).2 ⟨s, hs⟩
  have h1 : thT j k * (s' : Equiv.Perm (Fin 2300)) = s := congrArg Subtype.val he
  refine ⟨k, k.2, ?_⟩
  rw [← h1, inv_mul_cancel_left]
  exact s'.2

theorem prodFrom_memH
    {k : ℕ → ℕ} : ∀ (f j : ℕ), j + f = 13 →
    (∀ i, j ≤ i → i < 13 → k i < tsz i) → prodFrom k f j ∈ stabB j
  | 0, j, _, _ => by
    rw [prodFrom]
    exact (stabB j).one_mem
  | f + 1, j, hj, hk => by
    rw [prodFrom]
    exact (stabB j).mul_mem (thT_mem_stabBH h (by omega) (hk j le_rfl (by omega)))
      (stabB_succ_le j (prodFrom_memH f (j + 1) (by omega) fun i hi hi' => hk i (by omega) hi'))

theorem exists_prodFromH :
    ∀ (f j : ℕ), j + f = 13 → ∀ s ∈ stabB j,
    ∃ k : ℕ → ℕ, (∀ i, j ≤ i → i < 13 → k i < tsz i) ∧ s = prodFrom k f j
  | 0, j, hj, s, hs => by
    have h13 : j = 13 := by omega
    subst h13
    rw [stabB_thirteenH h, Subgroup.mem_bot] at hs
    exact ⟨fun _ => 0, fun i hi hi' => by omega, by rw [hs, prodFrom]⟩
  | f + 1, j, hj, s, hs => by
    obtain ⟨k0, hk0, hs'⟩ := exists_thT_inv_mul_memH h (by omega) hs
    obtain ⟨k', hk', he⟩ := exists_prodFromH f (j + 1) (by omega) _ hs'
    refine ⟨Function.update k' j k0, fun i hi hi' => ?_, ?_⟩
    · rcases eq_or_lt_of_le hi with rfl | hlt
      · rw [Function.update_self]
        exact hk0
      · rw [Function.update_of_ne (by omega)]
        exact hk' i hlt hi'
    · rw [prodFrom, Function.update_self, prodFrom_congr f (j + 1) (k' := k')
        fun i hi => Function.update_of_ne (by omega) _ _, ← he, mul_inv_cancel_left]

theorem prodFrom_injH :
    ∀ (f j : ℕ), j + f = 13 → ∀ (k k' : ℕ → ℕ),
    (∀ i, j ≤ i → i < 13 → k i < tsz i) → (∀ i, j ≤ i → i < 13 → k' i < tsz i) →
    prodFrom k f j = prodFrom k' f j → ∀ i, j ≤ i → i < 13 → k i = k' i
  | 0, j, hj, _, _, _, _, _, i, hi, hi' => by omega
  | f + 1, j, hj, k, k', hk, hk', he, i, hi, hi' => by
    rw [prodFrom, prodFrom] at he
    have hm := prodFrom_memH h f (j + 1) (by omega) fun i hi hi' => hk i (by omega) hi'
    have hm' := prodFrom_memH h f (j + 1) (by omega) fun i hi hi' => hk' i (by omega) hi'
    have h2 := congrArg (fun g : Equiv.Perm (Fin 2300) => g (bpt j)) he
    simp only [Equiv.Perm.mul_apply, hm.2 j (by omega), hm'.2 j (by omega)] at h2
    have hkj : k j = k' j := thT_injH h (by omega) (hk j le_rfl (by omega))
      (hk' j le_rfl (by omega)) h2
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact hkj
    · rw [hkj] at he
      exact prodFrom_injH f (j + 1) (by omega) k k' (fun i hi hi' => hk i (by omega) hi')
        (fun i hi hi' => hk' i (by omega) hi') (mul_left_cancel he) i hlt hi'

end CFSG.Sporadic.Co2Schreier
