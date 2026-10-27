module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.ConjFinCheck

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcHighThree

section Wit


theorem rfWitCands_length : ∀ mL ∈ rfWitCands, mL.length = Tag.E6.rank := by
  decide +kernel

theorem rf_cartan_dot_mod3 (mL : List ℕ) (hlen : mL.length = Tag.E6.rank)
    (j : Fin Tag.E6.rank) :
    ((rfDotN (rfCartanMod3.getD (j : ℕ) []) mL : ℕ) : ℤ) % 3 =
      (∑ l : Fin Tag.E6.rank, Tag.E6.cartan l j * ((mL.getD (l : ℕ) 0 : ℕ) : ℤ)) % 3 := by
  have hmcast := rf_map_cast_eq_ofFn mL hlen
  have hrow : rfCartanMod3.getD (j : ℕ) [] =
      (List.ofFn (fun l : Fin Tag.E6.rank => Tag.E6.cartan j l)).map rfRes3 := by
    rw [rfCartanMod3_eq, rfCartanL_eq, List.map_ofFn, List.map_ofFn, List.getD_eq_getElem?_getD]
    simp [List.getElem?_ofFn]
  rw [hrow, rfDotN_comm (List.map rfRes3 _) mL]
  have h2 := rfDotN_res3 mL (List.ofFn fun l : Fin Tag.E6.rank => Tag.E6.cartan j l)
  rw [hmcast, rfDotL_ofFn] at h2
  have h3 : ∑ l : Fin Tag.E6.rank, ((mL.getD (l : ℕ) 0 : ℕ) : ℤ) * Tag.E6.cartan j l =
      ∑ l : Fin Tag.E6.rank, Tag.E6.cartan l j * ((mL.getD (l : ℕ) 0 : ℕ) : ℤ) :=
    Finset.sum_congr rfl fun l _ => by rw [mul_comm (Tag.E6.cartan l j), rf_cartan_symm l j]
  rw [h3] at h2
  exact h2

theorem exists_witness_of_rfWitness (w : WeylGroup Tag.E6)
    (h : rfWitness ((rfCols w).map (·.map rfRes3)) = true) :
    ∃ (m : Fin Tag.E6.rank → ℤ) (k₀ : Fin Tag.E6.rank → ℕ),
      (∀ j : Fin Tag.E6.rank, (3 : ℤ) ∣ (∑ l, Tag.E6.cartan l j * m l) - (k₀ j : ℤ)) ∧
      (∀ t : Fin Tag.E6.rank, (3 : ℤ) ∣
        (∑ i, (k₀ i : ℤ) * (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i) - (k₀ t : ℤ)) ∧
      ¬ ∀ i, (3 : ℤ) ∣ (w • m) i - m i := by
  unfold rfWitness at h
  rw [List.any_eq_true] at h
  obtain ⟨mL, hmL, hmh⟩ := h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmh
  obtain ⟨hall, hne⟩ := hmh
  have hlen : mL.length = Tag.E6.rank := rfWitCands_length mL hmL
  have hmcast := rf_map_cast_eq_ofFn mL hlen
  set kL : List ℕ := rfCartanMod3.map fun row => rfDotN row mL % 3 with hkL
  have hkLlen : kL.length = Tag.E6.rank := by simp [hkL, rfCartanMod3]; rfl
  have hkLget : ∀ j : Fin Tag.E6.rank,
      kL.getD (j : ℕ) 0 = rfDotN (rfCartanMod3.getD (j : ℕ) []) mL % 3 := by
    intro j
    have hj : (j : ℕ) < rfCartanMod3.length := by simp [rfCartanMod3]; exact j.2
    simp [hkL, List.getD_eq_getElem?_getD, hj]
  refine ⟨fun l => ((mL.getD l 0 : ℕ) : ℤ), fun i => kL.getD i 0, ?_, ?_, ?_⟩
  · intro j
    have h1 := rf_cartan_dot_mod3 mL hlen j
    have h2 := hkLget j
    show (3 : ℤ) ∣ ∑ l : Fin Tag.E6.rank, Tag.E6.cartan l j * ((mL.getD (l : ℕ) 0 : ℕ) : ℤ) -
      ((kL.getD (j : ℕ) 0 : ℕ) : ℤ)
    rw [h2]
    omega
  · intro t
    have ht := (List.all_eq_true.1 hall) t.val (List.mem_range.2 t.2)
    simp only [beq_iff_eq] at ht
    have hβ : ((rfCols w).map (·.map rfRes3)).getD (t : ℕ) [] =
        (List.ofFn (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ))).map rfRes3 := by
      have hcl : (t : ℕ) < (rfCols w).length := by simp [rfCols]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hcl]
      simp only [Option.map_some, Option.getD_some]
      rw [rfCols_getElem w t]
    rw [hβ] at ht
    have h2 := rfDotN_res3 kL (List.ofFn (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)))
    rw [rf_map_cast_eq_ofFn kL hkLlen, rfDotL_ofFn] at h2
    show (3 : ℤ) ∣ ∑ i : Fin Tag.E6.rank, ((kL.getD (i : ℕ) 0 : ℕ) : ℤ) *
      (w • (Pi.single t 1 : Fin Tag.E6.rank → ℤ)) i - ((kL.getD (t : ℕ) 0 : ℕ) : ℤ)
    omega
  · intro hall'
    have hmod : rfModEq3 (rfLincomb3 mL ((rfCols w).map (·.map rfRes3))) mL = true := by
      rw [rfModEq3_iff _ _ (by
        rw [hlen]; simp [rfLincomb3]; rfl)]
      intro i
      by_cases hi : i < 6
      · have h2 := rfLincomb3_getD_cast mL (rfCols w) i hi
        have hrow := rf_cols_row w ⟨i, hi⟩
        rw [hmcast, hrow, rfDotL_ofFn] at h2
        have h3 : ∑ j : Fin Tag.E6.rank, ((mL.getD (j : ℕ) 0 : ℕ) : ℤ) *
            (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) ⟨i, hi⟩ =
            (w • fun l : Fin Tag.E6.rank => ((mL.getD (l : ℕ) 0 : ℕ) : ℤ)) ⟨i, hi⟩ :=
          (rf_smul_apply w _ ⟨i, hi⟩).symm
        rw [h3] at h2
        have h4 := hall' ⟨i, hi⟩
        change (3 : ℤ) ∣ (w • fun l : Fin Tag.E6.rank => ((mL.getD (l : ℕ) 0 : ℕ) : ℤ)) ⟨i, hi⟩ -
          ((mL.getD i 0 : ℕ) : ℤ) at h4
        omega
      · have h6 : ¬ i < mL.length := by rw [hlen]; exact hi
        have hr : ¬ i < (rfLincomb3 mL ((rfCols w).map (·.map rfRes3))).length := by
          simp [rfLincomb3]; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 h6),
          List.getElem?_eq_none (not_lt.1 hr)]
    rw [hmod] at hne
    exact Bool.noConfusion hne

end Wit

end CFSG.LieType.SeitzGeneration.ExcWideThree
