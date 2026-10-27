module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.ConjFinCheck

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem rfUnit_eq_ofFn (j : Fin Tag.E6.rank) :
    rfUnit (j : ℕ) = List.ofFn (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
  apply List.ext_getElem
  · simp [rfUnit, show Tag.E6.rank = 6 from rfl]
  · intro n h1 h2
    simp [rfUnit, Pi.single_apply, Fin.ext_iff]

theorem rfRefl_ofFn (i : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ℤ) :
    rfRefl (i : ℕ) (List.ofFn x) = List.ofFn (reflect Tag.E6 i x) := by
  have hrow : rfCartanL.getD (i : ℕ) [] =
      List.ofFn fun j : Fin Tag.E6.rank => Tag.E6.cartan i j := by
    simp [List.getD_eq_getElem?_getD, rfCartanL_eq]
  have hdot : rfDotL (rfCartanL.getD (i : ℕ) []) (List.ofFn x) =
      ∑ j, Tag.E6.cartan i j * x j := by
    rw [hrow, rfDotL_ofFn]
  have hget : (List.ofFn x).getD (i : ℕ) 0 = x i := by
    simp [List.getD_eq_getElem?_getD]
  unfold rfRefl
  rw [hget, hdot]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    have hn : n < Tag.E6.rank := by simpa using h2
    by_cases hin : (i : ℕ) = n
    · subst hin
      simp [reflect, Pi.single_apply]
    · have hne : ¬ (⟨n, hn⟩ : Fin Tag.E6.rank) = i := fun h => hin (by rw [← h])
      simp [reflect, Pi.single_apply, hne, hin, Fin.ext_iff]

theorem rf_wordProd_smul_eq_foldr (ω : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    ((coxeterSystem Tag.E6).wordProd ω) • v = ω.foldr (fun j x => reflect Tag.E6 j x) v := by
  induction ω with
  | nil => simp
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, List.foldr_cons, simple_smul]

theorem rfWordApply_ofFn (ω : List (Fin Tag.E6.rank)) (y : Fin Tag.E6.rank → ℤ) :
    rfWordApply (ω.map fun i : Fin Tag.E6.rank => (i : ℕ)) (List.ofFn y) =
      List.ofFn (((coxeterSystem Tag.E6).wordProd ω) • y) := by
  rw [rf_wordProd_smul_eq_foldr]
  induction ω with
  | nil => simp [rfWordApply]
  | cons j ω ih =>
    change rfRefl (j : ℕ) (rfWordApply (ω.map fun i : Fin Tag.E6.rank => (i : ℕ))
      (List.ofFn y)) = _
    rw [ih, rfRefl_ofFn, List.foldr_cons]

section Certs


theorem rfVCols_eq_rfCols (ω : List (Fin Tag.E6.rank)) :
    rfVCols (ω.map fun i : Fin Tag.E6.rank => (i : ℕ)) =
      rfCols ((coxeterSystem Tag.E6).wordProd ω) := by
  apply List.ext_getElem
  · simp [rfVCols, rfCols, show Tag.E6.rank = 6 from rfl]
  · intro n h1 h2
    have hn : n < Tag.E6.rank := by simpa [rfCols] using h2
    have hC : (rfCols ((coxeterSystem Tag.E6).wordProd ω))[n]'h2 =
        List.ofFn (((coxeterSystem Tag.E6).wordProd ω) •
          (Pi.single (⟨n, hn⟩ : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ)) :=
      rfCols_getElem _ ⟨n, hn⟩
    have hU : rfUnit n = List.ofFn (Pi.single (⟨n, hn⟩ : Fin Tag.E6.rank) 1 :
        Fin Tag.E6.rank → ℤ) :=
      rfUnit_eq_ofFn ⟨n, hn⟩
    rw [hC]
    simp only [rfVCols, List.getElem_map, List.getElem_range]
    rw [hU, rfWordApply_ofFn]

theorem rfVCols_reverse_eq_rfCols (ω : List (Fin Tag.E6.rank)) :
    rfVCols (ω.map fun i : Fin Tag.E6.rank => (i : ℕ)).reverse =
      rfCols (((coxeterSystem Tag.E6).wordProd ω)⁻¹) := by
  rw [← CoxeterSystem.wordProd_reverse, ← rfVCols_eq_rfCols ω.reverse, List.map_reverse]

end Certs

end CFSG.LieType.SeitzGeneration.ExcWideThree
