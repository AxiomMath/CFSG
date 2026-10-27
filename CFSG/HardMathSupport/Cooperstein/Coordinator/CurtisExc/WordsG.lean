module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Family
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.WeightsE
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.ClassSep

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Blueprint.Chevalley

section Lists

variable {τ : Tag}

@[expose] def reflectLG (τ : Tag) (i : Fin τ.rank) (l : List ℤ) : List ℤ :=
  List.ofFn fun j : Fin τ.rank =>
    l.getD j 0 - if j = i then (List.finRange τ.rank).map
      (fun k => τ.cartan i k * l.getD k 0) |>.sum else 0

theorem ofFn_reflectG (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    List.ofFn (reflect τ i v) = reflectLG τ i (List.ofFn v) := by
  unfold reflectLG reflect
  refine congrArg List.ofFn (funext fun j => ?_)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  have hs : ∑ k, τ.cartan i k * v k =
      ((List.finRange τ.rank).map (fun k => τ.cartan i k * (List.ofFn v).getD k 0)).sum := by
    rw [Fin.sum_univ_def]
    refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
    simp [List.getD_eq_getElem?_getD]
  rw [hs]
  by_cases hj : j = i <;> simp [hj]

theorem ofFn_foldr_reflectG (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    List.ofFn (l.foldr (reflect τ) v) = l.foldr (reflectLG τ) (List.ofFn v) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, List.foldr_cons, ofFn_reflectG, ih]

@[expose] def refELG (τ : Tag) (j : Fin τ.rank) (l : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin τ.rank => l.getD i 0 - τ.cartan i j * l.getD j 0

theorem ofFn_refEG (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    List.ofFn (refE τ j v) = refELG τ j (List.ofFn v) := by
  unfold refELG refE
  refine congrArg List.ofFn (funext fun i => ?_)
  simp [List.getD_eq_getElem?_getD]

theorem ofFn_foldr_refEG (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    List.ofFn (l.foldr (refE τ) v) = l.foldr (refELG τ) (List.ofFn v) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, List.foldr_cons, ofFn_refEG, ih]

theorem cont2_of_contentL {r : ℕ} {x y : Fin r → ℤ}
    (h : 1 ≤ contentL (subL (List.ofFn x) (List.ofFn y)) ∧
      contentL (subL (List.ofFn x) (List.ofFn y)) ≤ 2) : Cont2 (x - y) := by
  intro d hd
  have h1 : d ∣ contentL (subL (List.ofFn x) (List.ofFn y)) := by
    refine dvd_contentL d _ fun z hz => ?_
    have e : subL (List.ofFn x) (List.ofFn y) = List.ofFn (x - y) := by
      unfold subL
      refine List.ext_getElem (by simp) fun n h1 h2 => ?_
      simp
    rw [e, List.mem_ofFn] at hz
    obtain ⟨c, rfl⟩ := hz
    exact hd c
  have hc : contentL (subL (List.ofFn x) (List.ofFn y)) = 1 ∨
      contentL (subL (List.ofFn x) (List.ofFn y)) = 2 := by omega
  rcases hc with hc | hc <;> rw [hc] at h1
  · exact h1.trans (by norm_num)
  · exact h1

end Lists

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
