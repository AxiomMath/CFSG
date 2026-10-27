module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Dfs

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv

noncomputable def mkPerm (f : Fin 24 → Fin 24) (h : Function.Injective f) : Perm (Fin 24) :=
  Equiv.ofBijective f (Finite.injective_iff_bijective.1 h)

@[expose] def tabOfVec (f : Fin 24 → Fin 24) : Tab := List.ofFn fun i => (f i).val

theorem tabP_mkPerm (f : Fin 24 → Fin 24) (h : Function.Injective f) :
    tabP (mkPerm f h) = tabOfVec f := by
  simp [tabP, tabOfVec, mkPerm]

@[expose] def sylowVec0 : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 19, 13, 6, 7, 8, 9, 20, 15,
    22, 5, 17, 11, 21, 14, 23, 4, 10, 16, 12, 18]

@[expose] def sylowVec1 : Fin 24 → Fin 24 :=
  ![1, 2, 3, 0, 4, 15, 9, 8, 6, 7, 10, 14,
    5, 11, 22, 17, 23, 12, 21, 19, 20, 18, 13, 16]

@[expose] def sylowVec2 : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 23, 5, 7, 6, 9, 8, 16, 11,
    15, 14, 13, 12, 10, 17, 20, 21, 18, 19, 22, 4]

@[expose] def sylowVec3 : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 16, 17, 7, 6, 9, 8, 23, 22,
    12, 13, 14, 15, 4, 5, 19, 18, 21, 20, 11, 10]

@[expose] def sylowVec4 : Fin 24 → Fin 24 :=
  ![13, 1, 14, 3, 19, 7, 17, 5, 9, 8, 10, 22,
    12, 0, 2, 15, 18, 6, 16, 4, 20, 21, 11, 23]

@[expose] def sylowVec5 : Fin 24 → Fin 24 :=
  ![5, 1, 17, 3, 19, 0, 14, 13, 9, 8, 10, 11,
    15, 7, 6, 12, 16, 2, 18, 4, 20, 23, 22, 21]

@[expose] def sylowVec6 : Fin 24 → Fin 24 :=
  ![0, 15, 2, 12, 19, 17, 7, 6, 11, 22, 10, 8,
    3, 13, 14, 1, 18, 5, 16, 4, 20, 21, 9, 23]

@[expose] def sylowVec7 : Fin 24 → Fin 24 :=
  ![0, 11, 2, 22, 19, 5, 7, 6, 15, 12, 10, 1,
    9, 14, 13, 8, 16, 17, 18, 4, 20, 23, 3, 21]

@[expose] def sylowVec8 : Fin 24 → Fin 24 :=
  ![0, 12, 2, 15, 4, 17, 7, 6, 22, 11, 20, 9,
    1, 13, 14, 3, 16, 5, 18, 19, 10, 23, 8, 21]

@[expose] def sylowVec9 : Fin 24 → Fin 24 :=
  ![2, 3, 0, 1, 4, 17, 7, 6, 9, 8, 10, 22,
    15, 14, 13, 12, 16, 5, 18, 19, 20, 21, 11, 23]

noncomputable def sylowGen0 : Perm (Fin 24) := mkPerm sylowVec0 (by decide)

noncomputable def sylowGen1 : Perm (Fin 24) := mkPerm sylowVec1 (by decide)

noncomputable def sylowGen2 : Perm (Fin 24) := mkPerm sylowVec2 (by decide)

noncomputable def sylowGen3 : Perm (Fin 24) := mkPerm sylowVec3 (by decide)

noncomputable def sylowGen4 : Perm (Fin 24) := mkPerm sylowVec4 (by decide)

noncomputable def sylowGen5 : Perm (Fin 24) := mkPerm sylowVec5 (by decide)

noncomputable def sylowGen6 : Perm (Fin 24) := mkPerm sylowVec6 (by decide)

noncomputable def sylowGen7 : Perm (Fin 24) := mkPerm sylowVec7 (by decide)

noncomputable def sylowGen8 : Perm (Fin 24) := mkPerm sylowVec8 (by decide)

noncomputable def sylowGen9 : Perm (Fin 24) := mkPerm sylowVec9 (by decide)

noncomputable def sylowGens : List (Perm (Fin 24)) :=
  [sylowGen0, sylowGen1, sylowGen2, sylowGen3, sylowGen4, sylowGen5, sylowGen6, sylowGen7,
    sylowGen8, sylowGen9]

@[expose] def sylowTabs : List Tab :=
  [[0, 1, 2, 3, 19, 13, 6, 7, 8, 9, 20, 15,
    22, 5, 17, 11, 21, 14, 23, 4, 10, 16, 12, 18],
  [1, 2, 3, 0, 4, 15, 9, 8, 6, 7, 10, 14,
    5, 11, 22, 17, 23, 12, 21, 19, 20, 18, 13, 16],
  [0, 1, 2, 3, 23, 5, 7, 6, 9, 8, 16, 11,
    15, 14, 13, 12, 10, 17, 20, 21, 18, 19, 22, 4],
  [0, 1, 2, 3, 16, 17, 7, 6, 9, 8, 23, 22,
    12, 13, 14, 15, 4, 5, 19, 18, 21, 20, 11, 10],
  [13, 1, 14, 3, 19, 7, 17, 5, 9, 8, 10, 22,
    12, 0, 2, 15, 18, 6, 16, 4, 20, 21, 11, 23],
  [5, 1, 17, 3, 19, 0, 14, 13, 9, 8, 10, 11,
    15, 7, 6, 12, 16, 2, 18, 4, 20, 23, 22, 21],
  [0, 15, 2, 12, 19, 17, 7, 6, 11, 22, 10, 8,
    3, 13, 14, 1, 18, 5, 16, 4, 20, 21, 9, 23],
  [0, 11, 2, 22, 19, 5, 7, 6, 15, 12, 10, 1,
    9, 14, 13, 8, 16, 17, 18, 4, 20, 23, 3, 21],
  [0, 12, 2, 15, 4, 17, 7, 6, 22, 11, 20, 9,
    1, 13, 14, 3, 16, 5, 18, 19, 10, 23, 8, 21],
  [2, 3, 0, 1, 4, 17, 7, 6, 9, 8, 10, 22,
    15, 14, 13, 12, 16, 5, 18, 19, 20, 21, 11, 23]]

theorem sylowGens_map_tabP : sylowGens.map tabP = sylowTabs := by
  simp only [sylowGens, List.map_cons, List.map_nil, sylowGen0, sylowGen1, sylowGen2,
    sylowGen3, sylowGen4, sylowGen5, sylowGen6, sylowGen7, sylowGen8, sylowGen9, tabP_mkPerm]
  decide

noncomputable def sylowS : Subgroup (Perm (Fin 24)) := Subgroup.closure {g | g ∈ sylowGens}

@[expose] def isInv (t : Tab) : Bool := decide (t ≠ idTab ∧ tmul t t = idTab)

@[expose] def tabsArr (gs : List Tab) : Array Tab := (span gs).toArray

@[expose] def rowsOf (tabs : Array Tab) : Array (Array ℕ) :=
  let idx : Std.HashMap Tab ℕ := tabs.foldl (fun m t => m.insert t m.size) {}
  tabs.map fun t => if isInv t then tabs.map fun u => idx.getD (tmul t u) 0 else #[]

@[expose] def lookup (rows : Array (Array ℕ)) (i j : ℕ) : ℕ := (rows.getD i #[]).getD j 0

@[expose] def rowsOKWith (tabs : Array Tab) (rows : Array (Array ℕ)) : Bool :=
  (List.range 1024).all fun i =>
    !isInv (tabs.getD i []) ||
      (List.range 1024).all fun j =>
        decide (lookup rows i j < 1024) &&
          tmul (tabs.getD i []) (tabs.getD j []) == tabs.getD (lookup rows i j) []

@[expose] def colsTab (tabs : Array Tab) (i : ℕ) : List ℕ := colsOfTab (tabs.getD i [])

@[expose] def dfsOKWith (tabs : Array Tab) (rows : Array (Array ℕ)) : Bool :=
  children (lookup rows) (colsTab tabs) (dfs (lookup rows) (colsTab tabs) 9) [0]
    (List.range 4096) ((List.range 1024).filter fun i => isInv (tabs.getD i []))

theorem isInv_tabP {σ : Perm (Fin 24)} : isInv (tabP σ) = true ↔ σ ≠ 1 ∧ σ * σ = 1 := by
  simp only [isInv, decide_eq_true_eq]
  rw [← tabP_one, ← tabP_mul, tabP_injective.ne_iff, tabP_injective.eq_iff]

section Concrete

variable (gens : List (Perm (Fin 24)))

@[expose] def posElt (i : ℕ) : Perm (Fin 24) := (spanE gens).getD i 1

variable {gens}

theorem tabs_getD {n : ℕ} (hS : spanOK n (gens.map tabP) = true) {i : ℕ} (hi : i < n) :
    (tabsArr (gens.map tabP)).getD i [] = tabP (posElt gens i) := by
  have hlen := length_spanE_of_spanOK hS
  have hi' : i < (spanE gens).length := by omega
  have hsp : span (gens.map tabP) = (spanE gens).map tabP := (tabP_spanE gens).symm
  simp only [tabsArr, hsp, posElt]
  rw [List.getD_eq_getElem _ _ hi', Array.getD_eq_getD_getElem?]
  simp [List.getElem?_eq_getElem hi']

def enumOf (hS : spanOK 1024 (gens.map tabP) = true) (rows : Array (Array ℕ))
    (hrows : rowsOKWith (tabsArr (gens.map tabP)) rows = true) :
    Enum (Subgroup.closure {g | g ∈ gens}) where
  N := 1024
  e := posElt gens
  mulIdx := lookup rows
  cols := colsTab (tabsArr (gens.map tabP))
  mem := by
    intro i hi
    have hlen := length_spanE_of_spanOK hS
    have hi' : i < (spanE gens).length := by omega
    rw [posElt, List.getD_eq_getElem _ _ hi']
    exact (mem_closure_iff_of_spanOK hS _).2 (List.getElem_mem hi')
  surj := by
    intro x hx
    have hlen := length_spanE_of_spanOK hS
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 ((mem_closure_iff_of_spanOK hS x).1 hx)
    refine ⟨i, by omega, ?_⟩
    rw [posElt, List.getD_eq_getElem _ _ hi, hix]
  inj := by
    intro i hi j hj h
    have hlen := length_spanE_of_spanOK hS
    have hi' : i < (spanE gens).length := by omega
    have hj' : j < (spanE gens).length := by omega
    rw [posElt, posElt, List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at h
    exact (nodup_spanE hS).getElem_inj_iff.1 h
  pos := by norm_num
  zero := by
    have h := head_spanE gens
    rw [posElt]
    cases hl : spanE gens with
    | nil => simp [hl] at h
    | cons a l =>
      rw [hl] at h
      simp only [List.head?_cons, Option.some.injEq] at h
      simp [h]
  mul := by
    intro i hi hi1 hisq j hj
    have hinvi : isInv ((tabsArr (gens.map tabP)).getD i []) = true := by
      rw [tabs_getD hS hi]
      exact isInv_tabP.2 ⟨hi1, hisq⟩
    have h := List.all_eq_true.1 hrows i (List.mem_range.2 hi)
    simp only [hinvi, Bool.not_true, Bool.false_or] at h
    have h' := List.all_eq_true.1 h j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
    obtain ⟨hlt, heq⟩ := h'
    refine ⟨hlt, ?_⟩
    rw [tabs_getD hS hi, tabs_getD hS hj, tabs_getD hS hlt, ← tabP_mul] at heq
    exact (tabP_injective heq).symm
  fixed := by
    intro i hi m hm h
    simp only [colsTab]
    rw [tabs_getD hS hi]
    exact xorImg_eq_of_fixed hm h

end Concrete

theorem sylowFacts_of_checks
    (h1 : spanOK 1024 sylowTabs = true) (h2 : sylowTabs.all autOK = true)
    (h3 : rowsOKWith (tabsArr sylowTabs) (rowsOf (tabsArr sylowTabs)) = true)
    (h4 : dfsOKWith (tabsArr sylowTabs) (rowsOf (tabsArr sylowTabs)) = true) : SylowFacts := by
  rw [← sylowGens_map_tabP] at h1 h2 h3 h4
  have hcard : Nat.card sylowS = 1024 := card_closure_of_spanOK h1
  refine ⟨sylowS, ?_, by rw [hcard]; norm_num, ?_⟩
  · refine (Subgroup.closure_le aut).2 fun g hg => ?_
    exact mem_aut_of_autOK (List.all_eq_true.1 h2 _ (List.mem_map_of_mem hg))
  · refine offenderBound_of_dfs (enumOf h1 _ h3) (by rw [hcard]; norm_num)
      ((List.range 1024).filter fun i => isInv ((tabsArr (sylowGens.map tabP)).getD i [])) ?_ h4
    intro i hi hi1 hisq
    rw [List.mem_filter]
    refine ⟨List.mem_range.2 hi, ?_⟩
    rw [tabs_getD h1 hi]
    exact isInv_tabP.2 ⟨hi1, hisq⟩

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
