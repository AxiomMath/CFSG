
module

public import Certificates.Data.GrSLitL34FactsRealCheck
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def genR (j : ℕ) : Equiv.Perm (Fin 42) :=
  if j = 0 then g₁ else if j = 1 then g₂ else if j = 2 then g₃ else if j = 3 then g₄
    else if j = 4 then g₅ else g₆

theorem genR_mem (j : ℕ) : genR j ∈ R := by
  unfold genR
  split_ifs
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact g₄_mem_R
  · exact g₅_mem_R
  · exact g₆_mem_R

theorem tabRep_genR {j : ℕ} (hj : j < 6) : TabRep gTabs[j]! (genR j) := by
  interval_cases j
  · exact tabRep_g₁
  · exact tabRep_g₂
  · exact tabRep_g₃
  · exact tabRep_g₄
  · exact tabRep_g₅
  · exact tabRep_g₆

@[expose] def rPerm (w : List ℕ) : Equiv.Perm (Fin 42) := w.foldl (fun g j => g * genR j) 1

theorem tabRep_rTab_aux (w : List ℕ) (hw : ∀ j ∈ w, j < 6) {t : Tab} {g : Equiv.Perm (Fin 42)}
    (ht : TabRep t g) :
    TabRep (w.foldl (fun t j => comp 42 t gTabs[j]!) t) (w.foldl (fun g j => g * genR j) g) := by
  induction w generalizing t g with
  | nil => exact ht
  | cons j w ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun j' hj' => hw j' (List.mem_cons_of_mem _ hj'))
      (ht.comp (tabRep_genR (hw j (List.mem_cons_self))))

theorem rPerm_mem_aux (w : List ℕ) {g : Equiv.Perm (Fin 42)} (hg : g ∈ R) :
    w.foldl (fun g j => g * genR j) g ∈ R := by
  induction w generalizing g with
  | nil => exact hg
  | cons j w ih => exact ih (R.mul_mem hg (genR_mem j))

@[expose] def repPerm (i : ℕ) : Equiv.Perm (Fin 42) := rPerm (realRepWords.getD i [])

theorem repWords_lt : ∀ i < 36, ∀ j ∈ realRepWords.getD i [], j < 6 := by decide

theorem tabRep_repTab {i : ℕ} (hi : i < 36) : TabRep (repTab i) (repPerm i) := by
  have h := tabRep_rTab_aux (realRepWords.getD i []) (repWords_lt i hi)
    (TabRep.idTab (n := 42))
  exact h

theorem repPerm_mem (i : ℕ) : repPerm i ∈ R := rPerm_mem_aux _ R.one_mem

end CFSG.ComponentClassification.GrSLit.L34Facts.Real
