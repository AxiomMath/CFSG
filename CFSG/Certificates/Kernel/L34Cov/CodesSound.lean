module

public import Certificates.Data.Kernel.L34Cov.Codes
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.KC.L34Cov

open CFSG.Certificates.CosetEnumeration CFSG.LieType.Multipliers.L34 CFSG.CosetTable

theorem decL_of_lt : ∀ c < 4, (if decC c = 'a' then some ((0 : Fin 2), true)
    else if decC c = 'A' then some (0, false) else if decC c = 'b' then some (1, true)
    else if decC c = 'B' then some (1, false) else none) = some (decL c) := by
  decide

theorem letterCode_decL : ∀ c < 4, letterCode (decL c) = c := by decide

theorem codesOK_spec {w : List ℕ} (hw : codesOK w = true) : ∀ c ∈ w, c < 4 := by
  intro c hc
  have h := List.all_eq_true.1 hw c hc
  exact Nat.le_of_ble_eq_true h

theorem parseWord_ofList {w : List ℕ} (hw : codesOK w = true) :
    parseWord (String.ofList (w.map decC)) = w.map decL := by
  rw [parseWord, String.toList_ofList, List.filterMap_map]
  induction w with
  | nil => rfl
  | cons c w ih =>
    have h := codesOK_spec hw
    simp only [List.filterMap_cons, Function.comp_apply, decL_of_lt c (h c List.mem_cons_self),
      List.map_cons]
    congr 1
    exact ih (List.all_eq_true.2 fun x hx => (List.all_eq_true.1 hw) x (List.mem_cons_of_mem _ hx))

theorem map_letterCode_decL {w : List ℕ} (hw : codesOK w = true) :
    (w.map decL).map letterCode = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left fun c hc => letterCode_decL c (codesOK_spec hw c hc)

theorem letterCode_flip (x : Fin 2 × Bool) : letterCode (x.1, !x.2) = invCode (letterCode x) := by
  obtain ⟨i, b⟩ := x
  fin_cases i <;> cases b <;> rfl

theorem map_letterCode_invRev (w : List (Fin 2 × Bool)) :
    (FreeGroup.invRev w).map letterCode = invW (w.map letterCode) := by
  rw [FreeGroup.invRev, invW, List.map_reverse, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ => letterCode_flip x

theorem map_letterCode_substWord (hs : List (List (Fin 2 × Bool))) (r : List (Fin 2 × Bool)) :
    (substWord hs r).map letterCode = substC (hs.map (List.map letterCode)) (r.map letterCode) := by
  rw [substWord, substC, List.map_flatMap, List.flatMap_map]
  congr 1
  funext x
  obtain ⟨i, b⟩ := x
  have hg : (hs.map (List.map letterCode)).getD i.val [] = (hs.getD i.val []).map letterCode := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases hs[i.val]? <;> rfl
  have hdiv : Nat.div (letterCode (i, b)) 2 = i.val := by fin_cases i <;> cases b <;> rfl
  have hb : Nat.beq (Nat.mod (letterCode (i, b)) 2) 0 = b := by fin_cases i <;> cases b <;> rfl
  dsimp only
  rw [hdiv, hb, hg]
  cases b
  · rw [Bool.cond_false, if_neg Bool.false_ne_true, map_letterCode_invRev]
  · rw [Bool.cond_true, if_pos rfl]

end CFSG.KC.L34Cov

end
