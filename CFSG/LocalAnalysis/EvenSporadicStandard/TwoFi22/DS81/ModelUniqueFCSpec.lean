module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFCCheck
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

theorem fcLinL_congr {a b : Array Nat} (h : ∀ i < 10, a[i]! = b[i]!) (v : Nat) {l : List Nat}
    (hl : ∀ i ∈ l, i < 10) : linL a v l = linL b v l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [linL, List.foldr_cons] at ih ⊢
    rw [ih fun j hj => hl j (List.mem_cons_of_mem _ hj), h i (hl i List.mem_cons_self)]

theorem fcLin_congr {a b : Array Nat} (h : ∀ i < 10, a[i]! = b[i]!) (v : Nat) :
    lin a v = lin b v :=
  fcLinL_congr h v fun _ hi => List.mem_range.1 hi

theorem fcFn_congr {a b : Array Nat} (h : ∀ i < 10, a[i]! = b[i]!) : fn a = fn b := by
  funext v
  apply Fin.ext
  show lin a v.val % 1024 = lin b v.val % 1024
  rw [fcLin_congr h]

private theorem forall_lt_ten {P : Nat → Prop} :
    (∀ i < 10, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7 ∧ P 8 ∧ P 9 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
      h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num),
      h 8 (by norm_num), h 9 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ i hi
    interval_cases i <;> assumption

theorem fcMatEq_iff {a b : Array Nat} : fcMatEq a b = true ↔ ∀ i < 10, a[i]! = b[i]! := by
  simp only [fcMatEq, forall_lt_ten, Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem fcColsLt_iff {a : Array Nat} : fcColsLt a = true ↔ ∀ i < 10, a[i]! < 1024 := by
  simp only [fcColsLt, forall_lt_ten, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem fcMatEqAct_iff {m t r : Array Nat} :
    fcMatEqAct m t r = true ↔ ∀ i < 10, m[i]! = t[r[i]!]! := by
  simp only [fcMatEqAct, forall_lt_ten, Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem fcGetElem!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α)
    {i : Nat} (h : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using h), Array.getElem_map, getElem!_pos a i h]

theorem fcIdx_spec {ms : Array (Array Nat)} {r : Array Nat} (h : fcIdx ms r < ms.size) :
    ∀ i < 10, r[i]! = ms[fcIdx ms r]![i]! := by
  have h1 : fcMatEq r ms[ms.findIdx (fcMatEq r)] = true := Array.findIdx_getElem (w := h)
  rw [fcIdx, getElem!_pos ms _ h]
  exact fcMatEq_iff.1 h1

theorem fcAct_getElem! {c : Array Nat} {v : Nat} (hv : v < 1024) : (fcAct c)[v]! = lin c v := by
  have hv' : v < (Array.range 1024).size := by simpa using hv
  rw [fcAct, fcGetElem!_map _ _ hv', getElem!_pos (Array.range 1024) v hv', Array.getElem_range]

theorem fcMul_size (ms act : Array (Array Nat)) : (fcMul ms act).size = act.size := by
  simp [fcMul]

theorem fcMul_getElem!_size (ms act : Array (Array Nat)) {i : Nat} (hi : i < act.size) :
    ((fcMul ms act)[i]!).size = ms.size := by
  rw [fcMul, fcGetElem!_map _ _ hi]
  simp

theorem fcMul_getElem! {ms act : Array (Array Nat)} {i j : Nat} (hi : i < act.size)
    (hj : j < ms.size) :
    (fcMul ms act)[i]![j]! = ms.findIdx (fun m => fcMatEqAct m act[i]! ms[j]!) := by
  rw [fcMul, fcGetElem!_map _ _ hi, fcGetElem!_map _ _ hj]

theorem fcMul_spec {ms : Array (Array Nat)} {i j : Nat} (hi : i < ms.size) (hj : j < ms.size)
    (hjc : ∀ c < 10, ms[j]![c]! < 1024) (h : (fcMul ms (ms.map fcAct))[i]![j]! < ms.size) :
    ∀ c < 10, ms[(fcMul ms (ms.map fcAct))[i]![j]!]![c]! = lin ms[i]! ms[j]![c]! := by
  have hi' : i < (ms.map fcAct).size := by simpa using hi
  have hk := fcMul_getElem! (ms := ms) (act := ms.map fcAct) hi' hj
  rw [hk] at h ⊢
  have h1 : fcMatEqAct ms[ms.findIdx (fun m => fcMatEqAct m (ms.map fcAct)[i]! ms[j]!)]
      (ms.map fcAct)[i]! ms[j]! = true := Array.findIdx_getElem (w := h)
  intro c hc
  rw [getElem!_pos ms _ h, fcMatEqAct_iff.1 h1 c hc, fcGetElem!_map _ _ hi,
    fcAct_getElem! (hjc c hc)]

theorem fcMul_fn {ms : Array (Array Nat)} (hmsN : ∀ i < ms.size, ∀ c < 10, ms[i]![c]! < 1024)
    (hN : (fcMul ms (ms.map fcAct)).all (·.all (· < ms.size)) = true) {i j : Nat}
    (hi : i < ms.size) (hj : j < ms.size) :
    (fcMul ms (ms.map fcAct))[i]![j]! < ms.size ∧
      fn ms[(fcMul ms (ms.map fcAct))[i]![j]!]! = fn ms[i]! ∘ fn ms[j]! := by
  have hi' : i < (ms.map fcAct).size := by simpa using hi
  have h1 : i < (fcMul ms (ms.map fcAct)).size := by rw [fcMul_size]; exact hi'
  have h3 : j < ((fcMul ms (ms.map fcAct))[i]).size := by
    have := fcMul_getElem!_size ms (ms.map fcAct) hi'
    rw [getElem!_pos _ i h1] at this
    rw [this]
    exact hj
  have hlt : (fcMul ms (ms.map fcAct))[i]![j]! < ms.size := by
    have h4 := Array.all_eq_true.1 (Array.all_eq_true.1 hN i h1) j h3
    rw [getElem!_pos (fcMul ms (ms.map fcAct)) i h1,
      getElem!_pos ((fcMul ms (ms.map fcAct))[i]) j h3]
    simpa using h4
  refine ⟨hlt, ?_⟩
  have hspec := fcMul_spec hi hj (hmsN j hj) hlt
  have hk := hmsN _ hlt
  calc fn ms[(fcMul ms (ms.map fcAct))[i]![j]!]!
      = fn (compose ms[i]! ms[j]!) := by
        refine fcFn_congr fun c hc => ?_
        rw [hspec c hc, compose_getElem! _ _ hc]
    _ = fn ms[i]! ∘ fn ms[j]! := fn_compose (hmsN i hi) (hmsN j hj)

theorem fcDistinct_spec {ms : Array (Array Nat)} (h : fcDistinct ms = true)
    (hmsN : ∀ i < ms.size, ∀ c < 10, ms[i]![c]! < 1024) {i j : Nat} (hi : i < ms.size)
    (hj : j < ms.size) (hij : fn ms[i]! = fn ms[j]!) : i = j := by
  have h1 : fcMatEq ms[i]! ms[j]! = true :=
    fcMatEq_iff.2 fun c hc => col_eq_of_fn_eq (hmsN i hi) (hmsN j hj) hij hc
  simp only [fcDistinct, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h
  rcases h i hi j hj with h2 | h2
  · rw [h1] at h2
    exact absurd h2 (by simp)
  · exact h2

theorem fcRows_spec {rows ms : Array (Array Nat)}
    (h : (rows.map (fcIdx ms)).all (· < ms.size) = true) {k : Nat} (hk : k < rows.size) :
    fcIdx ms rows[k]! < ms.size ∧ ∀ c < 10, rows[k]![c]! = ms[fcIdx ms rows[k]!]![c]! := by
  have hk' : k < (rows.map (fcIdx ms)).size := by simpa using hk
  have h1 : fcIdx ms rows[k]! < ms.size := by
    simpa [getElem!_pos rows k hk] using Array.all_eq_true.1 h k hk'
  exact ⟨h1, fcIdx_spec h1⟩

theorem mem_fcHits {ia : Array Nat} {n x : Nat} : x ∈ fcHits ia n ↔ x < n ∧ x ∈ ia := by
  simp [fcHits]

theorem fcCover_spec {tab : Array (Array Nat)} {A B : List Nat} {n : Nat}
    (h : fcCover tab A B n = true) {i : Nat} (hi : i < n) :
    ∃ x ∈ A, ∃ y ∈ B, tab[x]![y]! = i := by
  simp only [fcCover, List.all_eq_true, List.mem_range, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h i hi
  exact ⟨x, hx, y, hy, hxy⟩

theorem mem_fcExt {tab : Array (Array Nat)} {Y : List Nat} {y i : Nat} :
    i ∈ fcExt tab Y y ↔ i ∈ Y ∨ ∃ x ∈ Y, i = tab[y]![x]! := by
  simp [fcExt, List.mem_mergeSort, eq_comm]

theorem fcExtOK_spec {tab : Array (Array Nat)} {e n : Nat} {fam : List (List Nat)}
    (h : fcExtOK tab e n fam = true) {Y : List Nat} (hY : Y ∈ fam) {y : Nat} (hy : y < n)
    (hyy : tab[y]![y]! = e) (hyY : y ∉ Y) (hc : ∀ x ∈ Y, tab[y]![x]! = tab[x]![y]!) :
    fcExt tab Y y ∈ fam := by
  simp only [fcExtOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  have h1 := h Y hY y hy
  have h2 : Y.contains y = false := by simpa using hyY
  have h3 : (Y.all fun x => tab[y]![x]! == tab[x]![y]!) = true := by
    simpa [List.all_eq_true] using hc
  simp only [hyy, h2, h3] at h1
  simpa using h1

theorem fcFixOK_spec {act : Array (Array Nat)} {e : Nat} {fam : List (List Nat)}
    (h : fcFixOK act e fam = true) {Z : List Nat} (hZ : Z ∈ fam) :
    Z = [e] ∨ Z.length * fcFix act Z ≤ 2 ^ 9 := by
  simp only [fcFixOK, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h Z hZ

end CFSG.EvenSporadicStandard.TwoFi22.DS81
