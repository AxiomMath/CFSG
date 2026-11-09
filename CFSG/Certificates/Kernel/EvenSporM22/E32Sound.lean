module

public import Certificates.Data.Kernel.EvenSporM22.E32Defs

public section

namespace CFSG.KC.EvenSporM22

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.EvenSporadicStandard.M22Std.E32Check

theorem tabLE_nil (b : Tab) : tabLE [] b = true := by
  cases b <;> rfl

theorem tabLE_cons_nil (a : Nat) (s : Tab) : tabLE (a :: s) [] = false := rfl

theorem tabLE_cons (a b : Nat) (s t : Tab) :
    tabLE (a :: s) (b :: t) = true ↔ a < b ∨ (a = b ∧ tabLE s t = true) := by
  change (if a < b then true else if a = b then tabLE s t else false) = true ↔ _
  by_cases h : a < b
  · simp [h]
  · by_cases h' : a = b
    · subst h'
      simp
    · simp [h, h']

theorem tabLE_total : ∀ a b : Tab, tabLE a b = true ∨ tabLE b a = true
  | [], b => Or.inl (tabLE_nil b)
  | _ :: _, [] => Or.inr (tabLE_nil _)
  | a :: s, b :: t => by
    rw [tabLE_cons, tabLE_cons]
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact Or.inl (Or.inl h)
    · subst h
      rcases tabLE_total s t with h' | h'
      · exact Or.inl (Or.inr ⟨rfl, h'⟩)
      · exact Or.inr (Or.inr ⟨rfl, h'⟩)
    · exact Or.inr (Or.inl h)

theorem tabLE_trans : ∀ a b c : Tab, tabLE a b = true → tabLE b c = true → tabLE a c = true
  | [], _, c, _, _ => tabLE_nil c
  | _ :: _, [], _, h, _ => by simp [tabLE_cons_nil] at h
  | _ :: _, _ :: _, [], _, h => by simp [tabLE_cons_nil] at h
  | a :: s, b :: t, c :: u, h1, h2 => by
    rw [tabLE_cons] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (by omega)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, tabLE_trans s t u h1 h2⟩

theorem tabLE_antisymm : ∀ a b : Tab, tabLE a b = true → tabLE b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [tabLE_cons_nil] at h
  | _ :: _, [], h, _ => by simp [tabLE_cons_nil] at h
  | a :: s, b :: t, h1, h2 => by
    rw [tabLE_cons] at h1 h2
    rcases h1 with h1 | ⟨rfl, h1⟩
    · rcases h2 with h2 | ⟨h2, _⟩ <;> omega
    · rcases h2 with h2 | ⟨_, h2⟩
      · omega
      · rw [tabLE_antisymm s t h1 h2]

abbrev tabR (a b : Tab) : Prop := tabLE a b = true

instance : Std.Total tabR := ⟨tabLE_total⟩
instance : IsTrans Tab tabR := ⟨tabLE_trans⟩
instance : Std.Antisymm tabR := ⟨tabLE_antisymm⟩

theorem insK_eq (a : Tab) : ∀ l : List Tab, insK a l = l.orderedInsert tabR a
  | [] => by rw [List.orderedInsert_nil]; rfl
  | b :: l => by
    rw [List.orderedInsert_cons, ← insK_eq a l]
    rfl

theorem isortK_eq : ∀ l : List Tab, isortK l = l.insertionSort tabR
  | [] => by rw [List.insertionSort_nil]; rfl
  | b :: l => by
    rw [List.insertionSort_cons, ← isortK_eq l, ← insK_eq]
    rfl

theorem sortTabs_eq (L : List Tab) : sortTabs L = isortK L := by
  have h := List.mergeSort_eq_insertionSort (r := tabR) L
  have e : (fun a b : Tab => decide (tabR a b)) = tabLE := by
    funext a b
    simp [tabR]
  rw [e] at h
  rw [isortK_eq]
  exact h

theorem stepOK_iff (T : List Tab) (k : Nat) : StepOK T k ↔ StepOKK T k := by
  simp only [StepOK, StepOKK, sortTabs_eq]

theorem jTabs_eqK : jTabs = jTabsK := by
  rw [jTabs_eq, jTabsK]

theorem checkProp_iff : CheckProp ↔ CheckPropK := by
  simp only [CheckProp, CheckPropK, CheckRest, CheckRestK, jTabs_eqK, stepOK_iff]

theorem xProp_iff : xProp ↔ xPropK := by
  simp only [xProp, xPropK, jTabs_eqK]

theorem check_of (h : CheckPropK) : check = true := by
  unfold check
  exact decide_eq_true (checkProp_iff.2 h)

theorem xCheck_of (h : xPropK) : xCheck = true := by
  unfold xCheck
  exact decide_eq_true (xProp_iff.2 h)

end CFSG.KC.EvenSporM22
