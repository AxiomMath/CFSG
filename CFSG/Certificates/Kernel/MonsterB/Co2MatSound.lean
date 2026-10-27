module

public import Certificates.Data.Kernel.MonsterB.Co2Word
public import CFSG.Certificates.Kernel.MonsterB.Co2PermSound

public section

namespace CFSG.KC.Co2Mem

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2

theorem permF_sound (n : ℕ) (g : ℕ → ℕ) : ∀ (k M : ℕ), permF n g k M = true →
    (∀ a < k, g a < n ∧ M.testBit (g a) = false) ∧ ∀ a b, a < k → b < k → g a = g b → a = b := by
  intro k
  induction k with
  | zero =>
    intro M _
    exact ⟨fun a ha => absurd ha (Nat.not_lt_zero a), fun a _ ha => absurd ha (Nat.not_lt_zero a)⟩
  | succ k ih =>
    intro M h
    change permStep n (g k) (permF n g k) M = true at h
    rw [permStep, CFSG.KC.U6Orb.andB_eq_true, CFSG.KC.U6Orb.andB_eq_true,
      CFSG.KC.U6Orb.notB_eq, CFSG.KC.U6Orb.strictB_eq, CFSG.KC.U6Orb.bit_eq, Nat.blt_eq,
      CFSG.KC.U6Orb.pw2_eq] at h
    obtain ⟨hlt, hbit, hrest⟩ := h
    obtain ⟨h1, h2⟩ := ih _ hrest
    have hbit' : M.testBit (g k) = false := by simpa using hbit
    have hne : ∀ a < k, g a ≠ g k := by
      intro a ha e
      have := (h1 a ha).2
      rw [e, testBit_lor, Nat.testBit_two_pow_self, Bool.or_true] at this
      exact Bool.noConfusion this
    refine ⟨fun a ha => ?_, fun a b ha hb e => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · have := (h1 a ha).2
        rw [testBit_lor, Bool.or_eq_false_iff] at this
        exact ⟨(h1 a ha).1, this.1⟩
      · exact ⟨hlt, hbit'⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · exact h2 a b ha hb e
      · exact absurd e (hne a ha)
      · exact absurd e.symm (hne b hb)
      · rfl

theorem lt_of_sorted {n : ℕ} {g S : ℕ → ℕ} (h : ∀ k, k + 1 < n → g (S k) < g (S (k + 1))) :
    ∀ i j, i < j → j < n → g (S i) < g (S j) := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h1 | rfl
    · exact lt_trans (ih h1 (by omega)) (h j hj)
    · exact h i hj

theorem inj_of_sorted {n : ℕ} {g S : ℕ → ℕ} (hS : ∀ k < n, S k < n)
    (hSi : ∀ a b, a < n → b < n → S a = S b → a = b)
    (h : ∀ k, k + 1 < n → g (S k) < g (S (k + 1))) :
    ∀ a b, a < n → b < n → g a = g b → a = b := by
  let f : Fin n → Fin n := fun k => ⟨S k, hS k k.2⟩
  have hf : Function.Injective f := fun a b e =>
    Fin.ext (hSi a b a.2 b.2 (congrArg Fin.val e))
  have hsurj := Finite.injective_iff_surjective.1 hf
  intro a b ha hb e
  obtain ⟨i, hi⟩ := hsurj ⟨a, ha⟩
  obtain ⟨j, hj⟩ := hsurj ⟨b, hb⟩
  have hia : S i = a := congrArg Fin.val hi
  have hjb : S j = b := congrArg Fin.val hj
  rcases Nat.lt_trichotomy i j with hl | he | hl
  · have := lt_of_sorted h i j hl j.2
    rw [hia, hjb, e] at this
    exact absurd this (lt_irrefl _)
  · rw [← hia, ← hjb, Fin.ext he]
  · have := lt_of_sorted h j i hl i.2
    rw [hia, hjb, e] at this
    exact absurd this (lt_irrefl _)

theorem compA_get {n : ℕ} {t u : Array ℕ} {x : ℕ} (hx : x < n) :
    (Native.compA n t u)[x]! = t[u[x]!]! := by
  rw [Native.compA, getElem!_pos _ _ (by simpa using hx), Array.getElem_ofFn]

theorem idA_get {n x : ℕ} (hx : x < n) : (Native.idA n)[x]! = x := by
  rw [Native.idA, getElem!_pos _ _ (by simpa using hx), Array.getElem_ofFn]

theorem eqA_iff {n : ℕ} {t u : Array ℕ} : Native.eqA n t u = true ↔ ∀ i < n, t[i]! = u[i]! := by
  unfold Native.eqA
  rw [allLt_iff]
  simp only [beq_iff_eq]

theorem iterK_succ (f : ℕ → ℕ) (e x : ℕ) : iterK f (e + 1) x = f (iterK f e x) := rfl

theorem powA_get {t : Array ℕ} (ht : ∀ y < 2300, t[y]! < 2300) :
    ∀ e x, x < 2300 → (Native.powA t e)[x]! = iterK (fun y => t[y]!) e x ∧
      iterK (fun y => t[y]!) e x < 2300 := by
  intro e
  induction e with
  | zero => intro x hx; exact ⟨idA_get (n := Native.deg ()) hx, hx⟩
  | succ e ih =>
    intro x hx
    obtain ⟨h1, h2⟩ := ih x hx
    rw [Native.powA, compA_get (n := Native.deg ()) hx, h1, iterK_succ]
    exact ⟨rfl, ht _ h2⟩

@[expose] def wordEval (w : List ℤ) (x : ℕ) : ℕ := w.foldl (fun y l => (Native.permLetter l)[y]!) x

theorem wordPermA_get : ∀ w, (∀ l ∈ w, ∀ y < 2300, (Native.permLetter l)[y]! < 2300) →
    ∀ x, x < 2300 → (Native.wordPermA w)[x]! = wordEval w x ∧ wordEval w x < 2300 := by
  intro w
  induction w with
  | nil => intro _ x hx; exact ⟨idA_get (n := Native.deg ()) hx, hx⟩
  | cons l w ih =>
    intro hl x hx
    obtain ⟨h1, h2⟩ := ih (fun l' hl' => hl l' (List.mem_cons_of_mem _ hl')) _
      (hl l (List.mem_cons_self) x hx)
    rw [Native.wordPermA, compA_get (n := Native.deg ()) hx, h1]
    exact ⟨rfl, h2⟩

theorem wordK_eq {P PI : ℕ → ℕ} : ∀ w, (∀ l ∈ w, ∀ y < 2300,
    letterK P PI l y = (Native.permLetter l)[y]! ∧ (Native.permLetter l)[y]! < 2300) →
    ∀ x, x < 2300 → wordK P PI w x = wordEval w x := by
  intro w
  induction w with
  | nil => intro _ x _; rfl
  | cons l w ih =>
    intro hl x hx
    change wordK P PI w (letterK P PI l x) = wordEval w ((Native.permLetter l)[x]!)
    rw [(hl l List.mem_cons_self x hx).1]
    exact ih (fun l' hl' => hl l' (List.mem_cons_of_mem _ hl')) _
      (hl l List.mem_cons_self x hx).2

theorem iterK_congr {f g : ℕ → ℕ} (h : ∀ y < 2300, f y = g y ∧ f y < 2300) :
    ∀ e x, x < 2300 → iterK f e x = iterK g e x ∧ iterK f e x < 2300 := by
  intro e
  induction e with
  | zero => intro x hx; exact ⟨rfl, hx⟩
  | succ e ih =>
    intro x hx
    obtain ⟨h1, h2⟩ := ih x hx
    rw [iterK_succ, iterK_succ, ← h1]
    exact h _ h2

end CFSG.KC.Co2Mem

end
