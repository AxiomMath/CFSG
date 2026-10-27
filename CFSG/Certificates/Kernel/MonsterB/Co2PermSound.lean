module

public import Certificates.Data.Kernel.MonsterB.Co2Perm
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.KC.Co2Mem

open CFSG.KC.Enum CFSG.KS CFSG.KLie.CT CFSG.KC.U6Orb

theorem permGo_succ (n w X k : Nat) (M : Nat) :
    permGo n w X (k + 1) M = permStep n (pg w (mask w) X k) (permGo n w X k) M := rfl

theorem testBit_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i

theorem permGo_sound (n w X : Nat) : ∀ (k M : Nat), permGo n w X k M = true →
    (∀ a < k, pg w (mask w) X a < n ∧ M.testBit (pg w (mask w) X a) = false) ∧
      ∀ a b, a < k → b < k → pg w (mask w) X a = pg w (mask w) X b → a = b := by
  intro k
  induction k with
  | zero =>
    intro M _
    exact ⟨fun a ha => absurd ha (Nat.not_lt_zero a), fun a _ ha => absurd ha (Nat.not_lt_zero a)⟩
  | succ k ih =>
    intro M h
    rw [permGo_succ, permStep, andB_eq_true, andB_eq_true, notB_eq, strictB_eq, bit_eq,
      Nat.blt_eq, pw2_eq] at h
    obtain ⟨hlt, hbit, hrest⟩ := h
    obtain ⟨h1, h2⟩ := ih _ hrest
    have hbit' : M.testBit (pg w (mask w) X k) = false := by simpa using hbit
    have hne : ∀ a < k, pg w (mask w) X a ≠ pg w (mask w) X k := by
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

theorem permK_sound {n w X : Nat} (h : permK n w X = true) :
    (∀ a < n, pg w (mask w) X a < n) ∧
      ∀ a b, a < n → b < n → pg w (mask w) X a = pg w (mask w) X b → a = b := by
  obtain ⟨h1, h2⟩ := permGo_sound n w X n 0 h
  exact ⟨fun a ha => (h1 a ha).1, h2⟩

theorem foldl_set_spec {m d : Nat} {g : Nat → Nat} {n : Nat} (hb : ∀ i < n, g i < m)
    (hi : ∀ i j, i < n → j < n → g i = g j → i = j) : ∀ k ≤ n,
    ((List.range' 0 k).foldl (fun r i => r.set! (g i) i) (Array.replicate m d)).size = m ∧
      ∀ i < k, ((List.range' 0 k).foldl (fun r i => r.set! (g i) i) (Array.replicate m d))[g i]! =
        i := by
  intro k
  induction k with
  | zero => intro _; exact ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
    intro hk
    obtain ⟨hs, h⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    generalize List.foldl (fun r i => r.set! (g i) i) (Array.replicate m d) (List.range' 0 k) = r
      at hs h
    refine ⟨by simp [hs], fun i hi' => ?_⟩
    have hti : g i < r.size := by
      rw [hs]
      exact hb i (by omega)
    simp only [Array.set!_eq_setIfInBounds]
    rw [getElem!_pos _ _ (by simpa using hti), Array.getElem_setIfInBounds]
    by_cases e : g k = g i
    · obtain rfl : k = i := hi k i hk (by omega) e
      simp
    · have hik : i < k := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h' | rfl
        · exact h'
        · exact absurd rfl e
      simp only [e, ite_false]
      rw [← getElem!_pos r _ hti]
      exact h i hik
    exact hti

open CFSG.Monster.B.Co2 in
theorem invCand_spec {n : Nat} {t : Array Nat} (hb : ∀ i < n, t[i]! < n)
    (hi : ∀ i j, i < n → j < n → t[i]! = t[j]! → i = j) :
    ∀ i < n, (Native.invCand n t)[t[i]!]! = i := by
  have e : Native.invCand n t =
      (List.range' 0 n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
    simp [Native.invCand, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
      List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size]
    rfl
  intro i hin
  rw [e]
  exact (foldl_set_spec (g := fun i => t[i]!) hb hi n le_rfl).2 i hin

open CFSG.Monster.B.Co2 in
theorem isInvA_invCand {n : Nat} {t : Array Nat} (hb : ∀ i < n, t[i]! < n)
    (hi : ∀ i j, i < n → j < n → t[i]! = t[j]! → i = j) :
    Native.isInvA n t (Native.invCand n t) = true := by
  unfold Native.isInvA
  rw [allLt_iff]
  intro i hin
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨hb i hin, invCand_spec hb hi i hin⟩

end CFSG.KC.Co2Mem

end
