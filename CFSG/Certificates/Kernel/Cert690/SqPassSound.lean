module

public import Certificates.Data.Kernel.Cert690.SqPass
public import CFSG.Certificates.Kernel.Cert690.SqSound
public import CFSG.Certificates.Kernel.Cert690.TreeSound

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

theorem bitK_eq (m p : ℕ) : bitK m p = m.testBit p := by
  have e : bitK m p = Nat.beq ((m >>> p) % 2) 1 := by
    unfold bitK
    rw [← Nat.and_one_is_mod]
    rfl
  rw [e, Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (m >>> p) with h | h <;> rw [h] <;> rfl

theorem testBit_lor_one_shiftLeft (m k p : ℕ) :
    (m ||| 1 <<< k).testBit p = (m.testBit p || decide (p = k)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : p = k
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem passL_spec (W : IT) (n M : ℕ) : ∀ (ks : List ℕ) (j m : ℕ), passL W n M ks j m = true →
    (∀ k ∈ ks, k < n) ∧ (∀ p, M.testBit p = (m.testBit p || decide (p ∈ ks))) ∧
      ∀ p ∈ ks, m.testBit p = false → W.find p n = j + ks.idxOf p
  | [], j, m, h => by
    have h' : Nat.beq m M = true := h
    rw [Nat.beq_eq] at h'
    subst h'
    exact ⟨by simp, by simp, by simp⟩
  | k :: ks, j, m, h => by
    have h' : bAnd(Nat.blt k n,
        bIf(bitK m k, passL W n M ks (j + 1) m,
          bAnd(Nat.beq (W.find k n) j, passL W n M ks (j + 1) (m ||| 1 <<< k)))) = true := h
    rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, bitK_eq] at h'
    obtain ⟨hk, h'⟩ := h'
    cases hb : m.testBit k with
    | true =>
      rw [hb] at h'
      obtain ⟨h1, h2, h3⟩ := passL_spec W n M ks (j + 1) m h'
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hk
        · exact h1 x hx
      · intro p
        rw [h2 p]
        by_cases hp : p = k
        · subst hp
          simp [hb]
        · simp [hp]
      · intro p hp hpm
        have hpk : p ≠ k := by
          rintro rfl
          rw [hb] at hpm
          exact Bool.noConfusion hpm
        have hp' : p ∈ ks := (List.mem_cons.1 hp).resolve_left hpk
        rw [h3 p hp' hpm, List.idxOf_cons_ne _ (Ne.symm hpk)]
        omega
    | false =>
      rw [hb] at h'
      have h'' : (Nat.beq (W.find k n) j && passL W n M ks (j + 1) (m ||| 1 <<< k)) = true := by
        rw [← bAnd_eq]
        exact h'
      rw [Bool.and_eq_true, Nat.beq_eq] at h''
      obtain ⟨hW, h''⟩ := h''
      obtain ⟨h1, h2, h3⟩ := passL_spec W n M ks (j + 1) _ h''
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hk
        · exact h1 x hx
      · intro p
        rw [h2 p, testBit_lor_one_shiftLeft]
        by_cases hp : p = k
        · subst hp
          simp
        · simp [hp]
      · intro p hp hpm
        by_cases hpk : p = k
        · subst hpk
          rw [List.idxOf_cons_self, hW]
          omega
        · have hp' : p ∈ ks := (List.mem_cons.1 hp).resolve_left hpk
          have hpm' : (m ||| 1 <<< k).testBit p = false := by
            rw [testBit_lor_one_shiftLeft, hpm]
            simp [hpk]
          rw [h3 p hp' hpm', List.idxOf_cons_ne _ (Ne.symm hpk)]
          omega

theorem find?_range_eq (q : ℕ) : ∀ (l : List ℕ) (P : ℕ → Bool),
    (∀ j (hj : j < l.length), P j = (l[j] == q)) →
      (List.range l.length).find? P = if q ∈ l then some (l.idxOf q) else none
  | [], _, _ => by simp
  | a :: l, P, hP => by
    rw [List.length_cons, List.range_succ_eq_map, List.find?_cons]
    have h0 : P 0 = (a == q) := hP 0 (by simp)
    rw [h0]
    by_cases ha : a = q
    · subst ha
      simp
    · have hb : (a == q) = false := by simpa using ha
      rw [hb, List.find?_map]
      have ih := find?_range_eq q l (P ∘ Nat.succ) (fun j hj => by
        have h1 := hP (j + 1) (by rw [List.length_cons]; omega)
        rw [List.getElem_cons_succ] at h1
        exact h1)
      rw [ih]
      by_cases hq : q ∈ l
      · rw [if_pos hq, if_pos (List.mem_cons_of_mem a hq), List.idxOf_cons_ne _ ha]
        rfl
      · rw [if_neg hq, if_neg (by simp [Ne.symm ha, hq])]
        rfl

theorem firstConj_of_passGo {E inv : List ℕ} {T W : IT} {M r : ℕ} (hnd : E.Nodup)
    (hT : ∀ c, T.find c E.length = E.idxOf c) (h : passGo T W E.length M r E inv = true)
    (i y : ℕ) : firstConj E.toArray inv.toArray i r y =
      if M.testBit (T.find y E.length) then some (i, E[W.find (T.find y E.length) E.length]!)
      else none := by
  have h' : (Nat.beq E.length inv.length && passL W E.length M
      (List.zipWith (fun x y => T.find (mulF (mulF x r) y) E.length) E inv) 0 0) = true := by
    rw [← bAnd_eq]
    exact h
  rw [Bool.and_eq_true, Nat.beq_eq] at h'
  obtain ⟨hl, hp⟩ := h'
  obtain ⟨hlt, hM, hW⟩ := passL_spec W E.length M _ 0 0 hp
  set ks := List.zipWith (fun x y => T.find (mulF (mulF x r) y) E.length) E inv with hks
  have hkl : ks.length = E.length := by simp [hks, hl]
  have hkj : ∀ j (hj : j < ks.length), ks[j] = E.idxOf (mulF (mulF (E[j]'(by omega)) r)
      (inv[j]'(by omega))) := by
    intro j hj
    simp [hks, List.getElem_zipWith, hT]
  have hmem : ∀ j (hj : j < ks.length),
      mulF (mulF (E[j]'(by omega)) r) (inv[j]'(by omega)) ∈ E := by
    intro j hj
    have := hlt _ (List.getElem_mem hj)
    rw [hkj j hj] at this
    exact List.idxOf_lt_length_iff.1 this
  unfold firstConj
  rw [hT y]
  have hfind := find?_range_eq (E.idxOf y) ks
    (fun j => Code.mul (Code.mul (E.toArray[j]!) r) (inv.toArray[j]!) == y) (by
      intro j hj
      have hjE : j < E.length := by omega
      have hjI : j < inv.length := by omega
      rw [getElem!_pos E.toArray j (by simpa using hjE),
        getElem!_pos inv.toArray j (by simpa using hjI)]
      simp only [List.getElem_toArray, ← mulF_eq]
      rw [hkj j hj]
      have hm := hmem j hj
      by_cases hy : mulF (mulF (E[j]'hjE) r) (inv[j]'hjI) = y
      · rw [hy]
        simp
      · have hne : E.idxOf (mulF (mulF (E[j]'hjE) r) (inv[j]'hjI)) ≠ E.idxOf y := by
          intro he
          apply hy
          have h1 := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hm)
          by_cases hyE : y ∈ E
          · have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hyE)
            simp only [he] at h1
            rw [← h1, h2]
          · have := List.idxOf_lt_length_iff.2 hm
            rw [he, List.idxOf_eq_length hyE] at this
            omega
        simp [hy, hne])
  rw [hkl] at hfind
  rw [List.size_toArray, hfind, hM]
  simp only [Nat.zero_testBit, Bool.false_or]
  by_cases hq : E.idxOf y ∈ ks
  · have hql := List.idxOf_lt_length_iff.2 hq
    rw [if_pos hq, if_pos (by simpa using hq), Option.map_some, hW _ hq (Nat.zero_testBit _),
      Nat.zero_add, getElem!_pos E.toArray (ks.idxOf (E.idxOf y)) (by simp; omega),
      getElem!_pos E (ks.idxOf (E.idxOf y)) (by omega)]
    simp
  · rw [if_neg hq, if_neg (by simpa using hq)]
    rfl

end CFSG.KC.C690

end
