module

public import CFSG.Certificates.Kernel.Common.Loop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace CFSG.Certificates.DceLoop

open CFSG.KC.Loop

theorem strictN_eq (v : ℕ) (k : ℕ → ℕ) : strictN v k = k v := by
  cases v <;> rfl

theorem band_iff (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) false b a = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem bor_iff (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) b true a = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem bnot_iff (b : Bool) : Bool.rec (motive := fun _ => Bool) true false b = true ↔ b = false := by
  cases b <;> decide

theorem brec_true {α : Sort*} (a b : α) : Bool.rec (motive := fun _ => α) a b true = b := rfl

theorem brec_false {α : Sort*} (a b : α) : Bool.rec (motive := fun _ => α) a b false = a := rfl

@[expose] noncomputable def bitsG (J o x : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight J o) (Nat.sub (Nat.shiftLeft (nat_lit 1) x) (nat_lit 1))

theorem bitsG_eq (J o x : ℕ) : bitsG J o x = J / 2 ^ o % 2 ^ x := by
  unfold bitsG
  change (J >>> o) &&& ((1 <<< x) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem bitsG_lt (J o x : ℕ) : bitsG J o x < 2 ^ x := by
  rw [bitsG_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos x)

@[expose] noncomputable def byteG (x i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight x (Nat.mul (nat_lit 8) i)) (nat_lit 255)

theorem land_low (x k : ℕ) : x &&& (2 ^ k - 1) = x % 2 ^ k := Nat.and_two_pow_sub_one_eq_mod x k

theorem lor_shl_mod (a b k : ℕ) : (a ||| b <<< k) % 2 ^ k = a % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < k
  · simp [hi]
  · simp [hi]

theorem lor_shl_shr (a b k : ℕ) : (a ||| b <<< k) >>> k = (a >>> k) ||| b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  simp

theorem le_lor_right (a b : ℕ) : b ≤ a ||| b := by
  rw [Nat.lor_comm]
  exact Nat.left_le_or

@[expose] noncomputable def cntStep (ok : ℕ → ℕ → Bool) (adv : ℕ → ℕ) (ih : ℕ → ℕ → ℕ) (J S : ℕ) :
    ℕ :=
  strictN (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (Nat.succ S)
      (Bool.rec (motive := fun _ => Bool) false (ok (Nat.sub S (nat_lit 1)) J)
        (Nat.blt (nat_lit 0) S)))
    (ih (Nat.shiftRight J (adv J)))

@[expose] noncomputable def cntInner (ok : ℕ → ℕ → Bool) (adv : ℕ → ℕ) (n J S : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
    (fun _ ih J S => cntStep ok adv ih J S) n J S

@[expose] noncomputable def cntRun (ok : ℕ → ℕ → Bool) (adv : ℕ → ℕ) (cm cs : ℕ) (Cs : List ℕ) :
    ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun C _ ih S => strictN (cntInner ok adv (Nat.land C cm) (Nat.shiftRight C cs) S) ih) Cs

@[expose] def CntOK (ok : ℕ → ℕ → Bool) (a S : ℕ) : Prop := ∀ k, a ≤ k → k + 1 < S → ∃ J, ok k J = true

theorem cntInner_ok (ok : ℕ → ℕ → Bool) (adv : ℕ → ℕ) (a : ℕ) : ∀ (n J S : ℕ), CntOK ok a S →
    CntOK ok a (cntInner ok adv n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change CntOK ok a (cntStep ok adv (cntInner ok adv n) J S)
    unfold cntStep
    rw [strictN_eq]
    apply cntInner_ok ok adv a n
    cases hc : Bool.rec (motive := fun _ => Bool) false (ok (Nat.sub S (nat_lit 1)) J)
        (Nat.blt (nat_lit 0) S)
    · intro k _ hk
      exact absurd hk (Nat.not_lt_zero _)
    · rw [band_iff, Nat.blt_eq] at hc
      intro k hak hk
      change k + 1 < S + 1 at hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact h k hak hk
      · refine ⟨J, ?_⟩
        have e : k = Nat.sub S 1 := by
          change k = S - 1
          omega
        rw [e]
        exact hc.2

theorem cntRun_ok (ok : ℕ → ℕ → Bool) (adv : ℕ → ℕ) (cm cs a : ℕ) : ∀ (Cs : List ℕ) (S : ℕ),
    CntOK ok a S → CntOK ok a (cntRun ok adv cm cs Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change CntOK ok a (strictN (cntInner ok adv (Nat.land C cm) (Nat.shiftRight C cs) S)
      (cntRun ok adv cm cs Cs))
    rw [strictN_eq]
    exact cntRun_ok ok adv cm cs a Cs _ (cntInner_ok ok adv a _ _ _ h)

theorem cntRun_spec {ok : ℕ → ℕ → Bool} {adv : ℕ → ℕ} {cm cs a n : ℕ} {Cs : List ℕ}
    (h : cntRun ok adv cm cs Cs (a + 1) = n + 1) : ∀ k, a ≤ k → k < n → ∃ J, ok k J = true := by
  have hi := cntRun_ok ok adv cm cs a Cs (a + 1) (fun k hk h2 => absurd h2 (by omega))
  rw [h] at hi
  exact fun k hk hkn => hi k hk (by omega)

@[expose] noncomputable def sortStep (get : ℕ → ℕ) (qb m : ℕ) (ih : ℕ → ℕ → ℕ) (J S : ℕ) : ℕ :=
  (fun q => strictN (Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
      (Nat.lor (Nat.succ (Nat.land S (nat_lit 1048575))) (Nat.shiftLeft (get q) (nat_lit 20)))
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Nat.blt (Nat.shiftRight S (nat_lit 20)) (get q)) (Nat.blt q m))
        (Nat.blt (nat_lit 0) S)))
    (ih (Nat.shiftRight J qb))) (bitsG J (nat_lit 0) qb)

@[expose] noncomputable def sortRun (get : ℕ → ℕ) (qb m : ℕ) (Cs : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih2 J S => sortStep get qb m ih2 J S)
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] def SortInv (get : ℕ → ℕ) (m S : ℕ) : Prop :=
  S = 0 ∨ ∃ L : List ℕ, (∀ q ∈ L, q < m ∧ 0 < get q ∧ get q ≤ S >>> 20) ∧
    L.Pairwise (fun a b => get b < get a) ∧ S % 2 ^ 20 ≤ L.length + 1

theorem m20_eq : (1048575 : ℕ) = 2 ^ 20 - 1 := rfl

theorem sortOne_inv (get : ℕ → ℕ) (m q S : ℕ) (h : SortInv get m S) :
    SortInv get m (Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
      (Nat.lor (Nat.succ (Nat.land S (nat_lit 1048575))) (Nat.shiftLeft (get q) (nat_lit 20)))
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Nat.blt (Nat.shiftRight S (nat_lit 20)) (get q)) (Nat.blt q m))
        (Nat.blt (nat_lit 0) S))) := by
  cases hc : Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (Nat.blt (Nat.shiftRight S (nat_lit 20)) (get q)) (Nat.blt q m)) (Nat.blt (nat_lit 0) S)
  · exact Or.inl rfl
  rw [band_iff, band_iff, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq] at hc
  obtain ⟨hS, hq, hv⟩ := hc
  change S >>> 20 < get q at hv
  rcases h with h | ⟨L, hL, hP, hc⟩
  · omega
  have hge : get q ≤ (Nat.succ (S &&& 1048575) ||| get q <<< 20) >>> 20 := by
    rw [lor_shl_shr]
    exact le_lor_right _ _
  refine Or.inr ⟨q :: L, ?_, ?_, ?_⟩
  · intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨hq, by omega, hge⟩
    · obtain ⟨h1, h2, h3⟩ := hL r hr
      exact ⟨h1, h2, by change get r ≤ (Nat.succ (S &&& 1048575) ||| get q <<< 20) >>> 20; omega⟩
  · refine List.Pairwise.cons (fun b hb => ?_) hP
    have := (hL b hb).2.2
    omega
  · change (Nat.succ (S &&& 1048575) ||| get q <<< 20) % 2 ^ 20 ≤ _
    rw [lor_shl_mod, m20_eq, land_low, List.length_cons]
    have := Nat.mod_le (Nat.succ (S % 2 ^ 20)) (2 ^ 20)
    omega

theorem sortInner_inv (get : ℕ → ℕ) (qb m : ℕ) : ∀ (n J S : ℕ), SortInv get m S →
    SortInv get m (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
      (fun _ ih2 J S => sortStep get qb m ih2 J S) n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change SortInv get m (sortStep get qb m (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
      (fun _ ih2 J S => sortStep get qb m ih2 J S) n) J S)
    unfold sortStep
    dsimp only
    rw [strictN_eq]
    exact sortInner_inv get qb m n _ _ (sortOne_inv get m _ S h)

theorem sortRun_inv (get : ℕ → ℕ) (qb m : ℕ) : ∀ (Cs : List ℕ) (S : ℕ), SortInv get m S →
    SortInv get m (sortRun get qb m Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change SortInv get m (strictN (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih2 J S => sortStep get qb m ih2 J S)
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) (sortRun get qb m Cs))
    rw [strictN_eq]
    exact sortRun_inv get qb m Cs _ (sortInner_inv get qb m _ _ _ h)

theorem sortRun_spec {get : ℕ → ℕ} {qb m S1 : ℕ} {Cs : List ℕ} (h : sortRun get qb m Cs 1 = S1)
    (hc : Nat.sub (Nat.land S1 (nat_lit 1048575)) (nat_lit 1) = m) :
    (∀ q < m, 0 < get q) ∧ ∀ q < m, ∀ q' < m, get q = get q' → q = q' := by
  classical
  have h1 : SortInv get m 1 := Or.inr ⟨[], by simp, List.Pairwise.nil, by norm_num⟩
  have hi := sortRun_inv get qb m Cs 1 h1
  rw [h] at hi
  change (S1 &&& 1048575) - 1 = m at hc
  rw [m20_eq, land_low] at hc
  rcases hi with h0 | ⟨L, hL, hP, hcnt⟩
  · subst h0
    have : m = 0 := by simpa using hc.symm
    subst this
    exact ⟨fun q hq => absurd hq (Nat.not_lt_zero _), fun q hq => absurd hq (Nat.not_lt_zero _)⟩
  have hne : L.Pairwise (fun a b => get a ≠ get b) := hP.imp (fun h => (Nat.ne_of_lt h).symm)
  have hnd : L.Nodup := hne.imp (fun h e => h (congrArg get e))
  have hsub : L.toFinset ⊆ Finset.range m := fun q hq =>
    Finset.mem_range.2 (hL q (List.mem_toFinset.1 hq)).1
  have hcard : (Finset.range m).card ≤ L.toFinset.card := by
    rw [Finset.card_range, List.toFinset_card_of_nodup hnd]
    omega
  have heq : L.toFinset = Finset.range m := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : ∀ q < m, q ∈ L := fun q hq => by
    have : q ∈ L.toFinset := by
      rw [heq]
      exact Finset.mem_range.2 hq
    exact List.mem_toFinset.1 this
  have hnd' : (L.map get).Nodup := List.pairwise_map.2 hne
  exact ⟨fun q hq => (hL q (hmem q hq)).2.1, fun q hq q' hq' e =>
    List.inj_on_of_nodup_map hnd' (hmem q hq) (hmem q' hq') e⟩

@[expose] noncomputable def aliveG (AL D : ℕ) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land AL (Nat.shiftLeft (nat_lit 1) D))

theorem aliveG_iff (AL D : ℕ) : aliveG AL D = true ↔ AL.testBit D = true := by
  unfold aliveG
  rw [Nat.blt_eq]
  change 0 < AL &&& 1 <<< D ↔ _
  rw [Nat.one_shiftLeft, Nat.and_two_pow, Nat.pos_iff_ne_zero]
  cases AL.testBit D <;> simp

@[expose] noncomputable def covStep (slot : ℕ → ℕ → ℕ → ℕ → Bool) (NO AL : ℕ) (ih : ℕ → ℕ → ℕ)
    (J S : ℕ) : ℕ :=
  (fun D w => (fun nxt =>
      Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
        (Bool.rec (motive := fun _ => ℕ)
          (strictN nxt (ih J))
          ((fun x => (fun tb => strictN (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) nxt
                (slot D w x (bitsG J (nat_lit 21) tb)))
              (ih (Nat.shiftRight J (Nat.add (nat_lit 21) tb))))
            (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (nat_lit 30)
              (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 1))))
            (bitsG J (nat_lit 0) (nat_lit 21)))
          (aliveG AL D))
        (Nat.blt (nat_lit 0) S))
      (Bool.rec (motive := fun _ => ℕ) (Nat.add S (nat_lit 1))
        (Nat.add (nat_lit 1) (Nat.shiftLeft (Nat.succ D) (nat_lit 20)))
        (Bool.rec (motive := fun _ => Bool) (Nat.beq (Nat.succ w) NO) true
          (Bool.rec (motive := fun _ => Bool) true false (aliveG AL D)))))
    (Nat.shiftRight (Nat.sub S (nat_lit 1)) (nat_lit 20))
    (Nat.land (Nat.sub S (nat_lit 1)) (nat_lit 1048575))

@[expose] noncomputable def coverRun (slot : ℕ → ℕ → ℕ → ℕ → Bool) (NO AL : ℕ) (Cs : List ℕ) :
    ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun C _ ih S => strictN (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih2 J S => covStep slot NO AL ih2 J S)
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) ih) Cs

@[expose] def SlotOK (slot : ℕ → ℕ → ℕ → ℕ → Bool) (D w : ℕ) : Prop := ∃ x h, slot D w x h = true

@[expose] def CovInv (slot : ℕ → ℕ → ℕ → ℕ → Bool) (NO AL S : ℕ) : Prop :=
  S = 0 ∨ ∃ D w, S = 1 + 2 ^ 20 * D + w ∧ w < NO ∧ (w = 0 ∨ AL.testBit D = true) ∧
    (∀ D' < D, AL.testBit D' = true → ∀ w' < NO, SlotOK slot D' w') ∧
    (∀ w' < w, SlotOK slot D w')

theorem covDec {D w : ℕ} (hw : w < 2 ^ 20) :
    Nat.shiftRight (Nat.sub (1 + 2 ^ 20 * D + w) (nat_lit 1)) (nat_lit 20) = D ∧
      Nat.land (Nat.sub (1 + 2 ^ 20 * D + w) (nat_lit 1)) (nat_lit 1048575) = w := by
  have e : Nat.sub (1 + 2 ^ 20 * D + w) (nat_lit 1) = w + 2 ^ 20 * D := by
    change 1 + 2 ^ 20 * D + w - 1 = _
    omega
  rw [e]
  refine ⟨?_, ?_⟩
  · change (w + 2 ^ 20 * D) >>> 20 = D
    rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hw,
      Nat.zero_add]
  · change (w + 2 ^ 20 * D) &&& 1048575 = w
    rw [m20_eq, land_low, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]

theorem covNext_inv {slot : ℕ → ℕ → ℕ → ℕ → Bool} {NO AL D w : ℕ} (hNO0 : 0 < NO) (hw : w < NO)
    (hw0 : w = 0 ∨ AL.testBit D = true)
    (hprev : ∀ D' < D, AL.testBit D' = true → ∀ w' < NO, SlotOK slot D' w')
    (hcur : ∀ w' < w, SlotOK slot D w') (hok : AL.testBit D = true → SlotOK slot D w) :
    CovInv slot NO AL
      (Bool.rec (motive := fun _ => ℕ) (Nat.add (1 + 2 ^ 20 * D + w) (nat_lit 1))
        (Nat.add (nat_lit 1) (Nat.shiftLeft (Nat.succ D) (nat_lit 20)))
        (Bool.rec (motive := fun _ => Bool) (Nat.beq (Nat.succ w) NO) true
          (Bool.rec (motive := fun _ => Bool) true false (aliveG AL D)))) := by
  have e1 : Nat.add (nat_lit 1) (Nat.shiftLeft (Nat.succ D) (nat_lit 20)) =
      1 + 2 ^ 20 * (D + 1) + 0 := by
    change 1 + (D + 1) <<< 20 = _
    rw [Nat.shiftLeft_eq]
    ring
  cases ha : aliveG AL D
  · have hd : AL.testBit D = false := by
      cases e : AL.testBit D
      · rfl
      · rw [← aliveG_iff] at e
        rw [e] at ha
        exact absurd ha (by decide)
    have hw' : w = 0 := hw0.resolve_right (by rw [hd]; decide)
    dsimp only
    rw [e1]
    refine Or.inr ⟨D + 1, 0, rfl, hNO0, Or.inl rfl, fun D' hD' hal w' hw'' => ?_,
      fun w' hw'' => absurd hw'' (Nat.not_lt_zero _)⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hD' with hD' | rfl
    · exact hprev D' hD' hal w' hw''
    · rw [hd] at hal
      exact absurd hal (by decide)
  · have hal : AL.testBit D = true := (aliveG_iff AL D).1 ha
    have hS := hok hal
    dsimp only
    cases hb : Nat.beq (Nat.succ w) NO
    · have hlt : w + 1 < NO := by
        have := Nat.ne_of_beq_eq_false hb
        omega
      dsimp only
      refine Or.inr ⟨D, w + 1, by simp only [Nat.add_eq]; omega, hlt, Or.inr hal,
        hprev, fun w' hw' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hw' with hw' | rfl
      · exact hcur w' hw'
      · exact hS
    · have hlt : w + 1 = NO := Nat.eq_of_beq_eq_true hb
      dsimp only
      rw [e1]
      refine Or.inr ⟨D + 1, 0, rfl, hNO0, Or.inl rfl, fun D' hD' hal' w' hw'' => ?_,
        fun w' hw'' => absurd hw'' (Nat.not_lt_zero _)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hD' with hD' | rfl
      · exact hprev D' hD' hal' w' hw''
      · rcases Nat.lt_succ_iff_lt_or_eq.mp (show w' < w + 1 by omega) with hw3 | rfl
        · exact hcur w' hw3
        · exact hS

theorem covInner_inv {slot : ℕ → ℕ → ℕ → ℕ → Bool} {NO AL : ℕ} (hNO : NO < 2 ^ 20) (hNO0 : 0 < NO) :
    ∀ (n J S : ℕ), CovInv slot NO AL S → CovInv slot NO AL
      (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih2 J S => covStep slot NO AL ih2 J S) n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change CovInv slot NO AL (covStep slot NO AL (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
      (fun _ S => S) (fun _ ih2 J S => covStep slot NO AL ih2 J S) n) J S)
    have ih := covInner_inv (slot := slot) (AL := AL) hNO hNO0 n
    rcases h with rfl | ⟨D, w, rfl, hw, hw0, hprev, hcur⟩
    · exact Or.inl rfl
    obtain ⟨eD, ew⟩ := covDec (D := D) (Nat.lt_trans hw hNO)
    have h1 : 0 < 1 + 2 ^ 20 * D + w := by omega
    have hpos : Nat.blt (nat_lit 0) (1 + 2 ^ 20 * D + w) = true := by
      rw [Nat.blt_eq]
      exact h1
    have hnext := covNext_inv (slot := slot) hNO0 hw hw0 hprev hcur
    unfold covStep
    simp only []
    rw [eD, ew, hpos]
    dsimp only
    cases ha : aliveG AL D
    · rw [ha] at hnext
      dsimp only at hnext ⊢
      rw [strictN_eq]
      exact ih _ _ (hnext (fun hal => absurd ((aliveG_iff AL D).2 hal) (by rw [ha]; decide)))
    · rw [ha] at hnext
      dsimp only at hnext ⊢
      rw [strictN_eq]
      apply ih
      cases hs : slot D w (bitsG J (nat_lit 0) (nat_lit 21)) (bitsG J (nat_lit 21)
          (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (nat_lit 30)
            (Nat.beq (Nat.land (bitsG J (nat_lit 0) (nat_lit 21)) (nat_lit 1)) (nat_lit 1))))
      · exact Or.inl rfl
      · dsimp only
        exact hnext (fun _ => ⟨_, _, hs⟩)

theorem coverRun_inv {slot : ℕ → ℕ → ℕ → ℕ → Bool} {NO AL : ℕ} (hNO : NO < 2 ^ 20)
    (hNO0 : 0 < NO) : ∀ (Cs : List ℕ) (S : ℕ), CovInv slot NO AL S →
      CovInv slot NO AL (coverRun slot NO AL Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change CovInv slot NO AL (strictN (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih2 J S => covStep slot NO AL ih2 J S)
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S) (coverRun slot NO AL Cs))
    rw [strictN_eq]
    exact coverRun_inv hNO hNO0 Cs _ (covInner_inv hNO hNO0 _ _ _ h)

theorem coverRun_spec {slot : ℕ → ℕ → ℕ → ℕ → Bool} {NO AL ND : ℕ} {Cs : List ℕ}
    (hNO : NO < 2 ^ 20) (hNO0 : 0 < NO)
    (h : coverRun slot NO AL Cs 1 = Nat.add (nat_lit 1) (Nat.shiftLeft ND (nat_lit 20))) :
    ∀ D < ND, AL.testBit D = true → ∀ w < NO, SlotOK slot D w := by
  have h1 : CovInv slot NO AL 1 := Or.inr ⟨0, 0, rfl, hNO0, Or.inl rfl,
    fun D' hD' => absurd hD' (Nat.not_lt_zero _), fun w' hw' => absurd hw' (Nat.not_lt_zero _)⟩
  have hi := coverRun_inv hNO hNO0 Cs 1 h1
  rw [h] at hi
  have e : Nat.add (nat_lit 1) (Nat.shiftLeft ND (nat_lit 20)) = 1 + 2 ^ 20 * ND + 0 := by
    change 1 + ND <<< 20 = _
    rw [Nat.shiftLeft_eq]
    ring
  rw [e] at hi
  rcases hi with h0 | ⟨D, w, he, hw, -, hprev, -⟩
  · omega
  obtain ⟨d1, d2⟩ := covDec (D := ND) (w := 0) (by norm_num)
  obtain ⟨d3, d4⟩ := covDec (D := D) (Nat.lt_trans hw hNO)
  rw [he] at d1 d2
  rw [d1] at d3
  subst d3
  exact hprev

@[expose] noncomputable def sumAcc (AL MD NORD : ℕ) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 2)
    (fun D acc => (fun m => Bool.rec (motive := fun _ => ℕ) acc
        (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (Nat.add acc (Nat.div NORD m))
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false
              (Nat.beq (Nat.mod NORD m) (nat_lit 0)) (Nat.blt (nat_lit 0) m))
            (Nat.blt (nat_lit 0) acc)))
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) true false (Nat.beq D (nat_lit 0)))
          (aliveG AL D)))
      (bitsG MD (Nat.mul (nat_lit 20) D) (nat_lit 20))) k

@[expose] noncomputable def sumG (AL MD ND NORD SUM : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false
      ((fun r => Bool.rec (motive := fun _ => Bool) false (Nat.beq (Nat.sub r (nat_lit 1)) SUM)
          (Nat.blt (nat_lit 0) r))
        (sumAcc AL MD NORD ND))
      (Nat.blt AL (Nat.shiftLeft (nat_lit 1) ND)))
    (aliveG AL (nat_lit 0))

@[expose] noncomputable def mDG (MD D : ℕ) : ℕ := bitsG MD (Nat.mul (nat_lit 20) D) (nat_lit 20)

@[expose] noncomputable def aliveSet (AL k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun D => AL.testBit D = true ∧ D ≠ 0

theorem sumAcc_spec (AL MD NORD : ℕ) : ∀ k, sumAcc AL MD NORD k = 0 ∨
    ((∀ D < k, AL.testBit D = true → D ≠ 0 → 0 < mDG MD D ∧ mDG MD D ∣ NORD) ∧
      sumAcc AL MD NORD k = 2 + ∑ D ∈ aliveSet AL k, NORD / mDG MD D)
  | 0 => Or.inr ⟨fun D hD => absurd hD (Nat.not_lt_zero _), by simp [aliveSet, sumAcc]⟩
  | k + 1 => by
    have hs : aliveSet AL (k + 1) = if AL.testBit k = true ∧ k ≠ 0 then
        insert k (aliveSet AL k) else aliveSet AL k := by
      unfold aliveSet
      rw [Finset.range_add_one, Finset.filter_insert]
    have e : sumAcc AL MD NORD (k + 1) = Bool.rec (motive := fun _ => ℕ) (sumAcc AL MD NORD k)
        (Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
          (Nat.add (sumAcc AL MD NORD k) (Nat.div NORD (mDG MD k)))
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false
              (Nat.beq (Nat.mod NORD (mDG MD k)) (nat_lit 0)) (Nat.blt (nat_lit 0) (mDG MD k)))
            (Nat.blt (nat_lit 0) (sumAcc AL MD NORD k))))
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) true false (Nat.beq k (nat_lit 0)))
          (aliveG AL k)) := rfl
    rw [e]
    rcases sumAcc_spec AL MD NORD k with h0 | ⟨hd, he⟩
    · left
      rw [h0]
      cases (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) true false (Nat.beq k (nat_lit 0))) (aliveG AL k))
      · rfl
      · rfl
    · rw [he]
      have hval : Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) true false (Nat.beq k (nat_lit 0))) (aliveG AL k) =
            true ↔ AL.testBit k = true ∧ k ≠ 0 := by
        rw [band_iff, bnot_iff, aliveG_iff]
        refine and_congr_right fun _ => ⟨fun e2 e3 => ?_, fun e2 => ?_⟩
        · rw [e3] at e2
          exact absurd e2 (by decide)
        · cases e4 : Nat.beq k 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true e4) e2
      by_cases hc : AL.testBit k = true ∧ k ≠ 0
      · rw [hval.2 hc]
        dsimp only
        have hm2 : Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false
              (Nat.beq (Nat.mod NORD (mDG MD k)) (nat_lit 0)) (Nat.blt (nat_lit 0) (mDG MD k)))
            (Nat.blt (nat_lit 0) (2 + ∑ D ∈ aliveSet AL k, NORD / mDG MD D)) = true ↔
              0 < mDG MD k ∧ NORD % mDG MD k = 0 := by
          rw [band_iff, band_iff, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq]
          exact ⟨fun h => h.2, fun h => ⟨Nat.lt_of_lt_of_le Nat.zero_lt_two (Nat.le_add_right _ _), h⟩⟩
        by_cases hm : 0 < mDG MD k ∧ NORD % mDG MD k = 0
        · rw [hm2.2 hm]
          dsimp only
          right
          refine ⟨fun D hD hA hD0 => ?_, ?_⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hD with hD | rfl
            · exact hd D hD hA hD0
            · exact ⟨hm.1, Nat.dvd_of_mod_eq_zero hm.2⟩
          · rw [hs, ite_eq_left hc, Finset.sum_insert (by simp [aliveSet])]
            change 2 + _ + NORD / mDG MD k = _
            ring
        · have hf : Bool.rec (motive := fun _ => Bool) false
              (Bool.rec (motive := fun _ => Bool) false
                (Nat.beq (Nat.mod NORD (mDG MD k)) (nat_lit 0)) (Nat.blt (nat_lit 0) (mDG MD k)))
              (Nat.blt (nat_lit 0) (2 + ∑ D ∈ aliveSet AL k, NORD / mDG MD D)) = false :=
            Bool.eq_false_iff.2 fun e => hm (hm2.1 e)
          rw [hf]
          left
          rfl
      · have hf : Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) true false (Nat.beq k (nat_lit 0))) (aliveG AL k) =
              false := Bool.eq_false_iff.2 fun e => hc (hval.1 e)
        rw [hf]
        dsimp only
        right
        refine ⟨fun D hD hA hD0 => ?_, ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hD with hD | rfl
          · exact hd D hD hA hD0
          · exact absurd ⟨hA, hD0⟩ hc
        · rw [hs, ite_eq_right hc]

theorem sumG_spec {AL MD ND NORD SUM : ℕ} (h : sumG AL MD ND NORD SUM = true) :
    AL.testBit 0 = true ∧ AL < 2 ^ ND ∧
      (∀ D < ND, AL.testBit D = true → D ≠ 0 → 0 < mDG MD D ∧ mDG MD D ∣ NORD) ∧
      SUM = 1 + ∑ D ∈ aliveSet AL ND, NORD / mDG MD D := by
  unfold sumG at h
  rw [band_iff, band_iff, aliveG_iff, Nat.blt_eq] at h
  obtain ⟨h0, hA, hr⟩ := h
  refine ⟨h0, by change AL < 1 <<< ND at hA; rw [Nat.shiftLeft_eq, Nat.one_mul] at hA; exact hA, ?_⟩
  rcases sumAcc_spec AL MD NORD ND with hz | ⟨hd, he⟩
  · simp only [] at hr
    rw [hz] at hr
    exact absurd hr Bool.false_ne_true
  · simp only [] at hr
    rw [he, band_iff, Nat.beq_eq] at hr
    refine ⟨hd, ?_⟩
    have := hr.2
    change 2 + _ - 1 = SUM at this
    omega

@[expose] noncomputable def sIG (S : ℕ) : ℕ := Nat.land S (nat_lit 4294967295)
@[expose] noncomputable def sXG (S : ℕ) : ℕ := Nat.shiftRight S (nat_lit 32)
@[expose] noncomputable def mkSG (i nx : ℕ) : ℕ := Nat.lor i (Nat.shiftLeft nx (nat_lit 32))

@[expose] noncomputable def factG (rk : ℕ → Bool) (tk ak : ℕ → ℕ → Bool) (wk : ℕ → ℕ → ℕ → Bool)
    (fr : ℕ → ℕ) (Jf S : ℕ) : ℕ :=
  (fun i nx R k => Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
      (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ)
          (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (mkSG (Nat.succ i) nx)
            (Bool.rec (motive := fun _ => Bool) false (wk i Jf R) (Nat.beq k (nat_lit 2))))
          (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (mkSG (Nat.succ i) nx) (ak Jf R))
          (Nat.beq k (nat_lit 1)))
        (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (mkSG (Nat.succ i) (Nat.succ nx)) (tk nx R))
        (Nat.beq k (nat_lit 0)))
      (Bool.rec (motive := fun _ => Bool) false (rk R) (Nat.blt (nat_lit 0) S)))
    (sIG S) (sXG S) (fr (sIG S)) (Nat.land Jf (nat_lit 3))

@[expose] noncomputable def chunkG (fs : ℕ → ℕ → ℕ) (C S : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
    (fun _ ih J S => (fun L =>
      strictN (fs (bitsG J (nat_lit 12) L) S)
        (ih (Nat.shiftRight J (Nat.add (nat_lit 12) L))))
      (Nat.land J (nat_lit 4095)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def factsG (fs : ℕ → ℕ → ℕ) (Cs : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun C _ ih S => strictN (chunkG fs C S) ih) Cs

theorem mkSG_eq {i : ℕ} (nx : ℕ) (hi : i < 2 ^ 32) : mkSG i nx = i + nx * 2 ^ 32 := by
  unfold mkSG
  change i ||| nx <<< 32 = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hi, Nat.shiftLeft_eq]
  ring

private theorem sIG_eq (S : ℕ) : sIG S = S &&& 4294967295 := rfl
private theorem sXG_eq (S : ℕ) : sXG S = S >>> 32 := rfl

theorem mkSG_dec {i : ℕ} (nx : ℕ) (hi : i < 2 ^ 32) : sIG (mkSG i nx) = i ∧ sXG (mkSG i nx) = nx := by
  rw [mkSG_eq nx hi]
  refine ⟨?_, ?_⟩
  · rw [sIG_eq, show (4294967295 : ℕ) = 2 ^ 32 - 1 from rfl, land_low, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hi]
  · rw [sXG_eq, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hi, Nat.zero_add]

theorem mkSG_wrap (nx : ℕ) : mkSG (2 ^ 32) nx = mkSG 0 (Nat.lor 1 nx) := by
  unfold mkSG
  change 2 ^ 32 ||| nx <<< 32 = 0 ||| (1 ||| nx) <<< 32
  rw [Nat.zero_or, Nat.shiftLeft_or_distrib, Nat.one_shiftLeft]

@[expose] def FactOK (rk : ℕ → Bool) (tk ak : ℕ → ℕ → Bool) (wk : ℕ → ℕ → ℕ → Bool)
    (fr : ℕ → ℕ) (i nx nx' : ℕ) : Prop :=
  rk (fr i) = true ∧ (nx' = nx + 1 ∧ tk nx (fr i) = true ∨ nx' = nx ∧ (∃ Jf, ak Jf (fr i) = true) ∨
    nx' = nx ∧ ∃ Jf, wk i Jf (fr i) = true)

@[expose] def FInvG (rk : ℕ → Bool) (tk ak : ℕ → ℕ → Bool) (wk : ℕ → ℕ → ℕ → Bool) (fr : ℕ → ℕ)
    (S : ℕ) : Prop :=
  S = 0 ∨ ∃ i nx, S = mkSG i nx ∧ i < 2 ^ 32 ∧ ∃ nxf : ℕ → ℕ, nxf i = nx ∧
    ∀ i' < i, FactOK rk tk ak wk fr i' (nxf i') (nxf (i' + 1))

variable {rk : ℕ → Bool} {tk ak : ℕ → ℕ → Bool} {wk : ℕ → ℕ → ℕ → Bool} {fr : ℕ → ℕ}

theorem factG_inv {Jf S : ℕ} (h : FInvG rk tk ak wk fr S) :
    FInvG rk tk ak wk fr (factG rk tk ak wk fr Jf S) := by
  rcases h with rfl | ⟨i, nx, rfl, hi, nxf, hnx, hf⟩
  · exact Or.inl rfl
  obtain ⟨eI, eN⟩ := mkSG_dec nx hi
  have key : factG rk tk ak wk fr Jf (mkSG i nx) = 0 ∨ ∃ nx',
      factG rk tk ak wk fr Jf (mkSG i nx) = mkSG (i + 1) nx' ∧ FactOK rk tk ak wk fr i nx nx' := by
    unfold factG
    simp only []
    rw [eI, eN]
    cases h1 : Bool.rec (motive := fun _ => Bool) false (rk (fr i)) (Nat.blt (nat_lit 0) (mkSG i nx))
    · exact Or.inl rfl
    rw [band_iff] at h1
    dsimp only
    cases h2 : Nat.beq (Nat.land Jf (nat_lit 3)) (nat_lit 0)
    · dsimp only
      cases h3 : Nat.beq (Nat.land Jf (nat_lit 3)) (nat_lit 1)
      · dsimp only
        cases h4 : Bool.rec (motive := fun _ => Bool) false (wk i Jf (fr i))
            (Nat.beq (Nat.land Jf (nat_lit 3)) (nat_lit 2))
        · exact Or.inl rfl
        · rw [band_iff] at h4
          exact Or.inr ⟨_, rfl, h1.2, Or.inr (Or.inr ⟨rfl, Jf, h4.2⟩)⟩
      · dsimp only
        cases h4 : ak Jf (fr i)
        · exact Or.inl rfl
        · exact Or.inr ⟨_, rfl, h1.2, Or.inr (Or.inl ⟨rfl, Jf, h4⟩)⟩
    · dsimp only
      cases h4 : tk nx (fr i)
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl, h1.2, Or.inl ⟨rfl, h4⟩⟩
  rcases key with hz | ⟨nx', e, hfr⟩
  · exact Or.inl hz
  rw [e]
  rcases Nat.lt_or_ge (i + 1) (2 ^ 32) with hlt | hge
  · refine Or.inr ⟨i + 1, nx', rfl, hlt, fun i' => if i' ≤ i then nxf i' else nx', by simp, ?_⟩
    intro i' hi'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
    · have h1 : i' ≤ i := by omega
      have h2 : i' + 1 ≤ i := by omega
      simp only [h1, h2, ↓reduceIte]
      exact hf i' hi'
    · simp only [le_refl, ↓reduceIte, Nat.not_succ_le_self]
      rw [hnx]
      exact hfr
  · have e2 : i + 1 = 2 ^ 32 := by omega
    rw [e2, mkSG_wrap]
    exact Or.inr ⟨0, _, rfl, by norm_num, fun _ => Nat.lor 1 nx', rfl,
      fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩

theorem chunkG_inv : ∀ (n J S : ℕ), FInvG rk tk ak wk fr S →
    FInvG rk tk ak wk fr (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
      (fun _ ih J S => (fun L =>
        strictN (factG rk tk ak wk fr (bitsG J (nat_lit 12) L) S)
          (ih (Nat.shiftRight J (Nat.add (nat_lit 12) L))))
        (Nat.land J (nat_lit 4095))) n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change FInvG rk tk ak wk fr (strictN (factG rk tk ak wk fr (bitsG J (nat_lit 12)
      (Nat.land J (nat_lit 4095))) S) (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
      (fun _ ih J S => (fun L =>
        strictN (factG rk tk ak wk fr (bitsG J (nat_lit 12) L) S)
          (ih (Nat.shiftRight J (Nat.add (nat_lit 12) L))))
        (Nat.land J (nat_lit 4095))) n (Nat.shiftRight J (Nat.add (nat_lit 12)
          (Nat.land J (nat_lit 4095))))))
    rw [strictN_eq]
    exact chunkG_inv n _ _ (factG_inv h)

theorem factsG_inv : ∀ (Cs : List ℕ) (S : ℕ), FInvG rk tk ak wk fr S →
    FInvG rk tk ak wk fr (factsG (factG rk tk ak wk fr) Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change FInvG rk tk ak wk fr (strictN (chunkG (factG rk tk ak wk fr) C S)
      (factsG (factG rk tk ak wk fr) Cs))
    rw [strictN_eq]
    exact factsG_inv Cs _ (chunkG_inv _ _ _ h)

theorem factsG_spec {Cs : List ℕ} {S1 NF : ℕ}
    (hrun : factsG (factG rk tk ak wk fr) Cs (mkSG 0 1) = S1) (hS1 : 0 < S1) (hNF : sIG S1 = NF) :
    ∃ nxf : ℕ → ℕ, ∀ i < NF, FactOK rk tk ak wk fr i (nxf i) (nxf (i + 1)) := by
  have h0 : FInvG rk tk ak wk fr (mkSG 0 1) :=
    Or.inr ⟨0, 1, rfl, by norm_num, fun _ => 1, rfl, fun i' hi' => absurd hi' (by omega)⟩
  have h1 := factsG_inv Cs _ h0
  rw [hrun] at h1
  rcases h1 with h1 | ⟨i, nx, e, hi, nxf, -, hf⟩
  · omega
  obtain ⟨d1, -⟩ := mkSG_dec nx hi
  rw [← e, hNF] at d1
  subst d1
  exact ⟨nxf, hf⟩

theorem tree_unique {nxf : ℕ → ℕ} {NF : ℕ} (hf : ∀ i < NF, FactOK rk tk ak wk fr i (nxf i) (nxf (i + 1)))
    (rD : ℕ → ℕ) (htD : ∀ nx R, tk nx R = true → rD R = nx)
    {i i' : ℕ} (hi : i < NF) (hi' : i' < NF) (ht : nxf (i + 1) = nxf i + 1)
    (ht' : nxf (i' + 1) = nxf i' + 1) (e : rD (fr i) = rD (fr i')) : i = i' := by
  have mono1 : ∀ k < NF, nxf k ≤ nxf (k + 1) := fun k hk => by
    rcases (hf k hk).2 with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> omega
  have mono : ∀ a b, a ≤ b → b ≤ NF → nxf a ≤ nxf b := by
    intro a b hab hb
    induction b with
    | zero => rw [Nat.le_zero.1 hab]
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hab) with h1 | h1
      · exact Nat.le_trans (ih (by omega) (by omega)) (mono1 k (by omega))
      · rw [h1]
  have tr : ∀ k < NF, nxf (k + 1) = nxf k + 1 → rD (fr k) = nxf k := fun k hk hk1 => by
    rcases (hf k hk).2 with ⟨-, h⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact htD _ _ h
    · omega
    · omega
  rw [tr i hi ht, tr i' hi' ht'] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · have := mono (i + 1) i' (by omega) (by omega)
    omega
  · have := mono (i' + 1) i (by omega) (by omega)
    omega

@[expose] noncomputable def walkStep (isN isUL : ℕ → Bool) (nst : ℕ → ℕ → ℕ)
    (stp : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (fr : ℕ → ℕ) (bad : ℕ) (i Ri ft fd Wd n k : ℕ)
    (ih : ℕ → ℕ → ℕ) (J S : ℕ) : ℕ :=
  (fun q => (fun c =>
      Bool.rec (motive := fun _ => ℕ)
        (ih J (nst S c))
        ((fun own => (fun h => (fun R dir =>
            Bool.rec (motive := fun _ => ℕ) bad
              (strictN (stp c R dir
                  (Bool.rec (motive := fun _ => ℕ) (bitsG J (nat_lit 21) (nat_lit 19))
                    (bitsG J (nat_lit 0) (nat_lit 19)) own) S)
                (fun S2 => ih (Nat.shiftRight J (Nat.add
                  (Bool.rec (motive := fun _ => ℕ) (nat_lit 21) (nat_lit 0) own)
                  (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (nat_lit 19) (isUL c)))) S2))
              (Bool.rec (motive := fun _ => Bool) (Nat.blt h i) true own))
            (Bool.rec (motive := fun _ => ℕ) (fr h) Ri own)
            (Bool.rec (motive := fun _ => ℕ) (Nat.land J (nat_lit 1)) fd own))
          (bitsG J (nat_lit 1) (nat_lit 20)))
         (Nat.beq q ft))
        (Bool.rec (motive := fun _ => Bool) true false (isN c)))
      (byteG Wd q)) (Nat.sub n (Nat.succ k))

@[expose] noncomputable def walkG (isN isUL : ℕ → Bool) (nst : ℕ → ℕ → ℕ)
    (stp : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (fr : ℕ → ℕ) (bad : ℕ) (i Ri ft fd Wd n : ℕ) (k : ℕ) :
    ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
    (fun k ih J S => walkStep isN isUL nst stp fr bad i Ri ft fd Wd n k ih J S) k

@[expose] def WStep (isN : ℕ → Bool) (nst : ℕ → ℕ → ℕ) (stp : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fr : ℕ → ℕ) (i Ri ft fd Wd q S S' : ℕ) : Prop :=
  (isN (byteG Wd q) = true ∧ S' = nst S (byteG Wd q)) ∨
    (isN (byteG Wd q) = false ∧ ∃ R dir e, S' = stp (byteG Wd q) R dir e S ∧
      (q = ft ∧ R = Ri ∧ dir = fd ∨ q ≠ ft ∧ ∃ h < i, R = fr h ∧ dir < 2))

theorem land1_lt (J : ℕ) : Nat.land J (nat_lit 1) < 2 := by
  change J &&& 1 < 2
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem walkG_spec (isN isUL : ℕ → Bool) (nst : ℕ → ℕ → ℕ) (stp : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (fr : ℕ → ℕ) (bad i Ri ft fd Wd n : ℕ) : ∀ k, k ≤ n → ∀ J S,
    walkG isN isUL nst stp fr bad i Ri ft fd Wd n k J S = bad ∨
      ∃ Ss : ℕ → ℕ, Ss (n - k) = S ∧ Ss n = walkG isN isUL nst stp fr bad i Ri ft fd Wd n k J S ∧
        ∀ q, n - k ≤ q → q < n → WStep isN nst stp fr i Ri ft fd Wd q (Ss q) (Ss (q + 1))
  | 0, _, J, S => Or.inr ⟨fun _ => S, rfl, rfl,
      fun q h1 h2 => absurd h2 (by omega)⟩
  | k + 1, hk, J, S => by
    have ih := walkG_spec isN isUL nst stp fr bad i Ri ft fd Wd n k (by omega)
    have ext : ∀ S', WStep isN nst stp fr i Ri ft fd Wd (n - (k + 1)) S S' → ∀ J',
        (walkG isN isUL nst stp fr bad i Ri ft fd Wd n k J' S' = bad ∨
          ∃ Ss : ℕ → ℕ, Ss (n - k) = S' ∧
            Ss n = walkG isN isUL nst stp fr bad i Ri ft fd Wd n k J' S' ∧
            ∀ q, n - k ≤ q → q < n → WStep isN nst stp fr i Ri ft fd Wd q (Ss q) (Ss (q + 1))) →
        walkG isN isUL nst stp fr bad i Ri ft fd Wd n k J' S' = bad ∨
          ∃ Ss : ℕ → ℕ, Ss (n - (k + 1)) = S ∧
            Ss n = walkG isN isUL nst stp fr bad i Ri ft fd Wd n k J' S' ∧
            ∀ q, n - (k + 1) ≤ q → q < n →
              WStep isN nst stp fr i Ri ft fd Wd q (Ss q) (Ss (q + 1)) := by
      intro S' hst J' h
      rcases h with h | ⟨Ss, h0, hn, hs⟩
      · exact Or.inl h
      refine Or.inr ⟨fun q => if q = n - (k + 1) then S else Ss q, by simp, ?_, ?_⟩
      · simp only []
        rw [ite_eq_right (by omega)]
        exact hn
      · intro q hq1 hq2
        simp only []
        rcases Nat.eq_or_lt_of_le hq1 with rfl | hq1
        · rw [ite_eq_left rfl, ite_eq_right (by omega), show n - (k + 1) + 1 = n - k by omega, h0]
          exact hst
        · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
          exact hs q (by omega) hq2
    change walkStep isN isUL nst stp fr bad i Ri ft fd Wd n k
      (walkG isN isUL nst stp fr bad i Ri ft fd Wd n k) J S = bad ∨ ∃ Ss : ℕ → ℕ,
        Ss (n - (k + 1)) = S ∧ Ss n = walkStep isN isUL nst stp fr bad i Ri ft fd Wd n k
          (walkG isN isUL nst stp fr bad i Ri ft fd Wd n k) J S ∧
        ∀ q, n - (k + 1) ≤ q → q < n → WStep isN nst stp fr i Ri ft fd Wd q (Ss q) (Ss (q + 1))
    unfold walkStep
    simp only []
    have eq : Nat.sub n (Nat.succ k) = n - (k + 1) := rfl
    rw [eq]
    cases hN : isN (byteG Wd (n - (k + 1)))
    ·
      dsimp only
      cases hc : Bool.rec (motive := fun _ => Bool) (Nat.blt (bitsG J (nat_lit 1) (nat_lit 20)) i)
          true (Nat.beq (n - (k + 1)) ft)
      · exact Or.inl rfl
      · dsimp only
        rw [strictN_eq]
        apply ext _ _ _ (ih _ _)
        refine Or.inr ⟨hN, _, _, _, rfl, ?_⟩
        cases ho : Nat.beq (n - (k + 1)) ft
        · rw [ho] at hc
          dsimp only at hc
          rw [Nat.blt_eq] at hc
          exact Or.inr ⟨Nat.ne_of_beq_eq_false ho, _, hc, rfl, land1_lt J⟩
        · exact Or.inl ⟨Nat.eq_of_beq_eq_true ho, rfl, rfl⟩
    ·
      dsimp only
      exact ext _ (Or.inl ⟨hN, rfl⟩) _ (ih _ _)

end CFSG.Certificates.DceLoop

end
