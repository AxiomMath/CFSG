module

public import Certificates.Data.Kernel.HMathieu.Pred24F
public import CFSG.Certificates.Kernel.HMathieu.PredQKSound

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.Quasithin.H.Mathieu

theorem bAnd_tt {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem bIf_tt {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem testBit_lor_shl (acc x z : Nat) :
    (Nat.lor acc (Nat.shiftLeft 1 x)).testBit z = (acc.testBit z || decide (x = z)) := by
  rw [shlQ]
  change (acc ||| 2 ^ x).testBit z = _
  rw [Nat.testBit_or, Nat.testBit_two_pow]

theorem nodupMK_spec : ∀ (l : List Nat) (acc : Nat), nodupMK l acc = true →
    l.Nodup ∧ ∀ x ∈ l, acc.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, acc, h => by
    change Bool.rec (motive := fun _ => Bool)
      (strictB (Nat.lor acc (Nat.shiftLeft 1 x)) (nodupMK l)) false
      (Nat.beq (Nat.land (Nat.shiftRight acc x) 1) 1) = true at h
    rcases bIf_tt h with ⟨-, h'⟩ | ⟨hb, h'⟩
    · exact absurd h' Bool.false_ne_true
    · rw [strictB_eqQ] at h'
      obtain ⟨hnd, hl⟩ := nodupMK_spec l _ h'
      have e1 : Nat.land (Nat.shiftRight acc x) 1 = acc / 2 ^ x % 2 := by
        rw [← Nat.shiftRight_eq_div_pow]
        exact Nat.and_one_is_mod _
      have hx : acc.testBit x = false := by
        rw [beqQ, e1, decide_eq_false_iff_not] at hb
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
        exact hb
      refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩, fun z hz => ?_⟩
      · have := hl x hm
        rw [testBit_lor_shl] at this
        simp at this
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact hx
        · have := hl z hz
          rw [testBit_lor_shl, Bool.or_eq_false_iff] at this
          exact this.1

theorem fixMasks_one (M : List Nat) :
    fixMasks 11 actM [M] = (List.range 2048).filter fun m => actM M m == m := by
  unfold fixMasks
  simp

theorem xiCandsF_eq (Mc : List (List Nat)) (S : List Nat) :
    xiCandsF Mc S = xiCandsK Mc 191 S := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    change Bool.rec (motive := fun _ => List Nat)
      (List.append (fixLstQ (Mc.getD s []) (List.range 2048)) (xiCandsF Mc S)) (xiCandsF Mc S)
      (Nat.beq s 191) = _
    rw [ih, beqQ]
    unfold xiCandsK
    rw [List.filter_cons]
    by_cases h : s = 191
    · rw [decide_eq_true h, if_neg (by simp [h])]
    · rw [decide_eq_false h, if_pos (by simpa using h), List.flatMap_cons, fixMasks_one,
        ← fixLstQ_eq]
      rfl

theorem foldl_sub {vs : List Nat} (f : List Nat × List Nat → Nat → List Nat × List Nat)
    (hf : ∀ st v, (f st v).2 = st.2 ∨ (f st v).2 = v :: st.2) :
    ∀ (l : List Nat) (st : List Nat × List Nat), (∀ x ∈ st.2, x ∈ vs) → (∀ x ∈ l, x ∈ vs) →
      ∀ x ∈ (l.foldl f st).2, x ∈ vs
  | [], _, h1, _ => h1
  | v :: l, st, h1, h2 => by
    rw [List.foldl_cons]
    refine foldl_sub f hf l (f st v) (fun x hx => ?_) fun x hx => h2 x (List.mem_cons_of_mem v hx)
    rcases hf st v with h | h
    · rw [h] at hx
      exact h1 x hx
    · rw [h] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h2 x List.mem_cons_self
      · exact h1 x hx

theorem pickBasis_sub (vs : List Nat) : ∀ x ∈ pickBasis vs, x ∈ vs := by
  unfold pickBasis
  refine foldl_sub _ (fun st v => ?_) vs ([], []) (fun x hx => absurd hx List.not_mem_nil)
    fun x hx => hx
  dsimp only
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem xiF_imp (Mc : List (List Nat)) (S : List Nat) (h : xiF Mc S = true) :
    indepCheck 11 (xiCandsK Mc 191 S) (pickBasis (xiCandsK Mc 191 S)) = true := by
  simp only [xiF, xiCandsF_eq] at h
  obtain ⟨h1, h2⟩ := bAnd_tt h
  rw [lenK_eq, bleQ, decide_eq_true_iff] at h1
  obtain ⟨hnd, -⟩ := nodupMK_spec _ _ h2
  unfold indepCheck
  rw [decide_eq_true h1, decide_eq_true hnd, Bool.true_and, Bool.and_true, List.all_eq_true]
  exact fun x hx => decide_eq_true (pickBasis_sub _ x hx)

theorem log_lt_of_lt {c j : Nat} (hj : 0 < j) (h : c < 2 ^ j) : Nat.log 2 c < j := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.log_zero_right]
    exact hj
  · exact (Nat.log_lt_iff_lt_pow (by norm_num) hc.ne').2 h

theorem log_eq_three {c : Nat} (h1 : 8 ≤ c) (h2 : c < 16) : Nat.log 2 c = 3 := by
  have a := log_lt_of_lt (j := 4) (by norm_num) (lt_of_lt_of_eq h2 (by norm_num))
  have b : 3 ≤ Nat.log 2 c := by
    by_contra hb
    have := (Nat.log_lt_iff_lt_pow (b := 2) (by norm_num) (by omega : c ≠ 0)).1
      (by omega : Nat.log 2 c < 3)
    norm_num at this
    omega
  omega

theorem pred24F_imp (Mc : List (List Nat)) (L S : List Nat) (st : List (List Nat) × List Nat)
    (h : pred24F Mc L S st = true) : pred24K Mc L S st = true := by
  simp only [pred24F, strictB_eqQ, lenK_eq] at h
  have es : Nat.sub 10 L.length = 10 - L.length := rfl
  obtain ⟨h6, h⟩ := bAnd_tt h
  obtain ⟨hA, h⟩ := bAnd_tt h
  obtain ⟨hB, hC⟩ := bAnd_tt h
  rw [bleQ, decide_eq_true_iff] at h6
  unfold pred24K
  dsimp only
  refine Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
    ⟨decide_eq_true h6, ?_⟩, ?_⟩, ?_⟩
  · rcases bIf_tt hA with ⟨hk, -⟩ | ⟨-, hA⟩
    · rw [beqQ, decide_eq_true_iff] at hk
      simp [hk]
    · rcases bIf_tt hA with ⟨hc, -⟩ | ⟨-, hav⟩
      · rw [bltQ, shlQ, es, decide_eq_true_iff] at hc
        have := log_lt_of_lt (by omega) hc
        rw [Bool.or_eq_true, Bool.or_eq_true]
        exact Or.inl (Or.inr (by simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega))
      · rw [Bool.or_eq_true]
        exact Or.inr hav
  · rcases bIf_tt hB with ⟨-, hc⟩ | ⟨hk, -⟩
    · rw [bltQ, decide_eq_true_iff] at hc
      have := log_lt_of_lt (j := 8) (by norm_num) (lt_of_lt_of_eq hc (by norm_num))
      rw [Bool.or_eq_true]
      exact Or.inr (decide_eq_true (by omega))
    · rw [beqQ, decide_eq_false_iff_not] at hk
      rw [Bool.or_eq_true]
      exact Or.inl (by simpa using hk)
  · rcases bIf_tt hC with ⟨-, hC⟩ | ⟨hk, -⟩
    · rcases bIf_tt hC with ⟨h3, -⟩ | ⟨-, hxi⟩
      · obtain ⟨h8, h16⟩ := bAnd_tt h3
        rw [bleQ, decide_eq_true_iff] at h8
        rw [bltQ, decide_eq_true_iff] at h16
        rw [Bool.or_eq_true]
        exact Or.inr (by rw [log_eq_three h8 h16]; rfl)
      · rw [Bool.or_eq_true, Bool.or_eq_true]
        exact Or.inl (Or.inr (xiF_imp Mc S hxi))
    · rw [beqQ, decide_eq_false_iff_not] at hk
      rw [Bool.or_eq_true, Bool.or_eq_true]
      exact Or.inl (Or.inl (by simpa using hk))

theorem pred24FK_eq (Mc : List (List Nat)) (L S : List Nat) (st : List (List Nat) × List Nat) :
    pred24FK Mc L S st = pred24K Mc L S st := by
  unfold pred24FK
  cases h : pred24F Mc L S st
  · rfl
  · exact (pred24F_imp Mc L S st h).symm

end CFSG.KC.HMathieu

end
