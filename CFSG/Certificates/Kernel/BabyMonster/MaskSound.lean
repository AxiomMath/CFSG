module

public import CFSG.Certificates.Kernel.BabyMonster.VStripSound

public section

namespace CFSG.KC.BM

open scoped Matrix
open CFSG.KC.BM.SL

theorem testBit_SM_mul {m : Nat} (hm : m < 2 ^ 64) (j t : Nat) (ht : t < 64) :
    (SM * m).testBit (64 * j + t) = (m.testBit t && decide (j < 4370)) := by
  rw [Nat.mul_comm SM m, testBit_mul_sparse hm j SM (by rw [SM_eq]; exact SMn_sparse 4370) t ht,
    SM_eq, testBit_SMn_mul]

theorem testBit_maskP {m : Nat} (hm : m < 2 ^ 64) (P j t : Nat) (ht : t < 64) (hj : j < 4370) :
    (Nat.land P (Nat.mul SM m)).testBit (64 * j + t) = (m.testBit t && P.testBit (64 * j + t)) := by
  rw [nland, nmul, Nat.testBit_and, testBit_SM_mul hm j t ht, decide_eq_true hj, Bool.and_true,
    Bool.and_comm]

theorem mask_row {m : Nat} (hm : m < 2 ^ 64) {B : List Nat} (hB : wfMat B = true) (P : Nat)
    {t : Nat} (ht : t < 64) :
    vrow (rowOf (mulS B (Nat.land P (Nat.mul SM m))) t) =
      if m.testBit t then vrow (rowOf P t) ᵥ* stripMat B else 0 := by
  rw [mulS_rows hB _ ht]
  have e : vrow (rowOf (Nat.land P (Nat.mul SM m)) t) =
      if m.testBit t then vrow (rowOf P t) else 0 := by
    funext j
    rw [vrow_rowOf, testBit_maskP hm P j.val t ht j.isLt]
    cases m.testBit t
    · simp
    · simp [vrow_rowOf]
  rw [e]
  by_cases hc : m.testBit t = true <;> simp [hc]

theorem maskUpd_rows {B : List Nat} (hB : wfMat B = true) (P m : Nat) (hm : m < 2 ^ 64) {t : Nat}
    (ht : t < 64) :
    vrow (rowOf (Nat.lor (Nat.sub P (Nat.land P (Nat.mul SM m)))
      (mulS B (Nat.land P (Nat.mul SM m)))) t) =
      if m.testBit t then vrow (rowOf P t) ᵥ* stripMat B else vrow (rowOf P t) := by
  have hR := mask_row hm hB P ht
  funext j
  have hR' := congrFun hR j
  have e : Nat.sub P (Nat.land P (Nat.mul SM m)) = P ^^^ Nat.land P (Nat.mul SM m) :=
    sub_land_eq P _
  rw [vrow_rowOf] at hR' ⊢
  rw [nlor, e, Nat.testBit_or, Nat.testBit_xor, testBit_maskP hm P j.val t ht j.isLt]
  by_cases hmt : m.testBit t = true
  · rw [ite_eq_left hmt] at hR' ⊢
    rw [hmt, Bool.true_and, Bool.xor_self, Bool.false_or]
    exact hR'
  · rw [ite_eq_right hmt] at hR' ⊢
    rw [Bool.not_eq_true] at hmt
    rw [hmt, Bool.false_and, Bool.xor_false]
    have h0 : (mulS B (Nat.land P (Nat.mul SM m))).testBit (64 * j.val + t) = false := by
      cases hc : (mulS B (Nat.land P (Nat.mul SM m))).testBit (64 * j.val + t)
      · rfl
      · rw [hc, Pi.zero_apply, bz_true] at hR'
        exact absurd hR' (by decide)
    rw [h0, Bool.or_false, vrow_rowOf]

@[expose] noncomputable def stepTerm (P U : Nat) (ms : List (List Nat × Nat)) : Nat :=
  ms.foldl (fun acc mv => Nat.lor acc (mulS mv.1 (Nat.land P (Nat.mul SM mv.2))))
    (Nat.sub P (Nat.land P (Nat.mul SM U)))

theorem foldl_lor_testBit {α : Type*} (f : α → Nat) (q : Nat) : ∀ (l : List α) (acc : Nat),
    (l.foldl (fun acc x => Nat.lor acc (f x)) acc).testBit q =
      (acc.testBit q || l.any fun x => (f x).testBit q)
  | [], acc => by simp
  | x :: l, acc => by
    rw [List.foldl_cons, foldl_lor_testBit f q l]
    simp only [nlor, Nat.testBit_or, List.any_cons, Bool.or_assoc]

theorem stepTerm_aux (P t : Nat) (ht : t < 64) (j : Fin 4370) : ∀ (ms : List (List Nat × Nat)),
    (∀ mv ∈ ms, wfMat mv.1 = true) → (∀ mv ∈ ms, mv.2 < 2 ^ 64) →
    ms.Pairwise (fun a b => Nat.land a.2 b.2 = 0) →
    bz ((P.testBit (64 * j.val + t) && !(ms.any fun mv => mv.2.testBit t)) ||
      ms.any fun mv => (mulS mv.1 (Nat.land P (Nat.mul SM mv.2))).testBit (64 * j.val + t)) =
    ms.foldr (fun mv acc => if mv.2.testBit t then vrow (rowOf P t) ᵥ* stripMat mv.1 else acc)
      (vrow (rowOf P t)) j
  | [], _, _, _ => by simp [vrow_rowOf]
  | mv :: rest, hwf, hlt, hd => by
    rw [List.pairwise_cons] at hd
    have hx := congrFun (mask_row (hlt mv List.mem_cons_self) (hwf mv List.mem_cons_self) P ht) j
    rw [vrow_rowOf] at hx
    simp only [List.any_cons, List.foldr_cons]
    by_cases hm : mv.2.testBit t = true
    · have hr : ∀ mv' ∈ rest, mv'.2.testBit t = false := by
        intro mv' h'
        have := congrArg (fun x => Nat.testBit x t) (hd.1 mv' h')
        simp only [nland, Nat.testBit_and, hm, Bool.true_and, Nat.zero_testBit] at this
        exact this
      have hr2 : (rest.any fun mv => (mulS mv.1 (Nat.land P (Nat.mul SM mv.2))).testBit
          (64 * j.val + t)) = false := by
        rw [List.any_eq_false]
        intro mv' h' hc
        have hc' : (mulS mv'.1 (Nat.land P (Nat.mul SM mv'.2))).testBit (64 * j.val + t) = true :=
          hc
        have hx' := congrFun (mask_row (hlt mv' (List.mem_cons_of_mem _ h'))
          (hwf mv' (List.mem_cons_of_mem _ h')) P ht) j
        have hn : ¬ mv'.2.testBit t = true := by
          rw [hr mv' h']
          decide
        rw [vrow_rowOf, ite_eq_right hn, hc', Pi.zero_apply, bz_true] at hx'
        exact absurd hx' (by decide)
      rw [ite_eq_left hm] at hx ⊢
      simp only [hm, hr2, Bool.true_or, Bool.not_true, Bool.and_false, Bool.false_or, Bool.or_false]
      exact hx
    · rw [ite_eq_right hm] at hx ⊢
      rw [Bool.not_eq_true] at hm
      have hx0 : (mulS mv.1 (Nat.land P (Nat.mul SM mv.2))).testBit (64 * j.val + t) = false := by
        cases hc : (mulS mv.1 (Nat.land P (Nat.mul SM mv.2))).testBit (64 * j.val + t)
        · rfl
        · rw [hc, Pi.zero_apply, bz_true] at hx
          exact absurd hx (by decide)
      simp only [hm, hx0, Bool.false_or]
      exact stepTerm_aux P t ht j rest (fun x h => hwf x (List.mem_cons_of_mem _ h))
        (fun x h => hlt x (List.mem_cons_of_mem _ h)) hd.2

theorem stepTerm_rows (ms : List (List Nat × Nat)) (hwf : ∀ mv ∈ ms, wfMat mv.1 = true)
    (hlt : ∀ mv ∈ ms, mv.2 < 2 ^ 64) (hd : ms.Pairwise fun a b => Nat.land a.2 b.2 = 0)
    (P U : Nat) (hU : U = (ms.map (·.2)).foldl Nat.lor 0) {t : Nat} (ht : t < 64) :
    vrow (rowOf (stepTerm P U ms) t) = ms.foldr (fun mv acc =>
      if mv.2.testBit t then vrow (rowOf P t) ᵥ* stripMat mv.1 else acc) (vrow (rowOf P t)) := by
  have hUt : ∀ i, U.testBit i = ms.any (fun mv => mv.2.testBit i) := by
    intro i
    rw [hU, List.foldl_map]
    have := foldl_lor_testBit (fun mv : List Nat × Nat => mv.2) i ms 0
    rw [Nat.zero_testBit, Bool.false_or] at this
    exact this
  have hU64 : U < 2 ^ 64 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [hUt, List.any_eq_false]
    intro mv hmv
    have hb : mv.2.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hlt mv hmv) (Nat.pow_le_pow_right (by norm_num) hi))
    simp [hb]
  funext j
  rw [vrow_rowOf]
  unfold stepTerm
  rw [foldl_lor_testBit (fun mv : List Nat × Nat => mulS mv.1 (Nat.land P (Nat.mul SM mv.2)))]
  have e0' : (Nat.sub P (Nat.land P (Nat.mul SM U))).testBit (64 * j.val + t) =
      (P.testBit (64 * j.val + t) && !(ms.any fun mv => mv.2.testBit t)) := by
    have e : Nat.sub P (Nat.land P (Nat.mul SM U)) = P ^^^ Nat.land P (Nat.mul SM U) :=
      sub_land_eq P _
    rw [e, Nat.testBit_xor, testBit_maskP hU64 P j.val t ht j.isLt, ← hUt t]
    cases P.testBit (64 * j.val + t) <;> cases U.testBit t <;> rfl
  rw [e0']
  exact stepTerm_aux P t ht j ms hwf hlt hd

set_option exponentiation.threshold 8192 in
theorem start_rows {m₀ m₁ v : Nat} (h : Nat.land m₀ m₁ = 0) (h₀ : m₀ < 2 ^ 64) (h₁ : m₁ < 2 ^ 64)
    (hv : v < 2 ^ 4370) {t : Nat} (ht : t < 64) :
    vrow (rowOf (Nat.lor m₀ (Nat.mul (spreadRow v) m₁)) t) =
      if m₁.testBit t then vecN v else if m₀.testBit t then e0 else 0 := by
  have hv' : v < 2 ^ 4410 := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hsp : ∀ p, (spreadRow v).testBit p = true → p % 64 = 0 := by
    intro p hp
    rw [testBit_spreadRow hv' p] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.1
  have hz : ∀ j : Nat, m₀.testBit (64 * j + t) = (decide (j = 0) && m₀.testBit t) := by
    intro j
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h₀ (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      simp [Nat.pos_iff_ne_zero.mp hj]
  have hdis : m₁.testBit t = true → m₀.testBit t = false := by
    intro h1
    have := congrArg (fun x => Nat.testBit x t) h
    simp only [nland, Nat.testBit_and, h1, Bool.and_true, Nat.zero_testBit] at this
    exact this
  funext j
  rw [vrow_rowOf, nlor, nmul, Nat.testBit_or, hz, Nat.mul_comm (spreadRow v) m₁,
    testBit_mul_sparse h₁ j.val _ hsp t ht, testBit_spreadRow hv', Nat.mul_mod_right,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 64)]
  cases h1 : m₁.testBit t
  · cases h0 : m₀.testBit t
    · simp
    · by_cases hj : j = 0
      · subst hj
        simp [e0]
      · have hj' : j.val ≠ 0 := fun e => hj (Fin.ext e)
        simp [e0, hj, hj']
  · rw [hdis h1]
    simp [vecN, bz]

end CFSG.KC.BM

end
