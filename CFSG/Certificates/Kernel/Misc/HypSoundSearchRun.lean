module

public import CFSG.Certificates.Kernel.Misc.HypSoundSearchStep

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

variable {C : HCtx} {PB LB LI GI : Nat → Nat} {PL NL : Nat → List Nat}

private def combOpt : Option (List Flags) → Option (List Flags) → Option (List Flags)
  | some a, some b => some (a ++ b)
  | _, _ => none

private theorem combOpt_assoc (A B C : Option (List Flags)) :
    combOpt (combOpt A B) C = combOpt A (combOpt B C) := by
  cases A <;> cases B <;> cases C <;> simp [combOpt, List.append_assoc]

private theorem combK_eq (a b : Nat) :
    combK a b = if a = 0 ∨ b = 0 then 0 else if a = 1 then b else if b = 1 then a else 0 := by
  unfold combK
  simp only [letN_eq, orB_eq, Bool.rec_eq, Nat.beq_eq]
  by_cases h : a = 0 ∨ b = 0 <;> simp [h]

private theorem combK_match {a b : Nat} {A B : Option (List Flags)}
    (ha : SearchMatch a A) (hb : SearchMatch b B) :
    SearchMatch (combK a b) (combOpt A B) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  constructor
  · intro h1
    rw [combK_eq] at h1
    by_cases h0 : a = 0 ∨ b = 0
    · rw [if_pos h0] at h1; omega
    · rw [if_neg h0] at h1
      by_cases h1a : a = 1
      · rw [if_pos h1a] at h1
        have hA : A = some [] := ha1 h1a
        have hB : B = some [] := hb1 h1
        rw [hA, hB]; simp [combOpt]
      · rw [if_neg h1a] at h1
        by_cases h1b : b = 1
        · rw [if_pos h1b] at h1
          have hA : A = some [] := ha1 h1
          have hB : B = some [] := hb1 h1b
          rw [hA, hB]; simp [combOpt]
        · rw [if_neg h1b] at h1; omega
  · intro S hS
    rw [combK_eq] at hS
    by_cases h0 : a = 0 ∨ b = 0
    · rw [if_pos h0] at hS; omega
    · rw [if_neg h0] at hS
      by_cases h1a : a = 1
      · rw [if_pos h1a] at hS
        have hA : A = some [] := ha1 h1a
        have hB : B = some [fl S] := hb2 S hS
        rw [hA, hB]; simp [combOpt]
      · rw [if_neg h1a] at hS
        by_cases h1b : b = 1
        · rw [if_pos h1b] at hS
          have hA : A = some [fl S] := ha2 S hS
          have hB : B = some [] := hb1 h1b
          rw [hA, hB]; simp [combOpt]
        · rw [if_neg h1b] at hS; omega

private theorem branchAll_append {rec : Flags → Flags → Option (List Flags)} {C : HCtx}
    {x : Nat} {I X : Flags} (l : List Nat) (j : Nat) :
    branchAll rec C x I X (l ++ [j]) =
      combOpt (branchAll rec C x I X l)
        (rec (extI C [(x, j)] I) (extX C [(x, j)] X)) := by
  induction l with
  | nil =>
    simp only [List.nil_append, branchAll]
    cases rec (extI C [(x, j)] I) (extX C [(x, j)] X) <;> simp [combOpt]
  | cons j' l' ih =>
    rw [List.cons_append]
    simp only [branchAll]
    rw [ih]
    cases rec (extI C [(x, j')] I) (extX C [(x, j')] X) <;>
      cases branchAll rec C x I X l' <;>
      cases rec (extI C [(x, j)] I) (extX C [(x, j)] X) <;>
      simp [combOpt, List.append_assoc]


private theorem runK_succ (n I X : Nat) :
    runK PB LB LI NL (Nat.succ n) I X =
      (if notB (Nat.beq (Nat.land I X) 0) then 1
       else if Nat.beq (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1) then Nat.add 2 I
       else
         let r := passK PB LB LI NL I X
         if bitK r 1386 then 1
         else if bitK r 1387 then
           runK PB LB LI NL n (Nat.land r (Nat.sub (Nat.shiftLeft 1 693) 1))
             (Nat.land (Nat.shiftRight r 693) (Nat.sub (Nat.shiftLeft 1 693) 1))
         else
           let a := minAccK PB LI NL I X
           if Nat.beq a (Nat.mul 1024 2048) then 0
           else branchK LB NL (runK PB LB LI NL n) (Nat.mod a 1024)
             (candK LI NL (Nat.mod a 1024) I X) (Nat.lor I (Nat.shiftLeft X 693))) := by
  unfold runK
  simp only [letN_eq, Bool.rec_eq]


private theorem branchK_match {go : Nat → Nat → Nat} {rec : Flags → Flags → Option (List Flags)}
    {I X x Cs : Nat}
    (h : ∀ j < 1024, SearchMatch
      (go (extK LB NL x j (I ||| X <<< 693) &&& (Nat.sub (Nat.shiftLeft 1 693) 1))
        (extK LB NL x j (I ||| X <<< 693) >>> 693))
      (rec (extI C [(x, j)] (fl I)) (extX C [(x, j)] (fl X)))) :
    SearchMatch (branchK LB NL go x Cs (I ||| X <<< 693))
      (branchAll rec C x (fl I) (fl X) ((List.range 1024).filter Cs.testBit)) := by
  let res : Nat → Nat := fun j =>
    go (extK LB NL x j (I ||| X <<< 693) &&& (Nat.sub (Nat.shiftLeft 1 693) 1))
      (extK LB NL x j (I ||| X <<< 693) >>> 693)
  let step : Nat → Nat → Nat := fun j acc => if Cs.testBit j then combK acc (res j) else acc
  have hmain : ∀ m, m ≤ 1024 → SearchMatch (Nat.rec 1 step m)
      (branchAll rec C x (fl I) (fl X) ((List.range m).filter Cs.testBit)) := by
    intro m
    induction m with
    | zero =>
      intro _
      show SearchMatch 1 (some [])
      exact ⟨fun _ => rfl, fun S hS => by omega⟩
    | succ m ih =>
      intro hm
      have hm' : m ≤ 1024 := by omega
      change SearchMatch (step m (Nat.rec 1 step m))
        (branchAll rec C x (fl I) (fl X) (List.filter Cs.testBit (List.range (Nat.succ m))))
      rw [List.range_succ, List.filter_append]
      by_cases hb : Cs.testBit m = true
      · have hstepm : step m (Nat.rec 1 step m) =
            combK (Nat.rec 1 step m) (res m) := by simp [step, hb]
        rw [hstepm]
        have hf : List.filter Cs.testBit [m] = [m] := by simp [hb]
        rw [hf, branchAll_append]
        exact combK_match (ih hm') (h m (by omega))
      · have hb' : Cs.testBit m = false := by simpa using hb
        have hstepm : step m (Nat.rec 1 step m) = Nat.rec 1 step m := by simp [step, hb']
        rw [hstepm]
        have hf : List.filter Cs.testBit [m] = [] := by simp [hb']
        rw [hf, List.append_nil]
        exact ih hm'
  have hbranch : branchK LB NL go x Cs (I ||| X <<< 693) = Nat.rec 1 step 1024 := by
    unfold branchK
    simp only [step, res, letN_eq, Bool.rec_eq, bitK_eq_testBit, Nat.land_eq,
      Nat.shiftRight_eq']
  rw [hbranch]
  exact hmain 1024 (le_refl 1024)

private theorem hstep_conflict {rec : Flags → Flags → Option (List Flags)} {I X : Flags}
    (hany : anyIn 693 (fun p => I[p]! && X[p]!) = true) : hstep C rec I X = some [] := by
  unfold hstep
  rw [if_pos hany]

private theorem hstep_complete {rec : Flags → Flags → Option (List Flags)} {I X : Flags}
    (hany : anyIn 693 (fun p => I[p]! && X[p]!) = false)
    (hall : allIn 0 693 (fun p => I[p]! || X[p]!) = true) : hstep C rec I X = some [I] := by
  unfold hstep
  rw [if_neg (by rw [hany]; simp), if_pos hall]

private theorem hstep_empty {rec : Flags → Flags → Option (List Flags)} {I X : Flags}
    (hany : anyIn 693 (fun p => I[p]! && X[p]!) = false)
    (hall : allIn 0 693 (fun p => I[p]! || X[p]!) = false)
    (hcs : (candsAt C I X).any (fun c => c.2.isEmpty) = true) : hstep C rec I X = some [] := by
  unfold hstep
  rw [if_neg (by rw [hany]; simp), if_neg (by rw [hall]; simp)]
  dsimp only
  rw [show (filterRange (fun x => I[x]! && C.pl[x]!.any fun y => !(I[y]! || X[y]!)) 693 []).map
      (fun x => (x, cands C x I X)) = candsAt C I X from rfl, if_pos hcs]

private theorem hstep_forced {rec : Flags → Flags → Option (List Flags)} {I X : Flags}
    (hany : anyIn 693 (fun p => I[p]! && X[p]!) = false)
    (hall : allIn 0 693 (fun p => I[p]! || X[p]!) = false)
    (hcs : (candsAt C I X).any (fun c => c.2.isEmpty) = false)
    (hf : (forcedOf (candsAt C I X)).isEmpty = false) :
    hstep C rec I X = rec (extI C (forcedOf (candsAt C I X)) I)
      (extX C (forcedOf (candsAt C I X)) X) := by
  unfold hstep
  rw [if_neg (by rw [hany]; simp), if_neg (by rw [hall]; simp)]
  dsimp only
  rw [show (filterRange (fun x => I[x]! && C.pl[x]!.any fun y => !(I[y]! || X[y]!)) 693 []).map
      (fun x => (x, cands C x I X)) = candsAt C I X from rfl,
    if_neg (by rw [hcs]; simp), if_pos (by rw [hf]; simp)]

private theorem hstep_branch {rec : Flags → Flags → Option (List Flags)} {I X : Flags}
    {d : Nat × List Nat}
    (hany : anyIn 693 (fun p => I[p]! && X[p]!) = false)
    (hall : allIn 0 693 (fun p => I[p]! || X[p]!) = false)
    (hcs : (candsAt C I X).any (fun c => c.2.isEmpty) = false)
    (hf : (forcedOf (candsAt C I X)).isEmpty = true)
    (hd : pickMin (candsAt C I X) = some d) :
    hstep C rec I X = branchAll rec C d.1 I X d.2 := by
  unfold hstep
  rw [if_neg (by rw [hany]; simp), if_neg (by rw [hall]; simp)]
  dsimp only
  rw [show (filterRange (fun x => I[x]! && C.pl[x]!.any fun y => !(I[y]! || X[y]!)) 693 []).map
      (fun x => (x, cands C x I X)) = candsAt C I X from rfl,
    if_neg (by rw [hcs]; simp), if_neg (by rw [hf]; simp), hd]

private theorem hM_eq : Nat.sub (Nat.shiftLeft 1 693) 1 = 2 ^ 693 - 1 := by
  rw [show Nat.shiftLeft 1 693 = 2 ^ 693 from Nat.one_shiftLeft 693]; rfl

private theorem hstep_none {rec : Flags → Flags → Option (List Flags)} {I X : Flags}
    (hany : anyIn 693 (fun p => I[p]! && X[p]!) = false)
    (hall : allIn 0 693 (fun p => I[p]! || X[p]!) = false)
    (hcs : (candsAt C I X).any (fun c => c.2.isEmpty) = false)
    (hf : (forcedOf (candsAt C I X)).isEmpty = true)
    (hpm : pickMin (candsAt C I X) = none) : hstep C rec I X = none := by
  unfold hstep
  rw [if_neg (by rw [hany]; simp), if_neg (by rw [hall]; simp)]
  dsimp only
  rw [show (filterRange (fun x => I[x]! && C.pl[x]!.any fun y => !(I[y]! || X[y]!)) 693 []).map
      (fun x => (x, cands C x I X)) = candsAt C I X from rfl,
    if_neg (by rw [hcs]; simp), if_neg (by rw [hf]; simp), hpm]

theorem runK_match (hC : SearchCtx C PB LB LI GI PL NL) (n : Nat) :
    ∀ I X : Nat, I < 2 ^ 693 → X < 2 ^ 693 →
      SearchMatch (runK PB LB LI NL n I X) (hsearch C n (fl I) (fl X)) := by
  induction n with
  | zero =>
    intro I X hI hX
    show SearchMatch 0 none
    exact ⟨fun h => by omega, fun S h => by omega⟩
  | succ n ih =>
    intro I X hI hX
    rw [runK_succ, hsearch]
    by_cases hc : I &&& X = 0
    · have hb1 : notB (Nat.beq (Nat.land I X) 0) = false := by
        have h : Nat.beq (Nat.land I X) 0 = true := by rw [Nat.beq_eq, Nat.land_eq]; exact hc
        rw [h]; rfl
      rw [if_neg (by rw [hb1]; simp)]
      by_cases hcomp : I ||| X = 2 ^ 693 - 1
      · have hb2 : Nat.beq (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1) = true := by
          rw [hM_eq, Nat.beq_eq, Nat.lor_eq]; exact hcomp
        rw [if_pos hb2]
        have hany : anyIn 693 (fun p => (fl I)[p]! && (fl X)[p]!) = false := by
          rw [Bool.eq_false_iff]
          intro h
          exact (anyIn_conflict_iff hI hX).1 h hc
        have hall : allIn 0 693 (fun p => (fl I)[p]! || (fl X)[p]!) = true :=
          (allIn_complete_iff hI hX).2 hcomp
        rw [hstep_complete hany hall]
        refine ⟨fun h => by change 2 + I = 1 at h; omega, fun S hS => by
          change 2 + I = 2 + S at hS
          rw [show S = I by omega]⟩
      · have hb2 : Nat.beq (Nat.lor I X) (Nat.sub (Nat.shiftLeft 1 693) 1) = false := by
          rw [hM_eq, Bool.eq_false_iff]
          intro hbeq
          rw [Nat.beq_eq, Nat.lor_eq] at hbeq
          exact hcomp hbeq
        rw [if_neg (by rw [hb2]; simp)]
        dsimp only
        have hany : anyIn 693 (fun p => (fl I)[p]! && (fl X)[p]!) = false := by
          rw [Bool.eq_false_iff]
          intro h
          exact (anyIn_conflict_iff hI hX).1 h hc
        have hall : allIn 0 693 (fun p => (fl I)[p]! || (fl X)[p]!) = false := by
          rw [Bool.eq_false_iff]
          intro h
          exact hcomp ((allIn_complete_iff hI hX).1 h)
        obtain ⟨hr1386, hr1387, hrI, hrX⟩ := passK_spec (C := C) hC hI hX hc
        by_cases h1386 : bitK (passK PB LB LI NL I X) 1386 = true
        · rw [if_pos h1386]
          have hcs : (candsAt C (fl I) (fl X)).any (fun c => c.2.isEmpty) = true := by
            have h : (passK PB LB LI NL I X).testBit 1386 = true := by
              rw [← bitK_eq_testBit]; exact h1386
            rwa [hr1386] at h
          rw [hstep_empty hany hall hcs]
          exact ⟨fun _ => rfl, fun S h => by omega⟩
        · rw [if_neg h1386]
          have hcs : (candsAt C (fl I) (fl X)).any (fun c => c.2.isEmpty) = false := by
            have h : (passK PB LB LI NL I X).testBit 1386 = false := by
              rw [← bitK_eq_testBit]
              exact Bool.eq_false_iff.mpr h1386
            rwa [hr1386] at h
          by_cases h1387 : bitK (passK PB LB LI NL I X) 1387 = true
          · rw [if_pos h1387]
            have hf : (forcedOf (candsAt C (fl I) (fl X))).isEmpty = false := by
              have h : (passK PB LB LI NL I X).testBit 1387 = true := by
                rw [← bitK_eq_testBit]; exact h1387
              rw [hr1387] at h
              simpa using h
            rw [hstep_forced hany hall hcs hf, hrI, hrX, hM_eq]
            exact ih (passK PB LB LI NL I X &&& (2 ^ 693 - 1))
              (passK PB LB LI NL I X >>> 693 &&& (2 ^ 693 - 1))
              (Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos 693) (by norm_num)))
              (Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos 693) (by norm_num)))
          · rw [if_neg h1387]
            have hf : (forcedOf (candsAt C (fl I) (fl X))).isEmpty = true := by
              have h : (passK PB LB LI NL I X).testBit 1387 = false := by
                rw [← bitK_eq_testBit]
                exact Bool.eq_false_iff.mpr h1387
              rw [hr1387] at h
              simpa using h
            cases hpm : pickMin (candsAt C (fl I) (fl X)) with
            | none =>
              have hbeq : Nat.beq (minAccK PB LI NL I X) (Nat.mul 1024 2048) = true := by
                rw [Nat.beq_eq]
                exact (minAccK_spec (C := C) hC hI hX hc).1 hpm
              rw [if_pos hbeq, hstep_none hany hall hcs hf hpm]
              exact ⟨fun h => by omega, fun S h => by omega⟩
            | some d =>
              obtain ⟨ha_eq, hd1, hd2⟩ := (minAccK_spec (C := C) hC hI hX hc).2 d hpm
              obtain ⟨hcand_lt, hcand_eq⟩ := candK_spec (C := C) hC hd1 hc
              have hd2' : d.2 = (List.range 1024).filter (candK LI NL d.1 I X).testBit := by
                rw [hd2, hcand_eq]
              have hne : minAccK PB LI NL I X ≠ 1024 * 2048 := by
                rw [ha_eq]
                have hlen : d.2.length ≤ 1024 := by
                  rw [hd2']
                  exact Nat.le_trans (List.length_filter_le
                    (fun j => (candK LI NL d.1 I X).testBit j) (List.range 1024)) (by simp)
                omega
              have hbeq : Nat.beq (minAccK PB LI NL I X) (Nat.mul 1024 2048) = false := by
                rw [Bool.eq_false_iff]
                intro hb
                rw [Nat.beq_eq] at hb
                exact hne (by simpa using hb)
              have hmod : Nat.mod (minAccK PB LI NL I X) 1024 = d.1 := by
                rw [ha_eq, Nat.add_comm, Nat.mul_comm]
                exact (Nat.add_mul_mod_self_right d.1 d.2.length 1024).trans
                  (Nat.mod_eq_of_lt (by omega))
              rw [if_neg (by rw [hbeq]; simp), hstep_branch hany hall hcs hf hpm]
              rw [hmod, hd2']
              refine branchK_match (go := runK PB LB LI NL n) (rec := hsearch C n) (I := I)
                (X := X) (x := d.1) (Cs := candK LI NL d.1 I X) (h := ?_)
              intro j hj
              obtain ⟨hSlt, hextI, hextX⟩ := extK_spec (C := C) hC hd1 hj hI hX
              have hbnd1 : extK LB NL d.1 j (I ||| X <<< 693) &&&
                  Nat.sub (Nat.shiftLeft 1 693) 1 < 2 ^ 693 := by
                apply Nat.and_lt_two_pow
                rw [hM_eq]
                exact Nat.sub_lt (Nat.two_pow_pos 693) (by norm_num)
              have hbnd2 : extK LB NL d.1 j (I ||| X <<< 693) >>> 693 < 2 ^ 693 := by
                rw [Nat.shiftRight_eq_div_pow]
                apply Nat.div_lt_of_lt_mul
                calc extK LB NL d.1 j (I ||| X <<< 693) < 2 ^ 1386 := hSlt
                  _ = 2 ^ 693 * 2 ^ 693 := by
                      rw [show (1386 : Nat) = 693 + 693 from by norm_num, Nat.pow_add]
              have hih := ih (extK LB NL d.1 j (I ||| X <<< 693) &&&
                Nat.sub (Nat.shiftLeft 1 693) 1)
                (extK LB NL d.1 j (I ||| X <<< 693) >>> 693) hbnd1 hbnd2
              simpa [hextI, hextX, hM_eq] using hih
    · have hb1 : notB (Nat.beq (Nat.land I X) 0) = true := by
        have h : Nat.beq (Nat.land I X) 0 = false := by
          rw [Bool.eq_false_iff]
          intro hbeq
          rw [Nat.beq_eq, Nat.land_eq] at hbeq
          exact hc hbeq
        rw [h]; rfl
      rw [if_pos hb1]
      have hany : anyIn 693 (fun p => (fl I)[p]! && (fl X)[p]!) = true :=
        (anyIn_conflict_iff hI hX).2 hc
      rw [hstep_conflict hany]
      exact ⟨fun _ => rfl, fun S h => by omega⟩
end CFSG.KC.Misc.Hyp

end
