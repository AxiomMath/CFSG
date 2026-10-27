module

public import Certificates.Data.Kernel.PcReach

public section

namespace CFSG.KC.PcReach

open CFSG.KC.Enum

theorem land_one_eq (S q : Nat) :
    Nat.land (Nat.shiftRight S q) 1 = if S.testBit q then 1 else 0 := by
  change (S >>> q) &&& 1 = _
  rw [Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (S >>> q) with h | h <;>
    simp [Nat.testBit, Nat.one_and_eq_mod_two, h]

theorem testBit_lor_shift (S p q : Nat) :
    (Nat.lor S (Nat.shiftLeft 1 p)).testBit q = (S.testBit q || decide (p = q)) := by
  change (S ||| 1 <<< p).testBit q = _
  rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

theorem natRec_reach (w m : Nat) (G recs : List Nat) (X : Nat) :
    Nat.rec (motive := fun _ => Bool) (reachC w m G 0 recs)
      (fun n _ => reachC w m G (Nat.succ n) recs) X = reachC w m G X recs := by
  cases X <;> rfl

theorem reachC_sound {w m : Nat} {G : List Nat} {P : Nat → Prop}
    (hstep : ∀ q g, P q → g < G.length → P (pg w m (G.getD g 0) q)) :
    ∀ (recs : List Nat) (S : Nat), (∀ q, S.testBit q = true → P q) →
      reachC w m G S recs = true →
      (recs.map fun r => Nat.land r m).Nodup ∧
        ∀ p ∈ recs.map (fun r => Nat.land r m), S.testBit p = false ∧ P p
  | [], _, _, _ => by simp
  | r :: recs, S, hS, h => by
    have e : reachC w m G S (r :: recs) =
        (Nat.beq (Nat.land (Nat.shiftRight S (Nat.land (Nat.shiftRight r w) m)) 1) 1 &&
        Nat.beq (Nat.land (Nat.shiftRight S (Nat.land r m)) 1) 0 &&
        Nat.blt (Nat.shiftRight r (Nat.mul 2 w)) G.length &&
        Nat.beq (pg w m (G.getD (Nat.shiftRight r (Nat.mul 2 w)) 0)
          (Nat.land (Nat.shiftRight r w) m)) (Nat.land r m) &&
        Nat.rec (motive := fun _ => Bool) (reachC w m G 0 recs)
          (fun n _ => reachC w m G (Nat.succ n) recs)
          (Nat.lor S (Nat.shiftLeft 1 (Nat.land r m)))) := rfl
    rw [e, natRec_reach] at h
    simp only [Bool.and_eq_true, Nat.beq_eq_true_eq, Nat.blt_eq, land_one_eq] at h
    obtain ⟨⟨⟨⟨hq, hp⟩, hg⟩, hpg⟩, hrest⟩ := h
    have hq' : S.testBit (Nat.land (Nat.shiftRight r w) m) = true := by
      revert hq
      cases S.testBit (Nat.land (Nat.shiftRight r w) m) <;> simp
    have hp' : S.testBit (Nat.land r m) = false := by
      revert hp
      cases S.testBit (Nat.land r m) <;> simp
    have hPp : P (Nat.land r m) := Nat.eq_of_beq_eq_true hpg ▸ hstep _ _ (hS _ hq') hg
    have hS' : ∀ x, (Nat.lor S (Nat.shiftLeft 1 (Nat.land r m))).testBit x = true → P x := by
      intro x hx
      rw [testBit_lor_shift] at hx
      rcases Bool.or_eq_true_iff.mp hx with hx | hx
      · exact hS x hx
      · rw [← of_decide_eq_true hx]
        exact hPp
    obtain ⟨hnd, hall⟩ := reachC_sound hstep recs _ hS' hrest
    refine ⟨List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩, fun x hx => ?_⟩
    · have := (hall _ hmem).1
      rw [testBit_lor_shift] at this
      simp at this
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hp', hPp⟩
      · obtain ⟨h1, h2⟩ := hall x hx
        rw [testBit_lor_shift] at h1
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h1
        exact ⟨h1.1, h2⟩

end CFSG.KC.PcReach

end
