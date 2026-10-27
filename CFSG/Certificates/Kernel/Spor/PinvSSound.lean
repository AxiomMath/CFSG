module

public import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Data.Finset.Card

public section

namespace CFSG.KS.PinvS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PF

@[expose, reducible] def InjK (n w p : Nat) : Prop :=
  (∀ i < n, pg w (mask w) p i < n) ∧
    ∀ a < n, ∀ b < n, pg w (mask w) p a = pg w (mask w) p b → a = b

theorem testBit_foldr_or (g : Nat → Nat) (t : Nat) : ∀ L : List Nat,
    (L.foldr (fun i s => Nat.lor s (g i)) 0).testBit t = L.any fun i => (g i).testBit t
  | [] => by simp
  | x :: L => by
    rw [List.foldr_cons, List.any_cons]
    change (_ ||| g x).testBit t = _
    rw [Nat.testBit_or, testBit_foldr_or g t L, Bool.or_comm]

theorem pinvS_testBit (n w p t : Nat) :
    (pinvS n w (mask w) p).testBit t =
      (List.range n).any fun i => (i <<< (w * pg w (mask w) p i)).testBit t := by
  unfold pinvS
  rw [CFSG.KS.Raw.Orb.foldN_eq]
  exact testBit_foldr_or (fun i => Nat.shiftLeft i (Nat.mul w (pg w (mask w) p i))) t _

theorem testBit_shl_field {w i j j' k : Nat} (hi : i < 2 ^ w) (hk : k < w) :
    (i <<< (w * j')).testBit (w * j + k) = (decide (j' = j) && i.testBit k) := by
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy j' j with h | h | h
  · have m1 := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at m1
    have e1 : w * j' ≤ w * j + k := by omega
    have hge : w ≤ w * j + k - w * j' := by omega
    have hz : i.testBit (w * j + k - w * j') = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hge))
    simp [e1, hz, Nat.ne_of_lt h]
  · subst h
    simp
  · have m1 := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at m1
    have e1 : ¬ w * j' ≤ w * j + k := by omega
    simp [e1, Nat.ne_of_gt h]

theorem pg_pinvS {n w p i : Nat} (hw : n < 2 ^ w) (hp : InjK n w p) (hi : i < n) :
    pg w (mask w) (pinvS n w (mask w) p) (pg w (mask w) p i) = i := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_pgM]
  by_cases hk : k < w
  · rw [pinvS_testBit]
    simp only [hk, decide_true, Bool.true_and]
    have e : ∀ i' ∈ List.range n, (i' <<< (w * pg w (mask w) p i')).testBit
        (w * pg w (mask w) p i + k) = (decide (i' = i) && i'.testBit k) := by
      intro i' h'
      have hi' : i' < n := List.mem_range.1 h'
      rw [testBit_shl_field (Nat.lt_trans hi' hw) hk]
      by_cases e : i' = i
      · subst e
        simp
      · have e' : pg w (mask w) p i' ≠ pg w (mask w) p i := fun h => e (hp.2 i' hi' i hi h)
        simp [e, e']
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨i', h', h⟩
      rw [e i' h', Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, h⟩ := h
      exact h
    · intro h
      refine ⟨i, List.mem_range.2 hi, ?_⟩
      rw [e i (List.mem_range.2 hi)]
      simp [h]
  · have hk' : w ≤ k := by omega
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_trans hi hw)
      (Nat.pow_le_pow_right (by omega) hk'))]
    simp [hk]

theorem pinvS_shr {n w p : Nat} (hw : n < 2 ^ w) (hp : ∀ i < n, pg w (mask w) p i < n) :
    pinvS n w (mask w) p >>> (n * w) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_shiftRight, Nat.zero_testBit, pinvS_testBit]
  apply Bool.eq_false_iff.2
  intro h
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨i, hi, h⟩ := h
  rw [Nat.testBit_shiftLeft] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have m1 := Nat.mul_le_mul_left w (Nat.succ_le_of_lt (hp i hi))
  rw [Nat.mul_succ] at m1
  have hge : w ≤ n * w + t - w * pg w (mask w) p i := by
    rw [Nat.mul_comm n w]
    omega
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_trans hi hw)
    (Nat.pow_le_pow_right (by omega) hge))] at h
  exact Bool.false_ne_true h.2

theorem surj_of_injK {n w p : Nat} (hp : InjK n w p) :
    ∀ j < n, ∃ i < n, pg w (mask w) p i = j := by
  intro j hj
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
    (fun a _ => pg w (mask w) p a) (fun a ha => by simpa using hp.1 a (by simpa using ha))
    (fun a₁ a₂ h₁ h₂ e => hp.2 a₁ (by simpa using h₁) a₂ (by simpa using h₂) e) le_rfl
  obtain ⟨i, hi, e⟩ := hsurj j (by simpa using hj)
  exact ⟨i, by simpa using hi, e.symm⟩

theorem injK_of_canonK {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hinj : ∀ a < n, ∀ b < n, pg w (mask w) p a = pg w (mask w) p b → a = b) : InjK n w p :=
  ⟨(canon_facts hp).2.2.2, hinj⟩

theorem permOK_pinvS {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hinj : InjK n w p) : permOK n w (mask w) (n * w) p (pinvS n w (mask w) p) = true := by
  obtain ⟨-, hw, hp0, hlt⟩ := canon_facts hp
  unfold permOK
  simp only [bAnd_iff]
  refine ⟨Nat.beq_eq.mpr hp0, Nat.beq_eq.mpr (pinvS_shr (by omega) hlt), ?_⟩
  refine CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => ?_
  rw [strictB_eqP, bAnd_iff]
  exact ⟨Nat.blt_eq.mpr (hlt i hi), Nat.beq_eq.mpr (pg_pinvS (by omega) hinj hi)⟩

theorem pinvS_lt {n w p : Nat} (hw : n < 2 ^ w) (hp : InjK n w p) :
    ∀ j < n, pg w (mask w) (pinvS n w (mask w) p) j < n := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := surj_of_injK hp j hj
  rw [pg_pinvS hw hp hi]
  exact hi

theorem injK_pinvS {n w p : Nat} (hw : n < 2 ^ w) (hp : InjK n w p) :
    InjK n w (pinvS n w (mask w) p) := by
  refine ⟨pinvS_lt hw hp, fun a ha b hb e => ?_⟩
  obtain ⟨a', ha', rfl⟩ := surj_of_injK hp a ha
  obtain ⟨b', hb', rfl⟩ := surj_of_injK hp b hb
  rw [pg_pinvS hw hp ha', pg_pinvS hw hp hb'] at e
  rw [e]

theorem canonK_pinvS {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hinj : InjK n w p) : canonK n w (mask w) (n * w) (pinvS n w (mask w) p) = true := by
  obtain ⟨-, hw, -, hlt⟩ := canon_facts hp
  have hp' := hp
  unfold canonK at hp' ⊢
  simp only [bAnd_iff] at hp' ⊢
  refine ⟨hp'.1, Nat.beq_eq.mpr (pinvS_shr (by omega) hlt), ?_⟩
  exact CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => Nat.blt_eq.mpr (pinvS_lt (by omega) hinj j hj)

theorem injK_pcomp {n w p q : Nat} (hn : n < 2 ^ 32) (hp : InjK n w p) (hq : InjK n w q) :
    InjK n w (pcomp n w (mask w) p q) := by
  refine ⟨fun i hi => ?_, fun a ha b hb e => ?_⟩
  · rw [pg_pcomp hn hi]
    exact hp.1 _ (hq.1 i hi)
  · rw [pg_pcomp hn ha, pg_pcomp hn hb] at e
    exact hq.2 a ha b hb (hp.2 _ (hq.1 a ha) _ (hq.1 b hb) e)

end CFSG.KS.PinvS

end
