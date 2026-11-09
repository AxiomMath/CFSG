module

public import Certificates.Data.Kernel.Spor.Fi24F4W
public import CFSG.Certificates.Kernel.Spor.Fi24KitSound
public import CFSG.Certificates.Kernel.Spor.Fi24FixPSound

public section

namespace CFSG.KS.Fi24F4W

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
open CFSG.KC.Fi24F4W CFSG.KS.Fi24Net CFSG.KS.Fi24Kit
open CFSG.KC.MonsterConv.Perm (ones)

theorem letB_eq (v : Nat) (k : Nat → Bool) : letB v k = k v := by cases v <;> rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

@[expose] noncomputable def rG (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) (t : Bool)
    (x : Nat) : Nat :=
  wN NW cs (if t then pF NT x else x)

theorem rPt_eq (NW : Nat → Nat → Nat) (NT : Nat → Nat) (cs : List Nat) (t : Bool) (x : Nat) :
    rPt NW NT cs t x = rG NW NT cs t x := by
  unfold rPt rG
  rw [wP_eq]
  cases t
  · rfl
  · change wN NW cs (ptF NT x) = wN NW cs (pF NT x)
    rw [CFSG.KS.Fi24NetPt.ptF_eq]

theorem testBit_rPl {NW : Nat → Nat → Nat} {NT : Nat → Nat} {cs : List Nat} (hw : WV NW cs)
    (hT : NV NT) (t : Bool) (v q : Nat) :
    (rPl NW NT cs t v).testBit q = v.testBit (rG NW NT cs t q) := by
  unfold rPl rG
  cases t
  · exact testBit_walkP cs hw v q
  · change (netF NT (walkP NW cs v)).testBit q = _
    rw [testBit_netF hT, testBit_walkP cs hw]
    rfl

theorem rG_lt {NW : Nat → Nat → Nat} {NT : Nat → Nat} {cs : List Nat} (hw : WV NW cs)
    (hT : NV NT) (t : Bool) {q : Nat} (hq : q < 524288) : rG NW NT cs t q < 524288 := by
  unfold rG
  refine wN_lt cs hw _ ?_
  cases t
  · exact hq
  · exact pF_lt hT hq

theorem testBit_bitsL : ∀ (l : List Nat) (x : Nat), (bitsL l).testBit x = true ↔ x ∈ l
  | [], x => by simp [bitsL]
  | y :: l, x => by
    change (Nat.lor (Nat.shiftLeft 1 y) (bitsL l)).testBit x = true ↔ _
    rw [Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, testBit_bitsL l x, List.mem_cons]
    have e : Nat.shiftLeft 1 y = 2 ^ y := by
      change 1 <<< y = 2 ^ y
      rw [Nat.shiftLeft_eq, one_mul]
    rw [e, Nat.testBit_two_pow]
    simp only [decide_eq_true_eq]
    exact or_congr ⟨fun h => h.symm, fun h => h.symm⟩ Iff.rfl

theorem nthL_mem : ∀ (l : List (List Nat)) (j : Nat), nthL l j ∈ l ∨ nthL l j = []
  | [], _ => Or.inr rfl
  | _ :: _, 0 => Or.inl List.mem_cons_self
  | _ :: l, j + 1 => (nthL_mem l j).imp (List.mem_cons_of_mem _) id

theorem testBit_plK {F : Nat → Nat} {x : Nat} (hx : x < 524288)
    (hF : ∀ v, (F v).testBit x = v.testBit x) (k a : Nat) :
    (plK F k a).testBit x = a.testBit x := by
  unfold plK
  change (a &&& ((ones 524288) ^^^ ((F (CFSG.KC.Fi24FixP.idPl19 k)) ^^^
    (CFSG.KC.Fi24FixP.idPl19 k)))).testBit x = _
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, hF, CFSG.KS.Fi24FixP.testBit_ones,
    decide_eq_true hx, Bool.xor_self, Bool.xor_false, Bool.and_true]

section Pick

variable {NW : Nat → Nat → Nat} {NT : Nat → Nat} {cs : List Nat} {t : Bool}
  {prods : List (List Nat)} (hw : WV NW cs) (hp : ∀ c ∈ prods, WV NW c) (hT : NV NT) {x : Nat}
  (hr : rG NW NT cs t x = x) (hc : ∀ c ∈ prods, wN NW c x = x)
include hw hp hT hr hc

theorem testBit_wordF (j v : Nat) : (wordF NW NT cs t prods j v).testBit x = v.testBit x := by
  cases j with
  | zero =>
    change (rPl NW NT cs t v).testBit x = _
    rw [testBit_rPl hw hT t v x, hr]
  | succ j =>
    change (walkP NW (nthL prods j) v).testBit x = _
    rcases nthL_mem prods j with h | h
    · rw [testBit_walkP _ (hp _ h) v x, hc _ h]
    · rw [h]
      rfl

theorem testBit_pickM (hx : x < 524288) (P : List (List Nat)) (a : Nat) :
    (pickM NW NT cs t prods P a).testBit x = a.testBit x := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    change (strictN (pickM NW NT cs t prods P a)
      (plK (wordF NW NT cs t prods (nthN p 0)) (nthN p 1))).testBit x = _
    rw [CFSG.KS.Fi24FixP.strictN_eq, testBit_plK hx (testBit_wordF hw hp hT hr hc _), ih]

end Pick

theorem coverOK_spec {NW : Nat → Nat → Nat} {NT : Nat → Nat} {cs : List Nat} {t : Bool}
    {prods : List (List Nat)} {q₀ : Nat} {E : List Nat} (hw : WV NW cs)
    (hp : ∀ c ∈ prods, WV NW c) (hT : NV NT)
    {P₁ P₂ : List (List Nat)} {R : List Nat}
    (h : CFSG.KC.Fi24F4W.coverOK NW NT cs t prods q₀ E P₁ P₂ R = true)
    {x : Nat} (hx : x < 306936) (hr : rG NW NT cs t x = x) (hc : ∀ c ∈ prods, wN NW c x = x) :
    x ∈ q₀ :: E := by
  unfold CFSG.KC.Fi24F4W.coverOK at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  unfold covA at h1
  unfold covB at h2
  rw [letB_eq] at h1 h2
  have hP := testBit_pickM hw hp hT hr hc (by omega : x < 524288)
  have b1 : (pickM NW NT cs t prods P₁ (ones (nat_lit 306936))).testBit x = true := by
    rw [hP, CFSG.KS.Fi24FixP.testBit_ones]
    exact decide_eq_true hx
  rw [← Nat.eq_of_beq_eq_true h1, Nat.land_eq, Nat.testBit_and, Bool.and_eq_true] at b1
  have b2 : (pickM NW NT cs t prods P₂ (bitsL R)).testBit x = true := by
    rw [hP]
    exact b1.2
  rw [← Nat.eq_of_beq_eq_true h2, Nat.land_eq, Nat.testBit_and, Bool.and_eq_true] at b2
  exact (testBit_bitsL _ x).1 b2.2

theorem allLN_spec {l : List Nat} {f : Nat → Bool} (h : allLN l f = true) : ∀ x ∈ l, f x = true := by
  induction l with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons y l ih =>
    intro x hx
    have h' := andB_iff.1 h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h'.1
    · exact ih h'.2 x hx

theorem prodOK_spec {NW : Nat → Nat → Nat} {OL NT : Nat → Nat} {B c : List Nat} {q q₀ : Nat}
    (h : prodOK NW OL NT B c q q₀ = true) :
    ∀ b ∈ B, wN NW c b = clsK OL NT q (clsK OL NT q₀ b) := fun b hb => by
  have := Nat.eq_of_beq_eq_true (allLN_spec h b hb)
  rw [wP_eq] at this
  exact this

theorem witOK_spec {OL NT : Nat → Nat} {q₀ p q x : Nat} (h : witOK OL NT q₀ p q x = true) :
    clsK OL NT q (clsK OL NT q₀ (clsK OL NT p (clsK OL NT q (clsK OL NT q₀ (clsK OL NT p x))))) ≠
      x := by
  unfold witOK at h
  rw [letB_eq] at h
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem qfixOK_spec {NW : Nat → Nat → Nat} {NT : Nat → Nat} {cs : List Nat} {t : Bool}
    {Q : List Nat} (h : qfixOK NW NT cs t Q = true) : ∀ q ∈ Q, rG NW NT cs t q = q :=
  fun q hq => by
    have := Nat.eq_of_beq_eq_true (allLN_spec h q hq)
    rwa [rPt_eq] at this

theorem graphOK_spec {OL NT : Nat → Nat} {Q par : List Nat} {th : List (List Nat)} {m : Nat}
    (h : graphOK OL NT Q par th m = true) :
    (∀ j < m, j = 0 ∨ (nthN par j < j ∧
      clsK OL NT (nthN Q (nthN par j)) (nthN Q j) ≠ nthN Q j)) ∧
    ∀ i < m, ∀ j < m, clsK OL NT (nthN Q i) (nthN Q j) = nthN Q j ∨
      ∃ k < m, clsK OL NT (nthN Q k) (nthN Q i) = nthN Q i ∧
        clsK OL NT (nthN Q k) (nthN Q j) = nthN Q j := by
  unfold graphOK at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  refine ⟨fun j hj => ?_, fun i hi j hj => ?_⟩
  · have := CFSG.KS.allN_spec h1 j hj
    rcases orB_iff.1 this with h0 | h0
    · exact Or.inl (Nat.eq_of_beq_eq_true h0)
    · obtain ⟨ha, hb⟩ := andB_iff.1 h0
      refine Or.inr ⟨Nat.le_of_ble_eq_true ha, fun e => ?_⟩
      unfold commQ at hb
      rw [e, Nat.beq_refl] at hb
      exact Bool.noConfusion hb
  · have := CFSG.KS.allN_spec (CFSG.KS.allN_spec h2 i hi) j hj
    rw [strictB_eq'] at this
    by_cases hk : nthN (nthL th i) j = 0
    · rw [hk] at this
      exact Or.inl (Nat.eq_of_beq_eq_true this)
    · have hk' : Nat.beq (nthN (nthL th i) j) 0 = false := by
        cases hb : Nat.beq (nthN (nthL th i) j) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) hk
      rw [show (bIf(Nat.beq (nthN (nthL th i) j) 0, commQ OL NT (nthN Q i) (nthN Q j),
          andB (Nat.blt (Nat.sub (nthN (nthL th i) j) 1) m)
            (andB (commQ OL NT (nthN Q (Nat.sub (nthN (nthL th i) j) 1)) (nthN Q i))
              (commQ OL NT (nthN Q (Nat.sub (nthN (nthL th i) j) 1)) (nthN Q j))))) =
          andB (Nat.blt (Nat.sub (nthN (nthL th i) j) 1) m)
            (andB (commQ OL NT (nthN Q (Nat.sub (nthN (nthL th i) j) 1)) (nthN Q i))
              (commQ OL NT (nthN Q (Nat.sub (nthN (nthL th i) j) 1)) (nthN Q j))) by
          rw [hk']] at this
      obtain ⟨ha, hb⟩ := andB_iff.1 this
      obtain ⟨hc, hd⟩ := andB_iff.1 hb
      exact Or.inr ⟨_, Nat.le_of_ble_eq_true ha, Nat.eq_of_beq_eq_true hc,
        Nat.eq_of_beq_eq_true hd⟩

end CFSG.KS.Fi24F4W

end
