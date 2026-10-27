module

public import Certificates.Data.Kernel.Spor.Fi24FreeK
public import CFSG.Certificates.Kernel.Spor.Fi24ThreeOSound

public section

namespace CFSG.KS.Fi24FreeK

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24FreeK CFSG.KC.Benes CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt
  CFSG.KS.Fi24ThreeO

variable {NW : Nat → Nat → Nat} {NT OL : Nat → Nat}

theorem and_t {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem letB_e (v : Nat) (k : Nat → Bool) : letB v k = k v := by
  cases v <;> rfl

theorem beq_t {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem nbeq_t {a b : Nat} (h : notB (Nat.beq a b) = true) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem xP_eq (c0 c1 p : Nat) :
    xP OL NT c0 c1 p = clsK OL NT 0 (clsK OL NT 305530 (clsK OL NT c0 (clsK OL NT c1 p))) := by
  unfold xP
  rw [Fi24NetPt.strictN_eq, Fi24NetPt.strictN_eq, Fi24NetPt.strictN_eq]

@[expose] def PpN (OL NT : Nat → Nat) (c0 c1 a : Nat) : Prop :=
  clsK OL NT a (xP OL NT c0 c1 a) ≠ xP OL NT c0 c1 a ∧
    xP OL NT c0 c1 (xP OL NT c0 c1 a) = clsK OL NT a (xP OL NT c0 c1 a)

theorem ppB_spec {c0 c1 a : Nat} : ppB OL NT c0 c1 a = true ↔ PpN OL NT c0 c1 a := by
  unfold ppB PpN
  rw [letB_e, letB_e]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := and_t h
    exact ⟨nbeq_t h1, beq_t h2⟩
  · rintro ⟨h1, h2⟩
    have e1 : Nat.beq (clsK OL NT a (xP OL NT c0 c1 a)) (xP OL NT c0 c1 a) = false := by
      cases e : Nat.beq (clsK OL NT a (xP OL NT c0 c1 a)) (xP OL NT c0 c1 a)
      · rfl
      · exact absurd (beq_t e) h1
    rw [e1, h2, Nat.beq_refl]
    rfl

theorem failB_spec {c0 c1 a q : Nat} (h : failB OL NT c0 c1 a q = true) :
    PpN OL NT c0 c1 q ∧ q ≠ a ∧ clsK OL NT a q = q ∧ clsK OL NT (xP OL NT c0 c1 a) q ≠ q := by
  unfold failB at h
  obtain ⟨h1, h2⟩ := and_t h
  obtain ⟨h3, h4⟩ := and_t h2
  obtain ⟨h5, h6⟩ := and_t h4
  exact ⟨ppB_spec.1 h1, nbeq_t h3, beq_t h5, nbeq_t h6⟩

theorem lamOK_spec (hV : VN NW NT) {c0 c1 P a : Nat} {Wa Wx : List Nat}
    (h : lamOK NW NT OL c0 c1 P a Wa Wx = true) :
    PpN OL NT c0 c1 a ∧ cP NW NT Wa 0 = a ∧ cP NW NT Wx 0 = xP OL NT c0 c1 a ∧
      ∀ q < 306936, P.testBit q = true → q ≠ a →
        (cP NW NT (invC Wa) q < 306936 ∧ pF NT (cP NW NT (invC Wa) q) = cP NW NT (invC Wa) q) →
        cP NW NT (invC Wx) q < 306936 ∧ pF NT (cP NW NT (invC Wx) q) = cP NW NT (invC Wx) q := by
  unfold lamOK at h
  obtain ⟨h1, h2⟩ := and_t h
  obtain ⟨h3, h4⟩ := and_t h2
  obtain ⟨h5, h6⟩ := and_t h4
  rw [letB_e] at h6
  have e0 := beq_t h6
  refine ⟨ppB_spec.1 h1, by rw [← ptC_eq]; exact beq_t h3, by rw [← ptC_eq]; exact beq_t h5, ?_⟩
  intro q hq hP hqa hA
  have hq' : q < 524288 := by omega
  have fT : ∀ W : List Nat, (ctP NW NT (fixC NW NT [26]) W).testBit q = true ↔
      cP NW NT (invC W) q < 306936 ∧ pF NT (cP NW NT (invC W) q) = cP NW NT (invC W) q := by
    intro W
    unfold ctP
    rw [testBit_wkC hV _ _ hq', testBit_fixC hV]
    rfl
  by_contra hX
  have hb := congrArg (fun n => n.testBit q) e0
  simp only [Nat.zero_testBit] at hb
  rw [nland, nland, nland, nxor, nxor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and,
    Nat.testBit_xor, Nat.testBit_xor, hP, (fT Wa).2 hA, ptsM_bit hq, nshl, Nat.one_shiftLeft,
    Nat.testBit_two_pow] at hb
  have hX' : (ctP NW NT (fixC NW NT [26]) Wx).testBit q = false := by
    cases e : (ctP NW NT (fixC NW NT [26]) Wx).testBit q
    · rfl
    · exact absurd ((fT Wx).1 e) hX
  rw [hX', decide_eq_false (Ne.symm hqa)] at hb
  exact absurd hb (by decide)

end CFSG.KS.Fi24FreeK

end
