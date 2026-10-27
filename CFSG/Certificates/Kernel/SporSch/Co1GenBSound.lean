module

public import Certificates.Data.Kernel.SporSch.Co1GenB
public import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas

public section

namespace CFSG.KS.SporSch.VOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.KS.SporSch.M24.ActL

theorem testBit_actK (X v i : Nat) : (actK X v).testBit i =
    (decide (i ∈ List.range 24) && xs (fun j => (rowK X i).testBit j && v.testBit j) (List.range 24)) := by
  rw [actK_eq_foldr, testBit_foldr_or, parK_and _ _ (rowK_lt X i)]

theorem actK_xor (X a b : Nat) : actK X (a ^^^ b) = actK X a ^^^ actK X b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e : xs (fun j => (rowK X i).testBit j && (a ^^^ b).testBit j) (List.range 24) =
      (xs (fun j => (rowK X i).testBit j && a.testBit j) (List.range 24) ^^
        xs (fun j => (rowK X i).testBit j && b.testBit j) (List.range 24)) := by
    rw [← xs_xor]
    exact xs_congr fun j _ => by
      rw [Nat.testBit_xor]
      cases (rowK X i).testBit j <;> cases a.testBit j <;> cases b.testBit j <;> rfl
  rw [Nat.testBit_xor, testBit_actK, testBit_actK, testBit_actK, e]
  cases decide (i ∈ List.range 24) <;> simp

theorem actK_congr (X : Nat) {a b : Nat} (h : ∀ j < 24, a.testBit j = b.testBit j) :
    actK X a = actK X b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_actK, testBit_actK, xs_congr (fun j hj => by rw [h j (List.mem_range.1 hj)])]

theorem lnB_tab {X B : Nat} (h : tabOK X B = true) {e : Nat} (he : e < 96) :
    lnB B e = actK X ((e % 16) <<< (4 * (e / 16))) := by
  have := (MatL.allN_iff.1 h) e he
  rw [Nat.beq_eq] at this
  rw [this]
  have e1 : Nat.land e 15 = e % 16 := Nat.and_two_pow_sub_one_eq_mod e 4
  have e2 : Nat.shiftRight e 4 = e / 16 := Nat.shiftRight_eq_div_pow e 4
  change actK X (Nat.shiftLeft (Nat.land e 15) (4 * Nat.shiftRight e 4)) = _
  rw [e1, e2]
  rfl

theorem testBit_15 (m : Nat) : (15 : Nat).testBit m = decide (m < 4) :=
  Nat.testBit_two_pow_sub_one 4 m

theorem actN_eq {X B : Nat} (h : tabOK X B = true) (v : Nat) : actN B v = actK X v := by
  have lane : ∀ k < 6, lnB B (16 * k + ((v >>> (4 * k)) &&& 15)) =
      actK X (((v >>> (4 * k)) &&& 15) <<< (4 * k)) := by
    intro k hk
    have hl : (v >>> (4 * k)) &&& 15 < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
    rw [lnB_tab h (by omega)]
    have e1 : (16 * k + ((v >>> (4 * k)) &&& 15)) % 16 = (v >>> (4 * k)) &&& 15 := by omega
    have e2 : (16 * k + ((v >>> (4 * k)) &&& 15)) / 16 = k := by omega
    rw [e1, e2]
  have l0 : lnB B (0 + ((v >>> 0) &&& 15)) = actK X (((v >>> 0) &&& 15) <<< 0) := lane 0 (by omega)
  have l1 : lnB B (16 + ((v >>> 4) &&& 15)) = actK X (((v >>> 4) &&& 15) <<< 4) := lane 1 (by omega)
  have l2 : lnB B (32 + ((v >>> 8) &&& 15)) = actK X (((v >>> 8) &&& 15) <<< 8) := lane 2 (by omega)
  have l3 : lnB B (48 + ((v >>> 12) &&& 15)) = actK X (((v >>> 12) &&& 15) <<< 12) :=
    lane 3 (by omega)
  have l4 : lnB B (64 + ((v >>> 16) &&& 15)) = actK X (((v >>> 16) &&& 15) <<< 16) :=
    lane 4 (by omega)
  have l5 : lnB B (80 + ((v >>> 20) &&& 15)) = actK X (((v >>> 20) &&& 15) <<< 20) :=
    lane 5 (by omega)
  change lnB B (0 + ((v >>> 0) &&& 15)) ^^^ lnB B (16 + ((v >>> 4) &&& 15)) ^^^
    lnB B (32 + ((v >>> 8) &&& 15)) ^^^ lnB B (48 + ((v >>> 12) &&& 15)) ^^^
    lnB B (64 + ((v >>> 16) &&& 15)) ^^^ lnB B (80 + ((v >>> 20) &&& 15)) = actK X v
  rw [l0, l1, l2, l3, l4, l5, ← actK_xor, ← actK_xor, ← actK_xor, ← actK_xor, ← actK_xor]
  apply actK_congr
  intro j hj
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight,
    testBit_15]
  interval_cases j <;> simp

theorem actS_eq {M B : Nat → Nat} (h : allN 93 (fun g => tabOK (M g) (B g)) = true) :
    actS M B = fun g v => actK (M g) v := by
  funext g v
  unfold actS
  rw [MatL.nIf_eq]
  by_cases hg : g < 93
  · rw [if_pos (by simpa [Nat.blt_eq] using hg)]
    exact actN_eq ((MatL.allN_iff.1 h) g hg) v
  · rw [if_neg (by simpa [Nat.blt_eq] using hg)]

theorem levelSlQ_eq_A (M : Nat → Nat) (q : Nat) (gens : List Nat) (n : Nat) (T E : Nat → Nat)
    (lo len c₀ c₁ : Nat) :
    levelSlQ M q gens n T E lo len c₀ c₁ = levelSlA (fun g v => actK (M g) v) q gens n T E lo len c₀ c₁ :=
  rfl

theorem hl_of_tab {M B : Nat → Nat} (htb : allN 93 (fun g => tabOK (M g) (B g)) = true)
    {q : Nat} {gens : List Nat} {n : Nat} {T E C : Nat → Nat} {NS L : Nat}
    (h : ∀ s < NS, levelSlA (actS M B) q gens n T E (s * L) L (C s) (C (s + 1)) = true) :
    ∀ s < NS, levelSlQ M q gens n T E (s * L) L (C s) (C (s + 1)) = true := by
  intro s hs
  rw [levelSlQ_eq_A, ← actS_eq htb]
  exact h s hs

end CFSG.KS.SporSch.VOrb

end
