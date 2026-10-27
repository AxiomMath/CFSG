module

public import CFSG.Certificates.Kernel.F4T7BRec
public import CFSG.Certificates.Kernel.F4T7BMap

public section

namespace CFSG.KC.F4T7B

open CFSG.Fischer CFSG.KC.F4M3B CFSG.RankThree.PartTwo.Sec10.KS1012GL34
  CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light

@[expose] def codeL (A : M3) : Nat := codeM (toL A)

theorem testBit_sumPow (C : List Nat) (n : Nat) : (sumPow C).testBit n = decide (n ∈ C) := by
  induction C with
  | nil => simp [sumPow]
  | cons c C ih =>
    simp only [sumPow, List.foldr_cons] at ih ⊢
    change ((1 <<< c) ||| _).testBit n = _
    rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp only [List.mem_cons, Bool.decide_or]
    by_cases h : n = c
    · simp [h]
    · simp [h, Ne.symm h]

@[expose] def AllOnes (T : Nat) : Prop := ∀ c, c < 2 ^ 18 → T.testBit c = true

theorem allOnes_gen (m : Nat) (c : Nat) (hc : c < 2 ^ m) :
    (Nat.sub (Nat.pow 2 (Nat.pow 2 m)) 1).testBit c = true := by
  rw [Nat.sub_eq, Nat.pow_eq, Nat.pow_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hc

set_option exponentiation.threshold 262144 in
theorem chkAll_eq {om : List Pt} {C K : List Nat} (h : chkAll om C K = true) :
    ∃ T, AllOnes T ∧ chkI T (plns 18) om C K = true := by
  have hA : AllOnes (Nat.sub (Nat.pow 2 (Nat.pow 2 18)) 1) := allOnes_gen 18
  unfold chkAll plnK at h
  generalize hT : Nat.sub (Nat.pow 2 (Nat.pow 2 18)) 1 = T at h hA
  simp only [frc_eq] at h
  exact ⟨T, hA, h⟩

theorem plns_bits (A : M3) :
    (plns 18).map (fun n => n.testBit (codeL A)) = bits A := by
  have hc := codeM_lt (toL A)
  simp only [plns, MatT.map, pln_bit, hc, decide_true, Bool.true_and, c0, c1, c2, c3, c4, c5,
    c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, codeL]
  rfl

theorem stabX_bit {T : Nat} (hT : AllOnes T) (A : M3) (om : List Pt) :
    (stabX (natOps T) (plns 18) om).testBit (codeL A) = stabX boolOps (bits A) om := by
  rw [stabX_map (natOps _) boolOps (fun n => n.testBit (codeL A))
    (fun p q => Nat.testBit_and p q (codeL A)) (fun p q => Nat.testBit_xor p q (codeL A))
    (hT _ (codeM_lt _)), plns_bits]

theorem mem_C_iff {i : Fin 6} {C K : List Nat} (h : chkAll (omC i.val) C K = true) (A : M3) :
    (decide (Light.detL A = 1) && stabLn i.val A) = decide (codeL A ∈ C) := by
  obtain ⟨T, hT, h1⟩ := chkAll_eq h
  unfold chkI at h1
  simp only [Bool.and_eq_true] at h1
  have hX := Nat.eq_of_beq_eq_true h1.1.1.1.2
  rw [← stabX_omC, ← stabX_bit hT, hX, testBit_sumPow]

end CFSG.KC.F4T7B

end
