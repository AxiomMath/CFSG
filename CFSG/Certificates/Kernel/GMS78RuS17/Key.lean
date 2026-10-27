module

public import CFSG.Certificates.Kernel.GMS78RuGenS
import CFSG.Certificates.Kernel.GMS78RuP.Basic
public import Certificates.Data.Kernel.GMS78RuS
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.GMS.S17

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

private theorem brec_eq (b : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t b = if b then t else e := by cases b <;> rfl

theorem sKey_aux (m : Nat → Nat → Nat) (u : Nat) : ∀ n,
    sKey m n u = ((List.range n).countP fun p => m p u == m u p) +
      ((List.range n).countP fun p => m p p == u && m p u == m u p) * 2 ^ 14 +
      ((List.range n).countP fun p => m p p == 256 && m p u == m u p) * 2 ^ 28
  | 0 => by simp [sKey]
  | n + 1 => by
    have e : sKey m (n + 1) u = strictN (sKey m n u) (fun a => Bool.rec (motive := fun _ => Nat) a
      ((fun s => Nat.add a (Nat.add 1 (Nat.add
        (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s u)) 14)
        (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s 256)) 28)))) (m n n))
      (Nat.beq (m n u) (m u n))) := rfl
    rw [e, P117.strictN_eq, sKey_aux m u n]
    simp only [brec_eq, P117.beq_eq, List.range_succ, List.countP_append, List.countP_cons,
      List.countP_nil, Nat.shiftLeft_eq, Nat.add_eq, decide_eq_true_eq]
    by_cases h1 : m n u = m u n <;> by_cases h2 : m n n = u <;> by_cases h3 : m n n = 256 <;>
      simp [h1, h2, h3] <;> omega

section Read

variable {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8} {ε : Bool}
  {m : Nat → Nat → Nat}

theorem sInvs_eq (hEq : ∀ p < 8192, ∀ q < 8192, m p q = Gen.mul17G gA dA dct ε p q) :
    sInvs m 8192 = Gen.inv17G gA dA dct ε := by
  unfold sInvs Gen.inv17G
  rw [P117.sFilter_eq]
  refine List.filter_congr fun u hu => ?_
  have h := List.mem_range.1 hu
  simp only [P117.andB_eq, P117.notB_eq, P117.beq_eq, hEq u h u h, Bool.and_assoc, bne]

theorem sFilter_cent (hEq : ∀ p < 8192, ∀ q < 8192, m p q = Gen.mul17G gA dA dct ε p q)
    {u : Nat} (hu : u < 8192) :
    sFilter 8192 (fun p => Nat.beq (m p u) (m u p)) = Gen.cent17G gA dA dct ε u := by
  unfold Gen.cent17G
  rw [P117.sFilter_eq]
  refine List.filter_congr fun p hp => ?_
  have h := List.mem_range.1 hp
  simp only [P117.beq_eq, hEq p h u hu, hEq u hu p h]

private theorem cnt_eq (hEq : ∀ p < 8192, ∀ q < 8192, m p q = Gen.mul17G gA dA dct ε p q)
    {u : Nat} (hu : u < 8192) (t : Nat) :
    (List.range 8192).countP (fun p => m p p == t && m p u == m u p) =
      Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) t := by
  unfold Gen.cntR17G Gen.cent17G
  rw [List.countP_filter]
  refine List.countP_congr fun p hp => ?_
  have h := List.mem_range.1 hp
  simp only [hEq p h p h, hEq p h u hu, hEq u hu p h]

private theorem len_eq (hEq : ∀ p < 8192, ∀ q < 8192, m p q = Gen.mul17G gA dA dct ε p q)
    {u : Nat} (hu : u < 8192) :
    (List.range 8192).countP (fun p => m p u == m u p) =
      (Gen.cent17G gA dA dct ε u).length := by
  unfold Gen.cent17G
  rw [List.countP_eq_length_filter]
  refine congrArg List.length (List.filter_congr fun p hp => ?_)
  have h := List.mem_range.1 hp
  simp only [hEq p h u hu, hEq u hu p h]

theorem sKey_eq (hEq : ∀ p < 8192, ∀ q < 8192, m p q = Gen.mul17G gA dA dct ε p q)
    {u : Nat} (hu : u < 8192) :
    sKey m 8192 u = (Gen.cent17G gA dA dct ε u).length +
      Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u * 2 ^ 14 +
      Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256 * 2 ^ 28 := by
  rw [sKey_aux, len_eq hEq hu, cnt_eq hEq hu, cnt_eq hEq hu]

private theorem kN_eq (k : Nat) : kN k = k % 2 ^ 14 := by
  change k &&& 16383 = _
  rw [show (16383 : Nat) = 2 ^ 14 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

private theorem kR1_eq (k : Nat) : kR1 k = k / 2 ^ 14 % 2 ^ 14 := by
  change (k >>> 14) &&& 16383 = _
  rw [show (16383 : Nat) = 2 ^ 14 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

private theorem kR2_eq (k : Nat) : kR2 k = k / 2 ^ 28 % 2 ^ 14 := by
  change (k >>> 28) &&& 16383 = _
  rw [show (16383 : Nat) = 2 ^ 14 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

private theorem kKeyPart_eq (k : Nat) : kKeyPart k = k % 2 ^ 42 := by
  change k &&& ((1 <<< 42) - 1) = _
  rw [Nat.one_shiftLeft]
  exact Nat.and_two_pow_sub_one_eq_mod k 42

theorem key_read (hEq : ∀ p < 8192, ∀ q < 8192, m p q = Gen.mul17G gA dA dct ε p q)
    {u : Nat} (hu : u < 8192) {k : Nat} (h : sKey m 8192 u = kKeyPart k) :
    kN k = (Gen.cent17G gA dA dct ε u).length ∧
      kR1 k = Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u ∧
      kR2 k = Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256 := by
  rw [sKey_eq hEq hu, kKeyPart_eq] at h
  have h1 : (Gen.cent17G gA dA dct ε u).length ≤ 8192 :=
    (List.length_filter_le _ _).trans (by simp)
  have h2 : ∀ t, Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) t ≤ 8192 := fun t =>
    List.countP_le_length.trans h1
  have h3 := h2 u
  have h4 := h2 256
  rw [kN_eq, kR1_eq, kR2_eq]
  generalize (Gen.cent17G gA dA dct ε u).length = A at *
  generalize Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u = B at *
  generalize Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256 = D at *
  norm_num at h ⊢
  omega

theorem shr10 (u : Nat) : Nat.shiftRight u 10 = u / 1024 :=
  (Nat.shiftRight_eq_div_pow u 10).trans (by norm_num)

theorem kNeedZ_eq (hEq : ∀ p < 8192, ∀ q < 8192, m p q = Gen.mul17G gA dA dct ε p q)
    {u : Nat} (hu : u < 8192) {k : Nat} (h : sKey m 8192 u = kKeyPart k) :
    kNeedZ u k = needZ17 u (Gen.cent17G gA dA dct ε u).length
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) u)
      (Gen.cntR17G gA dA dct ε (Gen.cent17G gA dA dct ε u) 256) := by
  obtain ⟨h1, h2, h3⟩ := key_read hEq hu h
  simp only [kNeedZ, needZ17, P117.andB_eq, P117.notB_eq, P117.beq_eq, h1, h2, h3,
    shr10, Bool.and_assoc, bne]

end Read

end CFSG.KC.GMS.S17

end
