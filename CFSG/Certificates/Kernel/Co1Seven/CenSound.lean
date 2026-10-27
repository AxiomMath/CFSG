module

public import Certificates.Data.Kernel.Co1Seven.Cen
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Certificates.Kernel.Co1BSound
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
public import CFSG.Sporadic.Schreier.Co1ThreeLocal

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Co1B CFSG.Sporadic.Co1Schreier.Native

local notation "U" => unpack 24 24

set_option exponentiation.threshold 1000

theorem unpack_powWK (M : Nat) : ∀ e : Nat, U (powWK M e) = pow (U M) e
  | 0 => by
    change U oneK = one
    rw [← unpackR_eq_unpack]
    exact CFSG.KC.Co1B.one_eq.symm
  | e + 1 => by
    change U (strictN (powWK M e) fun a => mulWK a M) = mul (pow (U M) e) (U M)
    rw [MatL.strictN_eq, ← mul_unpackW, unpack_powWK M e]

theorem foldr_rowV (X : Nat) : ∀ m j : Nat,
    ((List.range' j m).map (MatL.rowV X)).foldr (fun r acc => r + 16777216 * acc) 0 =
      X / 2 ^ (24 * j) % 2 ^ (24 * m)
  | 0, j => by simp only [List.range'_zero, List.map_nil, List.foldr_nil, Nat.mul_zero,
      Nat.pow_zero, Nat.mod_one]
  | m + 1, j => by
    rw [List.range'_succ, List.map_cons, List.foldr_cons, foldr_rowV X m (j + 1)]
    unfold MatL.rowV
    have e1 : 2 ^ (24 * (j + 1)) = 2 ^ (24 * j) * 2 ^ 24 := by
      rw [← Nat.pow_add, Nat.mul_succ]
    have e2 : 2 ^ (24 * (m + 1)) = 2 ^ 24 * 2 ^ (24 * m) := by
      rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
    rw [e1, e2, ← Nat.div_div_eq_div_mul, Nat.mod_mul]
    rfl

theorem unpack_toList (X : Nat) : (U X).toList = (List.range' 0 24).map (MatL.rowV X) := by
  apply List.ext_getElem
  · simp [MatL.unpack_size]
  · intro i h1 h2
    rw [Array.getElem_toList, MatL.unpack_getElem, List.getElem_map, List.getElem_range']
    simp

theorem key_unpack (X : Nat) : (U X).toList.foldr (fun r acc => r + 16777216 * acc) 0 = X % 2 ^ 576 := by
  rw [unpack_toList, foldr_rowV]
  simp

theorem eqU_of {X Y : Nat} (h : U X = U Y) : eqU X Y = true := by
  have e := congrArg (fun A : Array Nat => A.toList.foldr (fun r acc => r + 16777216 * acc) 0) h
  simp only [key_unpack] at e
  unfold eqU
  change Nat.beq (X % (1 <<< 576)) (Y % (1 <<< 576)) = true
  rw [Nat.one_shiftLeft, Nat.beq_eq]
  exact e

theorem eqU_one_of {X : Nat} (h : U X = one) : eqU X idM = true :=
  eqU_of (h.trans MatL.unpack_idM.symm)

theorem tgtK_of {x : Nat} (h1 : U x ≠ one)
    (hq : mul (U x) (U x) = one ∨ mul (mul (U x) (U x)) (U x) = one ∨
      mul (mul (mul (U x) (U x)) (mul (U x) (U x))) (U x) = one) : tgtK x = true := by
  have hx : Nat.beq x idM = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact h1 ((congrArg U (Nat.eq_of_beq_eq_true h)).trans MatL.unpack_idM)
  unfold tgtK
  rw [hx]
  change (strictB (mulWK x x) fun x2 => strictB (mulWK x2 x) fun x3 =>
    bIf(eqU x2 idM, true, bIf(eqU x3 idM, true, eqU (mulWK (mulWK x2 x2) x) idM))) = true
  rw [MatL.strictB_eq, MatL.strictB_eq]
  rcases hq with h | h | h
  · have e : eqU (mulWK x x) idM = true := eqU_one_of (by rw [← mul_unpackW]; exact h)
    simp only [e]
  · by_cases e2 : eqU (mulWK x x) idM = true
    · simp only [e2]
    · have e : eqU (mulWK (mulWK x x) x) idM = true :=
        eqU_one_of (by rw [← mul_unpackW, ← mul_unpackW]; exact h)
      simp only [Bool.eq_false_iff.2 e2, e]
  · by_cases e2 : eqU (mulWK x x) idM = true
    · simp only [e2]
    · by_cases e3 : eqU (mulWK (mulWK x x) x) idM = true
      · simp only [Bool.eq_false_iff.2 e2, e3]
      · simp only [Bool.eq_false_iff.2 e2, Bool.eq_false_iff.2 e3]
        exact eqU_one_of (by rw [← mul_unpackW, ← mul_unpackW, ← mul_unpackW]; exact h)

@[expose] noncomputable def witY (x a ai b bi : Array Nat) : Array Nat :=
  mul (mul x (mul (mul a x) ai)) (mul (mul b x) bi)

theorem wit7K_sound {P : Nat → Nat} {N x w : Nat} (h : wit7K P N x w = true) :
    ∃ a ai b bi, a < N ∧ ai < N ∧ b < N ∧ bi < N ∧ mul (U (P a)) (U (P ai)) = one ∧
      mul (U (P b)) (U (P bi)) = one ∧
      witY (U x) (U (P a)) (U (P ai)) (U (P b)) (U (P bi)) ≠ one ∧
      pow (witY (U x) (U (P a)) (U (P ai)) (U (P b)) (U (P bi))) 7 = one := by
  unfold wit7K at h
  simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨ha, hai, hb, hbi, hia, hib, hy1, hy7⟩ := h
  have hY : U (mulWK (mulWK x (mulWK (mulWK (P (fld16 w 0)) x) (P (fld16 w 1))))
      (mulWK (mulWK (P (fld16 w 2)) x) (P (fld16 w 3)))) =
      witY (U x) (U (P (fld16 w 0))) (U (P (fld16 w 1))) (U (P (fld16 w 2))) (U (P (fld16 w 3))) := by
    simp only [← mul_unpackW, witY]
  refine ⟨_, _, _, _, ha, hai, hb, hbi, ?_, ?_, ?_, ?_⟩
  · rw [mul_unpackW, Nat.eq_of_beq_eq_true hia, MatL.unpack_idM]
  · rw [mul_unpackW, Nat.eq_of_beq_eq_true hib, MatL.unpack_idM]
  · intro e
    rw [← hY] at e
    rw [eqU_one_of e] at hy1
    exact Bool.false_ne_true hy1
  · rw [← hY, ← unpack_powWK, Nat.eq_of_beq_eq_true hy7, MatL.unpack_idM]

theorem closK_sound {P : Nat → Nat} {N : Nat} {R C W : Nat → Nat} (h : closK P N R C W = true)
    {k : Nat} (hk : k < N) (ht : tgtK (P k) = true) :
    ∃ r c, r < N ∧ c < N ∧ mul (U (P k)) (U (P c)) = mul (U (P c)) (U (P r)) ∧
      wit7K P N (P r) (W r) = true := by
  unfold closK at h
  have hall := MatL.allN_iff.1 h
  have hk' := hall k hk
  rw [MatL.strictB_eq, MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, ht] at hk'
  simp only [MatL.strictB_eq] at hk'
  obtain ⟨hA, -⟩ := hk'
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hA
  obtain ⟨hr0, hr, hc, hrr, hm⟩ := hA
  have hR := hall (R k) hr
  rw [MatL.strictB_eq, MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true] at hR
  obtain ⟨-, hW⟩ := hR
  have hrr' : R (R k) = R k := Nat.eq_of_beq_eq_true hrr
  have hcond : (Nat.beq (R (R k)) (R k) && Nat.blt 0 (R k)) = true := by
    rw [hrr', Bool.and_eq_true, Nat.blt_eq]
    exact ⟨Nat.beq_refl _, hr0⟩
  rw [MatL.bAnd_eq, hcond] at hW
  simp only at hW
  refine ⟨R k, C k, hr, hc, ?_, hW⟩
  rw [mul_unpackW, mul_unpackW, Nat.eq_of_beq_eq_true hm]

theorem commGK_sound {G : Nat → Nat} {ng X : Nat} (h : commGK G ng X = true) :
    ∀ l < ng, mul (U (G l)) (U X) = mul (U X) (U (G l)) := by
  intro l hl
  rw [mul_unpackW, mul_unpackW, Nat.eq_of_beq_eq_true (MatL.allN_iff.1 h l hl)]

theorem centK_sound {P : Nat → Nat} {N Z : Nat} (h : centK P N Z = true) :
    ∀ k < N, mul (U (P k)) (U Z) = mul (U Z) (U (P k)) → pow (U (P k)) 7 = one := by
  intro k hk hc
  have hk' := MatL.allN_iff.1 h k hk
  have e : eqU (mulWK (P k) Z) (mulWK Z (P k)) = true :=
    eqU_of (by rw [← mul_unpackW, ← mul_unpackW]; exact hc)
  rw [MatL.strictB_eq, e] at hk'
  simp only at hk'
  rw [← unpack_powWK, Nat.eq_of_beq_eq_true hk', MatL.unpack_idM]

end CFSG.KS.SporSch.M24

end
