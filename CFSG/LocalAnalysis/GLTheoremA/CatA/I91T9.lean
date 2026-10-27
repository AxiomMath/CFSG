module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)


@[expose] def isA2n (k : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A 2 q => q.p = 2 ∧ q.exponent = k | _ => False

theorem twoPart_pow_two (k : ℕ) : twoPart (2 ^ k) = 2 ^ k := by
  unfold twoPart
  rw [Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one]

theorem twoPart_eight_mul {m : ℕ} (hm : Odd m) : twoPart (m * 2 ^ 3) = 8 := by
  rw [FP.twoPart_mul_odd hm (by positivity), twoPart_pow_two]
  norm_num

theorem twoPart_360 : twoPart 360 = 8 := by
  have h : (360 : ℕ) = 45 * 2 ^ 3 := by norm_num
  rw [h, twoPart_eight_mul (by decide)]

theorem twoPart_20160 : twoPart 20160 = 64 := by
  have h : (20160 : ℕ) = 315 * 2 ^ 6 := by norm_num
  rw [h, FP.twoPart_mul_odd (by decide) (by positivity), twoPart_pow_two]
  norm_num

theorem orderA_two_gt {R : ℕ} (hR : 16 ≤ R) (h3 : R % 3 = 1) : 35942400 < orderA 2 R := by
  obtain ⟨Y, hYA, hXY⟩ := orderA_two_eq_mul h3
  rw [hYA]
  have h2 : 16 ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
  have h3' : 16 ^ 3 ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have hXlow : 255 * 4095 ≤ (R ^ 2 - 1) * (R ^ 3 - 1) := by
    apply Nat.mul_le_mul <;> omega
  have hY : 348075 ≤ Y := by omega
  have hR3 : 4096 ≤ R ^ 3 := by norm_num at h3'; omega
  have := Nat.mul_le_mul hR3 hY
  norm_num at this ⊢
  omega

theorem orderTwistedA_two_gt {R : ℕ} (hR : 32 ≤ R) : 35942400 < orderTwistedA 2 R := by
  unfold orderTwistedA
  have hprod : (∏ i ∈ Finset.Icc 2 (2 + 1), if Even i then R ^ i - 1 else R ^ i + 1) =
      (R ^ 2 - 1) * (R ^ 3 + 1) := by
    rw [show Finset.Icc 2 (2 + 1) = {2, 3} from by decide]
    simp [Finset.prod_insert, Nat.even_iff]
  rw [hprod, show 2 * (2 + 1) / 2 = 3 from rfl]
  have hg : Nat.gcd (2 + 1) (R + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hgpos : 0 < Nat.gcd (2 + 1) (R + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdiv : R ^ 3 * ((R ^ 2 - 1) * (R ^ 3 + 1)) / 3 ≤
      R ^ 3 * ((R ^ 2 - 1) * (R ^ 3 + 1)) / Nat.gcd (2 + 1) (R + 1) :=
    Nat.div_le_div_left hg hgpos
  have h2 : 32 ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
  have h3 : 32 ^ 3 ≤ R ^ 3 := Nat.pow_le_pow_left hR 3
  have hA : 1023 * 32769 ≤ (R ^ 2 - 1) * (R ^ 3 + 1) := by
    apply Nat.mul_le_mul <;> norm_num at h2 h3 ⊢ <;> omega
  have hN : 32768 * (1023 * 32769) ≤ R ^ 3 * ((R ^ 2 - 1) * (R ^ 3 + 1)) := by
    apply Nat.mul_le_mul <;> norm_num at h3 ⊢ <;> omega
  have hbig : 35942401 ≤ R ^ 3 * ((R ^ 2 - 1) * (R ^ 3 + 1)) / 3 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by norm_num at hN ⊢; omega)
  omega

theorem card_isA6 {S : Type} [Group S] [Finite S] (h : catalogIs S isA6) : Nat.card S = 360 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | alternating n hn =>
    simp only [isA6] at hi
    subst hi
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie _ => exact hi.elim

theorem card_isA2n {S : Type} [Group S] [Finite S] {k : ℕ} (h : catalogIs S (isA2n k)) :
    Nat.card S = orderA 2 (2 ^ k) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex h
  cases d with
  | A r q =>
    rcases r with _ | _ | _ | r
    all_goals first | exact hP.elim | skip
    have hc : Nat.card S = lieOrderFormula (LieTypeIndex.A 2 q) :=
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 2 q, hv⟩ S ⟨e⟩
    have hqc : q.card = 2 ^ k := by rw [PrimePower.card_def, hP.1, hP.2]
    rw [hc]
    show orderA 2 q.card = orderA 2 (2 ^ k)
    rw [hqc]
  | _ => exact hP.elim

theorem card_isU3n {S : Type} [Group S] [Finite S] {k : ℕ} (h : catalogIs S (isU3n k)) :
    Nat.card S = orderTwistedA 2 (2 ^ k) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex h
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | r
    all_goals first | exact hP.elim | skip
    have hc : Nat.card S = lieOrderFormula (LieTypeIndex.twistedA 2 q) :=
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedA 2 q, hv⟩ S ⟨e⟩
    have hqc : q.card = 2 ^ k := by rw [PrimePower.card_def, hP.1, hP.2]
    rw [hc]
    show orderTwistedA 2 q.card = orderTwistedA 2 (2 ^ k)
    rw [hqc]
  | _ => exact hP.elim

end I91T


end CFSG.LocalAnalysis.GLTheoremA
