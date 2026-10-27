module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T9
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagChev
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)


theorem two_pow_mod_nine_eq (k : ℕ) : 2 ^ k % 9 = 2 ^ (k % 6) % 9 := by
  conv_lhs => rw [← Nat.div_add_mod k 6, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem even_of_mod_nine_47 {k : ℕ} (h : 2 ^ k % 9 = 4 ∨ 2 ^ k % 9 = 7) : Even k := by
  rw [two_pow_mod_nine_eq] at h
  have hk : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [Nat.even_iff]
  interval_cases hr : k % 6 <;> simp_all <;> omega

theorem odd_of_mod_nine_25 {k : ℕ} (h : 2 ^ k % 9 = 2 ∨ 2 ^ k % 9 = 5) (hk2 : 2 ≤ k) : Odd k ∧ 5 ≤ k := by
  rw [two_pow_mod_nine_eq] at h
  have hk : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hodd : k % 2 = 1 := by
    interval_cases hr : k % 6 <;> simp_all <;> omega
  refine ⟨Nat.odd_iff.2 hodd, ?_⟩
  by_contra hlt
  have : k = 3 := by omega
  subst this
  norm_num at h

theorem orderA_two_gt_25920 {x : ℕ} (hx : 7 ≤ x) : 25920 < orderA 2 x := by
  unfold orderA
  have hprod : (∏ i ∈ Finset.Icc 2 (2 + 1), (x ^ i - 1)) = (x ^ 2 - 1) * (x ^ 3 - 1) := by
    rw [show Finset.Icc 2 (2 + 1) = {2, 3} from by decide]
    simp [Finset.prod_insert]
  rw [hprod, show 2 * (2 + 1) / 2 = 3 from rfl]
  have hg : Nat.gcd (2 + 1) (x - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hgpos : 0 < Nat.gcd (2 + 1) (x - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdiv : x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) / 3 ≤
      x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) / Nat.gcd (2 + 1) (x - 1) :=
    Nat.div_le_div_left hg hgpos
  have h2 : 7 ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
  have h3 : 7 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have hA : 48 * 342 ≤ (x ^ 2 - 1) * (x ^ 3 - 1) := by
    apply Nat.mul_le_mul <;> norm_num at h2 h3 ⊢ <;> omega
  have hN : 343 * (48 * 342) ≤ x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) := by
    apply Nat.mul_le_mul <;> norm_num at h3 ⊢ <;> omega
  have hbig : 25921 ≤ x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1)) / 3 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by norm_num at hN ⊢; omega)
  omega

theorem orderTwistedA_two_gt_25920 {x : ℕ} (hx : 5 ≤ x) : 25920 < orderTwistedA 2 x := by
  unfold orderTwistedA
  have hprod : (∏ i ∈ Finset.Icc 2 (2 + 1), if Even i then x ^ i - 1 else x ^ i + 1) =
      (x ^ 2 - 1) * (x ^ 3 + 1) := by
    rw [show Finset.Icc 2 (2 + 1) = {2, 3} from by decide]
    simp [Finset.prod_insert, Nat.even_iff]
  rw [hprod, show 2 * (2 + 1) / 2 = 3 from rfl]
  have hg : Nat.gcd (2 + 1) (x + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hgpos : 0 < Nat.gcd (2 + 1) (x + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdiv : x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) / 3 ≤
      x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) / Nat.gcd (2 + 1) (x + 1) :=
    Nat.div_le_div_left hg hgpos
  have h2 : 5 ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
  have h3 : 5 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have hA : 24 * 126 ≤ (x ^ 2 - 1) * (x ^ 3 + 1) := by
    apply Nat.mul_le_mul <;> norm_num at h2 h3 ⊢ <;> omega
  have hN : 125 * (24 * 126) ≤ x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) := by
    apply Nat.mul_le_mul <;> norm_num at h3 ⊢ <;> omega
  have hbig : 25921 ≤ x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) / 3 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by norm_num at hN ⊢; omega)
  omega

theorem card_mem_ambiguous {S : Type} [Group S] [Finite S] (h : catalogIs S (ambiguousChev 2)) :
    Nat.card S = 60 ∨ Nat.card S = 360 ∨ Nat.card S = 20160 ∨ Nat.card S = 168 ∨ Nat.card S = 6048 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | alternating n hn =>
    have hi' : (n = 5 ∧ ((2 : ℕ) = 2 ∨ (2 : ℕ) = 5)) ∨ (n = 6 ∧ ((2 : ℕ) = 2 ∨ (2 : ℕ) = 3)) ∨
        (n = 8 ∧ (2 : ℕ) = 2) := hi
    rcases hi' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · have hS : Nat.card S = 60 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        norm_num [Nat.card_eq_fintype_card, Nat.factorial]
      rw [hS]
      norm_num
    · have hS : Nat.card S = 360 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        norm_num [Nat.card_eq_fintype_card, Nat.factorial]
      rw [hS]
      norm_num
    · have hS : Nat.card S = 20160 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        norm_num [Nat.card_eq_fintype_card, Nat.factorial]
      rw [hS]
      norm_num
  | cyclic _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q =>
      rcases r with _ | _ | r
      · exact hi.elim
      · have hi' : (q.card = 7 ∧ (2 : ℕ) = 2) ∨ (q.card = 8 ∧ (2 : ℕ) = 3) := hi
        have hc : Nat.card S = lieOrderFormula (LieTypeIndex.A (0 + 1) q) :=
          CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A (0 + 1) q, hv⟩ S ⟨e⟩
        rcases hi' with ⟨h7, -⟩ | ⟨-, h3⟩
        · have hS : Nat.card S = 168 := by
            rw [hc]
            show orderA (0 + 1) q.card = 168
            rw [h7]
            norm_num [orderA]
          rw [hS]
          norm_num
        · exact absurd h3 (by norm_num)
      · exact hi.elim
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      ·
        have hi' : q.card = 3 ∧ (2 : ℕ) = 2 := hi
        have hc : Nat.card S = lieOrderFormula (LieTypeIndex.twistedA 2 q) :=
          CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedA 2 q, hv⟩ S ⟨e⟩
        have hS : Nat.card S = 6048 := by
          rw [hc]
          show orderTwistedA 2 q.card = 6048
          rw [hi'.1]
          decide
        rw [hS]
        norm_num
      · exact absurd (show (q.card = 2 ∧ (2 : ℕ) = 3) from hi).2 (by norm_num)
      · exact hi.elim
    | _ => exact hi.elim

end I91T

end CFSG.LocalAnalysis.GLTheoremA
