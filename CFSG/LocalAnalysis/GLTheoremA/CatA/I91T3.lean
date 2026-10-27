module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.HardMathSupport.Solomon.Coordinator


theorem prod_twistedA5 (x : ℕ) :
    (∏ i ∈ Finset.Icc 2 (5 + 1), (if Even i then x ^ i - 1 else x ^ i + 1)) =
      (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) * (x ^ 5 + 1) * (x ^ 6 - 1) := by
  rw [show Finset.Icc 2 (5 + 1) = {2, 3, 4, 5, 6} from by decide]
  simp [Finset.prod_insert, Nat.even_iff]
  ring

theorem orderTwistedA_five_gt {x : ℕ} (hx : 2 ≤ x) : 35942400 < orderTwistedA 5 x := by
  unfold orderTwistedA
  rw [show 5 * (5 + 1) / 2 = 15 from rfl, prod_twistedA5]
  have h2 : 2 ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
  have h3 : 2 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have h4 : 2 ^ 4 ≤ x ^ 4 := Nat.pow_le_pow_left hx 4
  have h5 : 2 ^ 5 ≤ x ^ 5 := Nat.pow_le_pow_left hx 5
  have h6 : 2 ^ 6 ≤ x ^ 6 := Nat.pow_le_pow_left hx 6
  have h15 : 2 ^ 15 ≤ x ^ 15 := Nat.pow_le_pow_left hx 15
  have f2 : 3 ≤ x ^ 2 - 1 := by norm_num at h2; omega
  have f3 : 9 ≤ x ^ 3 + 1 := by norm_num at h3; omega
  have f4 : 15 ≤ x ^ 4 - 1 := by norm_num at h4; omega
  have f5 : 33 ≤ x ^ 5 + 1 := by norm_num at h5; omega
  have f6 : 63 ≤ x ^ 6 - 1 := by norm_num at h6; omega
  have hP : 3 * 9 * 15 * 33 * 63 ≤ (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) * (x ^ 5 + 1) * (x ^ 6 - 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul f2 f3) f4) f5) f6
  have hN : 2 ^ 15 * (3 * 9 * 15 * 33 * 63) ≤ x ^ 15 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) * (x ^ 5 + 1) * (x ^ 6 - 1)) :=
    Nat.mul_le_mul h15 hP
  have hg : Nat.gcd (5 + 1) (x + 1) ≤ 6 := (Nat.gcd_le_left _ (by norm_num))
  have hgpos : 0 < Nat.gcd (5 + 1) (x + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdiv : x ^ 15 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) * (x ^ 5 + 1) * (x ^ 6 - 1)) / 6 ≤
      x ^ 15 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) * (x ^ 5 + 1) * (x ^ 6 - 1)) /
        Nat.gcd (5 + 1) (x + 1) :=
    Nat.div_le_div_left hg hgpos
  have hbig : 35942401 ≤ x ^ 15 * ((x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) * (x ^ 5 + 1) * (x ^ 6 - 1)) / 6 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by norm_num at hN ⊢; omega)
  omega

theorem u6CardLarge_holds : U6CardLarge := by
  intro S _ _ k hk hc
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex hc
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    all_goals first | exact hP.elim | skip
    · have hcard : Nat.card S = I1420.lieOrderFormula (LieTypeIndex.twistedA 5 q) :=
        lieOrderBridge_holds ⟨.twistedA 5 q, hv⟩ S ⟨e⟩
      have hqc : q.card = 2 ^ k := by
        rw [PrimePower.card_def, hP.1, hP.2]
      have hx : 2 ≤ q.card := by
        rw [hqc]
        exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
      have := orderTwistedA_five_gt hx
      rw [hcard]
      exact this
  | _ => exact hP.elim

end I91T

end CFSG.LocalAnalysis.GLTheoremA
