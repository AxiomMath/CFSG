module

public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.ClassicalInvolution.Phan.Standard
public import CFSG.ClassicalInvolution.Phan.StandardPair
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LinearAlgebra.DesarguesianPlanes.SteinbergRecognition

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

theorem linear_eq_sup {K X : Type} [Field K] [Group X] {W U V : Subgroup X}
    (h : WeakCT.LinearBlockStandardPair K W U V) : W = U ⊔ V := by
  obtain ⟨θ, hrange, -, hU, hV⟩ := WeakCT.pair_normalize h
  rw [← hU, ← hV, ← Subgroup.map_sup, WeakCT.B12_sup_B23, ← MonoidHom.range_eq_map, hrange]

theorem unitary_eq_sup {K X : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    [Group X] (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f ≠ 2) {W U V : Subgroup X}
    (h : Phan.UnitaryBlockStandardPair K p f W U V) : W = U ⊔ V := by
  obtain ⟨θ, hrange, -, hU, hV⟩ := Phan.pair_normalize h
  rw [← hU, ← hV, ← Subgroup.map_sup, Phan.B12_sup_B23 hK hq, ← MonoidHom.range_eq_map, hrange]

theorem card_Su_three {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (Phan.Su K p f 3) = (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  obtain ⟨P₃, hP₃⟩ := exists_wittMatrix hK 3
  rw [← Nat.card_congr (conjEquiv P₃ hP₃).toEquiv, card_SU_three hK]

theorem card_SL_three {K : Type} [Field K] [Finite K] :
    Nat.card SL(3, K) = Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  rw [LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]

theorem card_eq_range_mul_ker {G X : Type} [Group G] [Group X] (θ : G →* X) :
    Nat.card G = Nat.card θ.range * Nat.card θ.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv]

theorem not_linear_and_unitary {K K' X : Type} [Field K] [Finite K] [Field K'] [Finite K']
    {p f : ℕ} [Fact p.Prime] [CharP K' p] [Group X] (hK : Nat.card K = p ^ f)
    (hK' : Nat.card K' = (p ^ f) ^ 2) (hodd : Odd (Nat.card K)) {W U V : Subgroup X}
    (hl : WeakCT.LinearBlockStandardPair K W U V) (hu : Phan.UnitaryBlockStandardPair K' p f W U V) :
    False := by
  obtain ⟨θ, -, hrange, hker, -⟩ := hl
  obtain ⟨θ', -, hrange', hker', -⟩ := hu
  have hq3 : 3 ≤ p ^ f := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1 hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  have hNl : Nat.card SL(3, K) = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) := by
    rw [card_SL_three, hK]
  have hNu := card_Su_three (K := K') (p := p) (f := f) hK'
  have e1 := card_eq_range_mul_ker θ
  have e2 := card_eq_range_mul_ker θ'
  rw [hrange] at e1
  rw [hrange'] at e2
  rw [hNl] at e1
  rw [hNu] at e2
  have ha : Nat.card θ.ker ≤ 3 :=
    (Subgroup.card_le_of_le hker).trans DesarguesianPlanes.card_center_SL3_le
  have ha0 : 0 < Nat.card θ.ker := Nat.card_pos
  have hfinW : Finite ↥W := by
    rw [← hrange]
    exact Finite.of_surjective _ θ.rangeRestrict_surjective
  have hw0 : 0 < Nat.card ↥W := Nat.card_pos
  set q := p ^ f with hqdef
  have hq27 : 27 ≤ q ^ 3 :=
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
  have hY2 : q ^ 3 + 1 = (q ^ 3 - 1) + 2 := by omega
  rw [← mul_assoc] at e1
  rw [hY2] at e2
  have hY26 : 26 ≤ q ^ 3 - 1 := by omega
  generalize q ^ 3 * (q ^ 2 - 1) = A at e1 e2
  generalize q ^ 3 - 1 = Y at e1 e2 hY26
  generalize Nat.card ↥W = w at e1 e2 hw0
  generalize Nat.card θ.ker = a at e1 ha ha0
  generalize Nat.card θ'.ker = b at e2
  have h3 : w * (a * (Y + 2)) = w * (b * Y) := by
    calc w * (a * (Y + 2)) = (w * a) * (Y + 2) := by ring
      _ = (A * Y) * (Y + 2) := by rw [e1]
      _ = (A * (Y + 2)) * Y := by ring
      _ = (w * b) * Y := by rw [e2]
      _ = w * (b * Y) := by ring
  have key : a * (Y + 2) = b * Y := Nat.eq_of_mul_eq_mul_left hw0 h3
  by_cases hba : b ≤ a
  · have : b * Y ≤ a * Y := Nat.mul_le_mul_right Y hba
    nlinarith
  · have hba' : a + 1 ≤ b := not_le.mp hba
    have : (a + 1) * Y ≤ b * Y := Nat.mul_le_mul_right Y hba'
    nlinarith

end CFSG.ClassicalInvolution.RouteD.Gaps
