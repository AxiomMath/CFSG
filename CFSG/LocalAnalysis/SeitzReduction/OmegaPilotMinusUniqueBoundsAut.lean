module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsAut
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.Open (ordD ordTwistedD)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)

section Outer

variable {K : Type} [Field K] [Finite K]

theorem card_outer_coordinateMinus_dvd {n f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (Outer (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) ∣
      2 * f := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have hn1 : 1 ≤ n := by omega
  have h := statedClassicalModel_coordinateMinus hf hK hn hn1 hirr
  have hab := orthogonal_model_isometry_abelianization_order_bound _ .POmegaMinus
    (.inr (.inr rfl)) n 2 f h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c)
    (coordinateMinusWitnessEquiv K hn1 b c (MulEquiv.refl _)).symm
  have hE : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr
  have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.exists_ne_zero_of_nondeg (by omega : 0 < 2 * n)
      (regular_coordinateQuadMinus n K b c hn hirr).1
  have ha := relIndex_inner_dvd (coordinateQuadMinus n K hn1 b c)
  have hA : Nat.card (Abelianization (matrixIsometries (coordinateQuadMinus n K hn1 b c))) ≤ 2 := by
    rw [coordinateQuadMinus, card_abelianization_matrixIsometries_reindex]
    exact hab.2.2 rfl
  have hA0 :=
    Nat.card_pos (α := Abelianization (matrixIsometries (coordinateQuadMinus n K hn1 b c)))
  have hA2 :
      Nat.card (Abelianization (matrixIsometries (coordinateQuadMinus n K hn1 b c))) ∣ 2 := by
    rcases (by omega : Nat.card (Abelianization (matrixIsometries
        (coordinateQuadMinus n K hn1 b c))) = 1 ∨ Nat.card (Abelianization (matrixIsometries
        (coordinateQuadMinus n K hn1 b c))) = 2) with h1 | h1 <;> simp [h1]
  have hb := relIndex_isometryRange_dvd (coordinateQuadMinus n K hn1 b c) hQ
  have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index = 1 := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.card_units, hK]
    apply Nat.coprime_two_right.mpr
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have hc := (relIndex_linearRange_dvd (coordinateQuadMinus n K hn1 b c)).trans
    ((Subgroup.card_subgroup_dvd_card
      (fieldProjection (coordinateQuadMinus n K hn1 b c)).range).trans
        (card_ringAut_and_isCyclic Nat.prime_two K hK).1.dvd)
  rw [hsq, Nat.dvd_one] at hb
  have hidx : (matrixProjectiveImage (coordinateQuadMinus n K hn1 b c)).index = 1 := by
    rw [hE, Subgroup.index_top]
  rw [card_outer_eq, hb, hidx, mul_one, mul_one]
  exact Nat.mul_dvd_mul (ha.trans hA2) hc

theorem card_mulAut_coordinateMinus_dvd {n f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) ∣
      2 * f * ordTwistedD n (2 ^ f) := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  rw [card_mulAut_eq_of_conj_injective (conj_injective_coordinateMinus hn hirr),
    card_coordinateMinus hf hK hn (by omega) hirr, mul_comm (2 * f)]
  exact Nat.mul_dvd_mul_left _ (card_outer_coordinateMinus_dvd hf hK hn hirr)

end Outer

section Arith

theorem coprime_two_pow_pow_sub_one_add_one {f n : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) :
    Nat.Coprime ((2 ^ f) ^ n - 1) ((2 ^ f) ^ n + 1) := by
  have hodd := CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hf hn
  have h1 : 1 ≤ (2 ^ f) ^ n := Nat.one_le_pow _ _ (by positivity)
  have heq : (2 ^ f) ^ n + 1 = 2 + ((2 ^ f) ^ n - 1) := by omega
  rw [heq, Nat.coprime_add_self_right]
  exact Nat.coprime_two_right.mpr hodd

theorem not_ordD_dvd_mul_ordTwistedD {f n : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) :
    ¬ ordD n (2 ^ f) ∣ 4 * f * ordTwistedD n (2 ^ f) := by
  intro h
  rw [ordD_two_pow hf (by omega), ordTwistedD_two_pow hf (by omega)] at h
  set q := 2 ^ f with hq
  set A := q ^ (n * (n - 1)) with hAdef
  set P := ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) with hPdef
  have hA : 0 < A := by positivity
  have hP : 0 < P := Nat.pos_of_ne_zero (prod_two_pow_sub_one_ne_zero hf)
  have h' : q ^ n - 1 ∣ 4 * f * (q ^ n + 1) := by
    have h2 : A * P * (q ^ n - 1) ∣ A * P * (4 * f * (q ^ n + 1)) := by
      have e1 : A * (q ^ n - 1) * P = A * P * (q ^ n - 1) := by ring
      have e2 : 4 * f * (A * (q ^ n + 1) * P) = A * P * (4 * f * (q ^ n + 1)) := by ring
      rw [← e1, ← e2]
      exact h
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos hA hP) h2
  have h'' : q ^ n - 1 ∣ 4 * f :=
    (coprime_two_pow_pow_sub_one_add_one hf (by omega)).dvd_of_dvd_mul_right h'
  have hle : q ^ n - 1 ≤ 4 * f := Nat.le_of_dvd (by omega) h''
  have hfq : f < q := Nat.lt_two_pow_self
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq3 : q ^ 3 ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
  have hcube : 4 * (f + 1) ≤ q ^ 3 := by
    have e : q ^ 3 = q * q * q := by ring
    rw [e]
    nlinarith
  omega

end Arith

end CFSG.SeitzReduction.OmegaPilot
