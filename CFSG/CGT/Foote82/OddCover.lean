module

public import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.Alternating.Multipliers.OddKernel
import CFSG.LieType.Multipliers.U42
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.CGT.Foote82

open CFSG.RankThree.PartTwo

theorem ker_eq_bot_of_odd_alt {P : Type*} [Group P] [Finite P] (hP : commutator P = ⊤) {N : ℕ}
    (hN : 8 ≤ N) (η : P →* alternatingGroup (Fin N)) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hodd : Odd (Nat.card η.ker)) : η.ker = ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  haveI : Group.IsPerfect P := Group.isPerfect_def.2 hP
  exact Subgroup.eq_bot_of_card_eq _
    (CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) η hη hK hodd)

open CFSG.Open in
theorem blueprintLieModel_omegaMinusTwo :
    CFSG.Blueprint.LieModel ↥(omegaMinusTwo 2) .PSU 4 2 1 := by
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨E, _, h, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      hK hirr
  obtain ⟨hsimple, -, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 3) (Or.inr rfl) hirr
  have : Finite E := h.finite
  have hE : Nat.card E = (2 ^ 1) ^ 2 := by rw [h.card_eq_sq]
  have hsimpleT : IsSimpleGroup (StatedSU 4 (2 ^ 1) E) := by
    have := hsimple
    exact eSU.symm.isSimpleGroup
  have hnaT : ¬ ∀ x y : StatedSU 4 (2 ^ 1) E, x * y = y * x := fun hc =>
    hna fun x y => eSU.injective (by rw [map_mul, map_mul, hc])
  have hcenter : Subgroup.center (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    have := hsimpleT
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedSU 4 (2 ^ 1) E)) with h0 | h1
    · exact h0
    · exact absurd (fun x y => (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top y)) x) hnaT
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hscal : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    rw [← (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := 1) hE (by norm_num) hnq).2, hcenter]
  have ht : CFSG.Assembly.LowTwoRank.StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags := by
    decide
  exact .inl ⟨ht, ⟨Nat.prime_two, le_rfl, by norm_num, hnq⟩, E, inferInstance, h.finite, hE,
    ⟨(MulEquiv.refl _ : ↥(omegaMinusTwo 2) ≃* ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1))).trans
      (eSU.trans (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hscal.symm)))⟩⟩

theorem ker_eq_bot_of_odd_omegaMinus_of_card_dvd
    (hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier ↥(omegaMinusTwo 2)) ∣ 2)
    {P : Type*} [Group P] [Finite P] (hP : commutator P = ⊤)
    (η : P →* ↥(omegaMinusTwo 2)) (hη : Function.Surjective η) (hK : η.ker ≤ Subgroup.center P)
    (hodd : Odd (Nat.card η.ker)) : η.ker = ⊥ := by
  haveI : Group.IsPerfect P := Group.isPerfect_def.2 hP
  have hdvd : Nat.card η.ker ∣ 2 :=
    (Subgroup.card_dvd_of_surjective
      (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective η hη hK)).trans hM
  have hle : Nat.card η.ker ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk⟩ := hodd
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

section Minus

theorem card_hopfMultiplier_omegaMinusTwo :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier ↥(omegaMinusTwo 2)) = 2 := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two _
    blueprintLieModel_omegaMinusTwo
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : _ ≃ ZMod 2), Nat.card_zmod]

end Minus

end CFSG.CGT.Foote82
