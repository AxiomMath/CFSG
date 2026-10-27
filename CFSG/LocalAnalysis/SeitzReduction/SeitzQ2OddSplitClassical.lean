module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplit
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SymplecticPerfect
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.Assembly.GL83LieDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial)
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus coordinatePlusWitnessEquiv coordinateMinusWitnessEquiv)

section SpinPlus


theorem spinPlus_exists_section_of_coprime {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] [CharP K p] {E : Type} [Group E] [Finite E]
    {π : E →* spinGroup (quadPlus n K)} (hπ : Function.Surjective π) (hcen : π.ker ≤ center E)
    (hC : p.Coprime (Nat.card π.ker)) :
    ∃ σ : spinGroup (quadPlus n K) →* E, ∀ g, π (σ g) = g := by
  have hC' : ¬ p ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hC
  exact (existsUnique_section_of_sl2_lift (D := plusDatum n K hn) (SpinPlus.isCTGroupDatum hn)
    (plusDatum_steinbergExtras hn) (SpinPlus.isParametrization hn)
    (fun i => SpinPlus.rankOne hn i) hπ hcen hC' fun ρ => by
      obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC' ρ
      exact ⟨ρ', fun g => congrArg (· g) hρ'⟩).exists

theorem oddCentralSplit_spinPlus {n : ℕ} (hn : 3 ≤ n) (K : Type) [Field K] [Finite K]
    [CharP K 2] : OddCentralSplit (spinGroup (quadPlus n K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E _ _ π hπ hcen hodd
  exact spinPlus_exists_section_of_coprime hn hπ hcen (Nat.coprime_two_left.2 hodd)

theorem center_spinGroup_quadPlus_eq_bot_of_charTwo {n : ℕ} (hn : 3 ≤ n) (K : Type) [Field K]
    [CharP K 2] : center (spinGroup (quadPlus n K)) = ⊥ := by
  obtain ⟨-, h1, h2⟩ := spinToStatedProj_quadPlus (n := n) (K := K) hn
  rw [← h2, h1]
  exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.comap_statedScalars_quadPlus_eq_bot hn
    CharTwo.two_eq_zero

@[expose] noncomputable def spinPlusEquivStatedProj {n : ℕ} (hn : 3 ≤ n) (K : Type) [Field K]
    [CharP K 2] :
    spinGroup (quadPlus n K) ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) :=
  ((QuotientGroup.quotientMulEquivOfEq (center_spinGroup_quadPlus_eq_bot_of_charTwo hn K)).trans
    QuotientGroup.quotientBot).symm.trans (spinQuotientCenterEquivQuadPlus (K := K) hn)

theorem oddSchurTrivial_statedProj_omegaPlus {n : ℕ} (hn : 3 ≤ n) (K : Type) [Field K]
    [Finite K] [CharP K 2] : OddSchurTrivial (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
  (oddSchurTrivial_of_oddCentralSplit (oddCentralSplit_spinPlus hn K)).of_mulEquiv
    (spinPlusEquivStatedProj hn K)

end SpinPlus

section SpinMinus


theorem oddCentralSplit_spinMinus {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OddCentralSplit (spinGroup (quadMinus n K b c)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E _ _ π hπ hcen hodd
  exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_coprime
    hirr hn hπ hcen (Nat.coprime_two_left.2 hodd)

@[expose] noncomputable def spinMinusEquivStatedProj {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    spinGroup (quadMinus n K b c) ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) :=
  ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn hirr)).trans
    QuotientGroup.quotientBot).symm.trans (spinQuotientCenterEquivQuadMinus hn hirr)

theorem oddSchurTrivial_statedProj_omegaMinus {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OddSchurTrivial (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
  (oddSchurTrivial_of_oddCentralSplit (oddCentralSplit_spinMinus hn hirr)).of_mulEquiv
    (spinMinusEquivStatedProj hn hirr)

end SpinMinus

section Symplectic


theorem oddCentralSplit_statedSp (r : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    OddCentralSplit (StatedSp r K) := by
  intro E _ _ π hπ hcen hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : ¬ 2 ∣ Nat.card π.ker := fun h2 =>
    (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have hlift : ∀ ρ : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp r K,
      ∃ ρ' : Matrix.SpecialLinearGroup (Fin 2) K →* E, ∀ g, π (ρ' g) = ρ g := by
    intro ρ
    obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift (k := K) hπ hcen hC ρ
    exact ⟨ρ', fun g => congrArg (· g) hρ'⟩
  obtain ⟨σ, hσ, -⟩ :=
    CFSG.LieType.Steinberg.sp_existsUnique_section_of_sl2_lift r (p := 2) hπ hcen hC hlift
  exact ⟨σ, hσ⟩

theorem oddSchurTrivial_statedProj_statedSp (r : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    OddSchurTrivial (StatedProj (StatedSp r K)) := by
  refine oddSchurTrivial_quotient_of_isPGroup (oddCentralSplit_statedSp r K) ?_
  have hle := card_statedScalars_subgroupOf_statedSp_le_two r K
  have hpos : 0 < Nat.card ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)) :=
    Nat.card_pos
  rcases (show Nat.card ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)) = 1 ∨
      Nat.card ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K)) = 2 by omega)
    with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [h, pow_one])

end Symplectic

section PerpLevi


theorem oddSchurTrivial_perpLevi_E7_of_charTwo (K : Type) [Field K] [Finite K] [CharP K 2] :
    OddSchurTrivial (EPilot.perpLevi .E7 K) :=
  (oddSchurTrivial_of_oddCentralSplit
    (oddCentralSplit_spinPlus E7Pilot.three_le_rank_D6 K)).of_mulEquiv
    (E7Pilot.spinEquivPerpLevi K)

end PerpLevi

section LieModel


theorem oddSchurTrivial_of_lieModel_POmegaPlus {X : Type} [Group X] {n f : ℕ}
    (hX : LieModel X .POmegaPlus n 2 f) : OddSchurTrivial X := by
  rcases hX with ⟨-, hst⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hst
    have := charTwo_of_natCard_eq_two_pow hK
    exact (oddSchurTrivial_statedProj_omegaPlus (by omega) K).of_mulEquiv e.symm
  · simp [chevalleyExceptionalTags] at ht
  · simp [reeTitsTags] at ht
  · cases ht

theorem oddSchurTrivial_of_lieModel_POmegaMinus {X : Type} [Group X] {n f : ℕ}
    (hX : LieModel X .POmegaMinus n 2 f) : OddSchurTrivial X := by
  rcases hX with ⟨-, hst⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hst
    have := charTwo_of_natCard_eq_two_pow hK
    exact (oddSchurTrivial_statedProj_omegaMinus hn hirr).of_mulEquiv e.symm
  · simp [chevalleyExceptionalTags] at ht
  · simp [reeTitsTags] at ht
  · cases ht

theorem oddSchurTrivial_of_lieModel_PSp {X : Type} [Group X] {n f : ℕ}
    (hX : LieModel X .PSp n 2 f) : OddSchurTrivial X := by
  rcases hX with ⟨-, hst⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hst
    have := charTwo_of_natCard_eq_two_pow hK
    exact (oddSchurTrivial_statedProj_statedSp n K).of_mulEquiv e.symm
  · simp [chevalleyExceptionalTags] at ht
  · simp [reeTitsTags] at ht
  · cases ht

theorem oddSchurTrivial_matrixProjectiveDerived_plus {n : ℕ} (hn : 3 ≤ n) (K : Type) [Field K]
    [Finite K] [CharP K 2] :
    OddSchurTrivial (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  (oddSchurTrivial_statedProj_omegaPlus hn K).of_mulEquiv
    (coordinatePlusWitnessEquiv K (MulEquiv.refl _))

theorem oddSchurTrivial_matrixProjectiveDerived_minus {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OddSchurTrivial (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) :=
  (oddSchurTrivial_statedProj_omegaMinus hn hirr).of_mulEquiv
    (coordinateMinusWitnessEquiv K (by omega) b c (MulEquiv.refl _))

end LieModel

end CFSG.SeitzReduction.SeitzQ2
