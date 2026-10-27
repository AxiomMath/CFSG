module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.PSLTwo
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.PSLThree
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.PSUThree
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.TFA
public import CFSG.LieType.Simplicity.Classical
public import CFSG.RankThree.PartOne.FOC.PSUModel
import CFSG.Models.Blueprint

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.Models CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

theorem center_eq_bot_of_simple_witness {X : Type} [Group X] [IsSimpleGroup X]
    (hw : ThreeTwoWitness X) : Subgroup.center X = ⊥ := by
  rcases (Subgroup.center X).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨P, hP, hP2, x, hx, hxN⟩ := hw
    have hPn : P.Normal := by
      constructor
      intro n hn g
      have : g ∈ Subgroup.center X := by rw [h]; trivial
      rw [Subgroup.mem_center_iff] at this
      rw [← this n, mul_inv_cancel_right]
      exact hn
    rcases hPn.eq_bot_or_eq_top with h1 | h1
    · exact hP h1
    · have hxP : x ∈ P := by rw [h1]; trivial
      obtain ⟨k, hk⟩ := hP2 ⟨x, hxP⟩
      have h2 : x ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
      rw [hx] at this
      have h3 : 3 ∣ 2 ^ k := this
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
      omega

theorem statedClassicalModel_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus) (hm : LieModel X t n p f) : StatedClassicalModel X t n p f :=
  CFSG.Models.LieModel.statedClassicalModel hm
    (by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem exists_equiv_projectiveSL {X : Type} [Group X] {n p f : ℕ}
    (hC : StatedClassicalModel X .PSL n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (X ≃* LinearFlag.projectiveSL n K) := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := hC
  exact ⟨K, hK, hfin, hcard, ⟨(e.trans
    (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)⟩⟩

@[expose] def RankOneParams (t : StatedLieTag) (n p f : ℕ) : Prop :=
  (t = .PSL ∧ n = 2) ∨ (t = .PSL ∧ n = 3 ∧ p ^ f % 3 = 2) ∨ (t = .PSU ∧ n = 3 ∧ p ^ f % 3 = 1)

theorem outerFixedWitness_of_params {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {n p f : ℕ} (hm : LieModel X t n p f) (hP : RankOneParams t n p f)
    (hw : ThreeTwoWitness X) : OuterFixedWitness X ∧ Subgroup.center X = ⊥ := by
  rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl, hq⟩ | ⟨rfl, rfl, hq⟩
  · have hC := statedClassicalModel_of_lieModel (Or.inl rfl) hm
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := exists_equiv_projectiveSL hC
    have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p f hC).2
    exact ⟨outerFixedWitness_psl_two e hw, center_eq_bot_of_simple_witness hw⟩
  · have hC := statedClassicalModel_of_lieModel (Or.inl rfl) hm
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL hC
    have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 p f hC).2
    exact ⟨outerFixedWitness_psl_three (by rw [hK]; exact hq) e,
      center_eq_bot_of_simple_witness hw⟩
  · have hC := statedClassicalModel_of_lieModel (Or.inr (Or.inl rfl)) hm
    obtain ⟨K, _, _, h, -, -, ⟨e⟩⟩ := CFSG.RankThree.PartOne.FOC.exists_psu_model hC
    have hs := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 p f hC).2
    exact ⟨outerFixedWitness_psu_three h hq e, center_eq_bot_of_simple_witness hw⟩

@[expose] def LieRankOneClassification : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n p f : ℕ), LieModel X t n p f →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 → RankOneParams t n p f

theorem tfaaModels_of_classification (hC : LieRankOneClassification) : TFAaModels := by
  intro X _ _ t n p f hm h1 hw H hH hc
  have hW : ThreeTwoWitness X := (one_le_glaTwoLocalRank_iff).1 (by omega)
  obtain ⟨hO, hZ⟩ := outerFixedWitness_of_params hm (hC X t n p f hm h1) hW
  exact fieldBonus_of_outerFixedWitness hZ h1 hw hO H hH hc

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
