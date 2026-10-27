module

public import CFSG.Blueprint.Catalog
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint

variable {X : Type} [Group X] {n : ℕ}

theorem suzukiModel_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) :
    SuzukiModel X 2 n :=
  (CFSG.Blueprint.LieModel.suzukiModel h).2

theorem exists_eq_two_mul_add_one_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 := by
  obtain ⟨-, a, ha, -, -, -, hn, -⟩ := suzukiModel_of_lieModel_twistedB2 h
  exact ⟨a, ha, hn⟩

theorem odd_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) : Odd n := by
  obtain ⟨a, -, rfl⟩ := exists_eq_two_mul_add_one_of_lieModel_twistedB2 h
  exact ⟨a, rfl⟩

theorem three_le_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) : 3 ≤ n := by
  obtain ⟨a, ha, rfl⟩ := exists_eq_two_mul_add_one_of_lieModel_twistedB2 h
  omega

theorem finite_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) : Finite X := by
  obtain ⟨-, a, -, K, _, _, -, -, ⟨e⟩⟩ := suzukiModel_of_lieModel_twistedB2 h
  exact Finite.of_equiv _ e.symm.toEquiv

theorem exists_mulEquiv_sz_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ Nonempty (X ≃* CFSG.Open.Sz a) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := suzukiModel_of_lieModel_twistedB2 h
  exact ⟨a, ha, rfl, ⟨e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))⟩⟩

private theorem exists_mulEquiv_suzukiMatrixGroup_of_lieModel_twistedB2
    (h : LieModel X .twistedB2 0 2 n) : ∃ a : ℕ, 1 ≤ a ∧
      Nonempty (X ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) := by
  obtain ⟨a, ha, -, ⟨e⟩⟩ := exists_mulEquiv_sz_of_lieModel_twistedB2 h
  have hmodel : CFSG.Theory.Comparator.SzModel a = CFSG.Open.Sz a := CFSG.Models.benderSzModel_eq_sz a
  exact ⟨a, ha, ⟨e.trans (MulEquiv.subgroupCongr
    (hmodel.symm.trans (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a)))⟩⟩

theorem isSimpleGroup_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) :
    IsSimpleGroup X := by
  obtain ⟨a, ha, ⟨e⟩⟩ := exists_mulEquiv_suzukiMatrixGroup_of_lieModel_twistedB2 h
  have := (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 a (by omega)).1
  exact e.isSimpleGroup

theorem not_three_dvd_card_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨a, ha, ⟨e⟩⟩ := exists_mulEquiv_suzukiMatrixGroup_of_lieModel_twistedB2 h
  rw [Nat.card_congr e.toEquiv]
  exact (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 a (by omega)).2

theorem fusionBenderBorel_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) :
    CFSG.Open.fusionBenderBorel X (2 ^ n) 2 := by
  have := finite_of_lieModel_twistedB2 h
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ := exists_mulEquiv_sz_of_lieModel_twistedB2 h
  have : Finite (CFSG.Open.Sz a) := Finite.of_equiv X e.toEquiv
  exact (CFSG.Open.bender_suzuki_borel_full a ha).map_mulEquiv e.symm

theorem exists_four_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) :
    ∃ E : Subgroup X, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  have := finite_of_lieModel_twistedB2 h
  exact exists_four_of_fusionBenderBorel (fusionBenderBorel_of_lieModel_twistedB2 h)
    (pow_dvd_pow 2 (by have := three_le_of_lieModel_twistedB2 h; omega) : 2 ^ 2 ∣ 2 ^ n)

theorem exists_mul_ne_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) :
    ∃ a b : X, a * b ≠ b * a := by
  have := isSimpleGroup_of_lieModel_twistedB2 h
  obtain ⟨E, -, hE4⟩ := exists_four_of_lieModel_twistedB2 h
  exact exists_mul_ne_of_four_dvd_card (hE4 ▸ Subgroup.card_subgroup_dvd_card E)

theorem factorization_two_card_of_lieModel_twistedB2 (h : LieModel X .twistedB2 0 2 n) :
    (Nat.card X).factorization 2 = 2 * n := by
  have := finite_of_lieModel_twistedB2 h
  rw [factorization_two_card_of_fusionBenderBorel (fusionBenderBorel_of_lieModel_twistedB2 h),
    mul_comm]

theorem card_of_lieModel_twistedB2
    (h : LieModel X .twistedB2 0 2 n) :
    Nat.card X = (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) := by
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := suzukiModel_of_lieModel_twistedB2 h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  exact Nat.mul_right_comm _ _ _

theorem card_eq_ordSuzuki_of_lieModel_twistedB2
    (h : LieModel X .twistedB2 0 2 n) : Nat.card X = CFSG.Open.ordSuzuki (2 ^ n) :=
  card_of_lieModel_twistedB2 h

theorem odd_card_outer_of_lieModel_twistedB2
    (h : LieModel X .twistedB2 0 2 n) :
    Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := suzukiModel_of_lieModel_twistedB2 h
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact CFSG.ProperTwoGeneratedCore.HighRankPair.odd_card_outer_suzukiGroup ha hK

end CFSG.LocalAnalysis.EvenBN.GMSK
