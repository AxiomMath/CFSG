module

public import CFSG.GH74.SmallRanks.PSL
public import CFSG.LocalAnalysis.ComponentClassification.LieOrderTwoPart
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.KDSp6Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.LinearFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.OmegaModels
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.PosE64
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.QuatCube
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.QuatCubeModels
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.RankOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.SylowA12
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.UnitaryFour
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.GH74.Statements
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.BasicSylow
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

variable {F : Type} [Group F] [Finite F]

theorem false_of_PSL {n p f : ℕ} (hS : ∀ S : Sylow 2 F, ElemFactsIn (S : Subgroup F))
    (h16 : ∀ x : F, orderOf x ≠ 16) (h6 : 6 ≤ twoRank F) (hp2 : p ≠ 2)
    (hN : Nat.card F * lieOrderDivisor .PSL n (p ^ f) = lieOrderNumerator .PSL n (p ^ f))
    (hm : StatedClassicalModel F .PSL n p f) : False := by
  obtain ⟨hp, -, hn2, -⟩ := hm.1
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with
    rfl | rfl | rfl | rfl | hn6
  · have := GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2 hm
    omega
  · have := twoRank_le_of_PSL_odd hp2 (by decide) hm
    omega
  · obtain ⟨h4, h16'⟩ := psl_four_of_two_part hm.1 hp2 hN (factorization_card_two hS)
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    obtain ⟨x, hx⟩ := exists_orderOf_sixteen_PSL_four
      (two_ne_zero_of_card_eq_odd_prime_pow hp hp2 hK) (by rwa [hK]) (by rwa [hK])
    exact h16 (e.symm x) (by rw [MulEquiv.orderOf_eq]; exact hx)
  · have := twoRank_le_four_of_PSL_five hp2 hm
    omega
  · obtain ⟨φ, hφ⟩ := quatCube_PSL hp2 hn6 hm
    exact false_of_quatCube hS φ hφ

theorem false_of_PSU {n p f : ℕ} (hS : ∀ S : Sylow 2 F, ElemFactsIn (S : Subgroup F))
    (h16 : ∀ x : F, orderOf x ≠ 16) (h6 : 6 ≤ twoRank F) (hp2 : p ≠ 2)
    (hN : Nat.card F * lieOrderDivisor .PSU n (p ^ f) = lieOrderNumerator .PSU n (p ^ f))
    (hm : StatedClassicalModel F .PSU n p f) : False := by
  obtain ⟨hp, -, hn3, -⟩ := hm.1
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | hn6
  · have := twoRank_le_of_PSU_odd hp2 (by decide) hm
    omega
  · obtain ⟨h4, h16'⟩ := psu_four_of_two_part hm.1 hp2 hN (factorization_card_two hS)
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    have : Fact p.Prime := ⟨hp⟩
    have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
    have := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
    obtain ⟨x, hx⟩ := exists_orderOf_sixteen_PSU_four hp2 hK h16'
    exact h16 (e.symm x) (by rw [MulEquiv.orderOf_eq]; exact hx)
  · have := twoRank_le_four_of_PSU_five hp2 hm
    omega
  · obtain ⟨φ, hφ⟩ := quatCube_PSU hp2 hn6 hm
    exact false_of_quatCube hS φ hφ

theorem false_of_PSp {n p f : ℕ} (hS : ∀ S : Sylow 2 F, ElemFactsIn (S : Subgroup F))
    (hp2 : p ≠ 2)
    (hN : Nat.card F * lieOrderDivisor .PSp n (p ^ f) = lieOrderNumerator .PSp n (p ^ f))
    (hm : StatedClassicalModel F .PSp n p f) : False := by
  obtain ⟨-, -, hn2, -⟩ := hm.1
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · exact psp_two_two_part_ne hm.1 hp2 hN (factorization_card_two hS)
  · obtain ⟨φ, hφ⟩ := quatCube_PSp hp2 hn3 hm
    exact false_of_quatCube hS φ hφ

theorem false_of_exceptional {t : StatedLieTag} {n p f N : ℕ}
    (ht : t ∈ ({.G2, .F4, .E6, .E7, .E8, .twistedE6, .trialityD4, .twistedG2} :
      Finset StatedLieTag))
    (hadm : StatedLieAdmissible t n p f) (hp2 : p ≠ 2)
    (hN : N * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f))
    (h9 : N.factorization 2 = 9) : False := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact g2_two_part_ne hadm hp2 hN h9
  · exact exceptional_two_part_ne (by simp) hadm hp2 hN h9
  · exact exceptional_two_part_ne (by simp) hadm hp2 hN h9
  · exact exceptional_two_part_ne (by simp) hadm hp2 hN h9
  · exact exceptional_two_part_ne (by simp) hadm hp2 hN h9
  · exact exceptional_two_part_ne (by simp) hadm hp2 hN h9
  · exact trialityD4_two_part_ne hadm hp2 hN h9
  · exact twistedG2_two_part_ne hadm hp2 hN h9

theorem false_of_char_two {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .twistedB2 ∨ t = .twistedF4 ∨ t = .Tits)
    (hadm : StatedLieAdmissible t n p f) (hp2 : p ≠ 2) : False := by
  rcases ht with rfl | rfl | rfl
  · exact hp2 hadm.2.2.2.1
  · exact hp2 hadm.2.2.2.1
  · exact hp2 hadm.2.2.2.1

theorem posE64_of_orthogonal {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (hp2 : p ≠ 2)
    (hm : StatedClassicalModel G t n p f) : PosE64 G := by
  rcases ht with rfl | rfl | rfl
  · exact posE64_POmegaOdd hp2 hm
  · exact posE64_POmegaPlus hp2 hm
  · exact posE64_POmegaMinus hp2 hm

theorem dvd_card_normalizer_of_posE64 (hS : ∀ S : Sylow 2 F, ElemFactsIn (S : Subgroup F))
    (h : PosE64 F) (E : Subgroup F) (hEsq : ∀ x ∈ E, x * x = 1) (hEc : Nat.card E = 2 ^ 6) :
    5 ∣ Nat.card (normalizer (E : Set F)) := by
  obtain ⟨E₀, h0sq, h0c, H, hH, h5⟩ := h
  exact dvd_card_normalizer_of_elem hS E₀ h0sq h0c H hH h5 E hEsq hEc

theorem oddLieA12Sylow_of (hA12 : ∀ S' : Sylow 2 (alternatingGroup (Fin 12)),
    ElemFactsIn (S' : Subgroup (alternatingGroup (Fin 12))))
    (hO : LieOrderFormulasInput) : OddLieA12Sylow := by
  intro F _ _ hF hA E hEsq hEc
  have hS := elemFactsIn_sylow_of_type hA12 hA
  have h16 := orderOf_ne_sixteen hA
  have h6 := six_le_twoRank hEsq hEc
  have h9 := factorization_card_two hS
  obtain ⟨t, n, p, f, -, hp2, hadm, hL⟩ := hF
  have hN := (hO F t n p f hadm hL).2.1
  cases t
  case PSL => exact (false_of_PSL hS h16 h6 hp2 hN (hL.statedClassicalModel (by decide))).elim
  case PSU => exact (false_of_PSU hS h16 h6 hp2 hN (hL.statedClassicalModel (by decide))).elim
  case PSp => exact (false_of_PSp hS hp2 hN (hL.statedClassicalModel (by decide))).elim
  case POmegaOdd =>
    exact dvd_card_normalizer_of_posE64 hS (posE64_of_orthogonal (by simp) hp2
      (hL.statedClassicalModel (by decide))) E hEsq hEc
  case POmegaPlus =>
    exact dvd_card_normalizer_of_posE64 hS (posE64_of_orthogonal (by simp) hp2
      (hL.statedClassicalModel (by decide))) E hEsq hEc
  case POmegaMinus =>
    exact dvd_card_normalizer_of_posE64 hS (posE64_of_orthogonal (by simp) hp2
      (hL.statedClassicalModel (by decide))) E hEsq hEc
  case G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedG2 =>
    exact (false_of_exceptional (by simp) hadm hp2 hN h9).elim
  case twistedB2 | twistedF4 | Tits => exact (false_of_char_two (by simp) hadm hp2).elim

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
