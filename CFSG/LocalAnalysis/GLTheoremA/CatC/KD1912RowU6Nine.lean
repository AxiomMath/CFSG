module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912RowU6Core
public import CFSG.GroupTheory.PCore.SelfCentralizing

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.Fischer
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def U6TwoNineSpecial : Prop :=
  ∀ (B : GL (Fin 6) F4) (c : F4ˣ), B ∈ primeFormUnitary hF4 (idGram F4 6) → c ≠ 1 →
    B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c →
    ∃ T : Subgroup (CenD B), T.Normal ∧ IsSimpleGroup ↥T ∧ 3 ∣ Nat.card ↥T ∧
      ∀ x : ↥(CenD B), x ^ 9 ∈ T

theorem u6TwoNineCore_of_special (h : U6TwoNineSpecial) : U6TwoNineCore := by
  intro B c hB hc1 hBc
  obtain ⟨T, hTn, hT, h3T, hpow⟩ := h B c hB hc1 hBc
  have hbot : GLAPPrimeCoreOf 3 (⊤ : Subgroup ↥(CenD B)) = ⊥ := by
    refine CFSG.gLAPPrimeCoreOf_eq_bot_of_normal_simple_of_pow_mem Nat.prime_three le_top ?_
      hT h3T ?_
    · exact hTn.comap _
    · intro x _
      exact ⟨2, by simpa using hpow x⟩
  have htop : pPrimeCore 3 ↥(⊤ : Subgroup ↥(CenD B)) = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mp hbot
  exact pPrimeCore_eq_bot_of_mulEquiv 3 Subgroup.topEquiv htop

end CFSG.LocalAnalysis.GLTheoremA.KD1912
