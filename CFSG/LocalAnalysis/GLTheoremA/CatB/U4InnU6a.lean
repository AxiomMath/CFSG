module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnLift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnRed
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.F48.Core
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.CTP.SpEven
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate7233Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Fischer CFSG.StandardType CFSG.Assembly
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] noncomputable def covM6 : M6 →* S6 :=
  QuotientGroup.mk' ((StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4))

theorem covM6_surjective : Function.Surjective covM6 := QuotientGroup.mk'_surjective _

theorem covM6_ker_le_center : covM6.ker ≤ Subgroup.center M6 := by
  intro z hz
  rw [covM6, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : GL (Fin 6) F4) * z = z * g
  rw [← hc]
  exact (commute_scalar c (g : GL (Fin 6) F4)).eq

theorem F4unit_pow_three (c : F4ˣ) : c ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact F4unit_cube c)

theorem covM6_ker_cube : ∀ z ∈ covM6.ker, z ^ 3 = 1 := by
  intro z hz
  rw [covM6, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  apply Subtype.ext
  show (z : GL (Fin 6) F4) ^ 3 = 1
  rw [← hc, ← map_pow, F4unit_pow_three, map_one]

theorem u4Fix_conjM6 (A : primeFormUnitary hF4 (idGram F4 6)) :
    u4Fix (conjM6 A) = CenD (A : GL (Fin 6) F4) := by
  rw [← fixSubgroup_conjM6]
  ext x
  exact Iff.rfl

@[expose] def M6Main : Prop :=
  ∀ B : primeFormUnitary hF4 (idGram F4 6),
    (∃ c : F4ˣ, (B : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) →
    (¬ ∃ c : F4ˣ, (B : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c) →
    (∃ L : Subgroup M6, L ≤ CenD (B : GL (Fin 6) F4) ∧ Group.IsPerfect ↥L ∧ 25920 ∣ Nat.card L) →
    CFSG.pPrimeCore 3 ↥(CenD (B : GL (Fin 6) F4)) = ⊥

theorem u4InnModel_S6_of (h : M6Main) : U4InnModel S6 := by
  intro hS β hβ3 hq
  obtain ⟨B, hB, ⟨c, hBc⟩, hβB⟩ := exists_unitary_of_pow_three β hβ3
  show CFSG.pPrimeCore 3 ↥(u4Fix β) = ⊥
  by_cases hsc : ∃ c : F4ˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 6) c
  · obtain ⟨c₀, hc₀⟩ := hsc
    have hβ1 : β = 1 := by
      ext x
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      rw [MulAut.one_apply]
      refine hβB u u ?_
      rw [hc₀, ← (commute_scalar c₀ (u : GL (Fin 6) F4)).eq, mul_inv_cancel_right]
    subst hβ1
    have h3 : 3 ∣ Nat.card S6 := by
      have h25 := hq.dvd_card
      rw [u4Fix_one, Subgroup.card_top] at h25
      exact (show 3 ∣ 25920 by norm_num).trans h25
    exact pPrimeCore_u4Fix_one h3
  · have hαβ : ∀ k, covM6 (conjM6 ⟨B, hB⟩ k) = β (covM6 k) :=
      fun k => (hβB k (conjM6 ⟨B, hB⟩ k) rfl).symm
    obtain ⟨L, hL, hperf, hdvd⟩ := exists_perfect_of_central_cover covM6_surjective
      covM6_ker_le_center hαβ hq
    rw [u4Fix_conjM6] at hL
    have hcen := h ⟨B, hB⟩ ⟨c, hBc⟩ hsc ⟨L, hL, hperf, hdvd⟩
    refine pPrimeCore_fix_of_central_cover covM6_surjective covM6_ker_le_center covM6_ker_cube hαβ ?_
    rw [u4Fix_conjM6]
    exact hcen

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
