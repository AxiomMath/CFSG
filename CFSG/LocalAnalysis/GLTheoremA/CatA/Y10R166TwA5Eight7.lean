module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight4
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace TwA5Eight

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)

theorem twA5Bar_le_sup :
    (twA5Hom h).range.map (unitaryProj h 6) ≤
      blockSU h suFiveIndex ⊔ Subgroup.zpowers (twA5X h) := by
  rintro _ ⟨X0, hX0, rfl⟩
  obtain ⟨X, rfl⟩ := MonoidHom.mem_range.1 hX0
  obtain ⟨n, hn⟩ := mem_zpowers_lambda_nat (a := X.1.1) (by
    rw [zpowers_lambda_eq_roots h]
    exact (mem_rootsOfUnity (M := F) 9 X.1.1).mpr (mem_twA5Param.mp X.2).1)
  let z : Fˣ := X.1.2.1 * X.1.2.2.1 * X.1.2.2.2
  have hz3 : z ^ 3 = 1 := by
    simp only [z, mul_pow]
    rw [(mem_twA5Param.mp X.2).2.1, (mem_twA5Param.mp X.2).2.2.1,
      (mem_twA5Param.mp X.2).2.2.2]
    simp
  let zU : rootsOfUnity 3 F := ⟨z, (mem_rootsOfUnity (M := F) 3 z).mpr hz3⟩
  let Jp : twA5Param (F := F) :=
    ⟨(z, X.1.2.1, X.1.2.2.1, X.1.2.2.2), by
      rw [mem_twA5Param]
      refine ⟨?_, (mem_twA5Param.mp X.2).2.1, (mem_twA5Param.mp X.2).2.2.1,
        (mem_twA5Param.mp X.2).2.2.2⟩
      rw [show z ^ 9 = (z ^ 3) ^ 3 by
        rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul], hz3, one_pow]⟩
  have hXeq : X = twA5ScalarParam (F := F) zU⁻¹ * Jp * twA5XParam (F := F) ^ n := by
    apply Subtype.ext
    ext <;> simp [twA5ScalarParam, Jp, twA5XParam, z, hn]
    · have hzU : ((zU : Fˣ) : F) = (z : F) := by simp [zU]
      rw [hzU]
      rw [show (z : F) = (X.1.2.1 : F) * (X.1.2.2.1 : F) * (X.1.2.2.2 : F) by simp [z]]
      field_simp
    all_goals simp [mul_assoc]
  have hJ : unitaryProj h 6 (twA5Hom h Jp) ∈ blockSU h suFiveIndex := by
    apply unitaryProj_mem_blockSU
    rw [twA5Hom_apply]
    unfold twA5Diag
    apply diagSU_mem_unitaryBlock
    intro k hk
    simp only [suFiveIndex, Finset.mem_erase, Finset.mem_univ, and_true, not_not] at hk
    subst hk
    change twA5Entries (F := F) z X.1.2.1 X.1.2.2.1 X.1.2.2.2 5 = 1
    rw [twA5Entries_five]
    have hz6 : z ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hz3, one_pow]
    have hz6 : z ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hz3, one_pow]
    rw [show z ^ 5 * X.1.2.1 * X.1.2.2.1 * X.1.2.2.2 = z ^ 6 by
      simp only [z]
      rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_add, pow_one]
      group]
    rw [hz6]
    simp
  have hZ : unitaryProj h 6 (twA5Hom h (twA5ScalarParam (F := F) zU⁻¹)) = 1 := by
    exact MonoidHom.mem_ker.mp (by
      rw [ker_unitaryProj]
      exact twA5Hom_scalarParam_mem h zU⁻¹)
  have hX : unitaryProj h 6 (twA5Hom h (twA5XParam (F := F))) = twA5X h := rfl
  have hcalc : unitaryProj h 6 (twA5Hom h X) =
      unitaryProj h 6 (twA5Hom h Jp) * (twA5X h) ^ n := by
    calc
      unitaryProj h 6 (twA5Hom h X)
          = unitaryProj h 6 (twA5Hom h
              (twA5ScalarParam (F := F) zU⁻¹ * Jp * twA5XParam (F := F) ^ n)) := by rw [hXeq]
      _ = unitaryProj h 6 (twA5Hom h (twA5ScalarParam (F := F) zU⁻¹)) *
            unitaryProj h 6 (twA5Hom h Jp) *
              (unitaryProj h 6 (twA5Hom h (twA5XParam (F := F)))) ^ n := by
        simp only [map_mul, map_pow]
      _ = unitaryProj h 6 (twA5Hom h Jp) * (twA5X h) ^ n := by rw [hZ, hX]; simp
  rw [hcalc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hJ)
    (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) n))

end TwA5Eight

end CFSG.LocalAnalysis.GLTheoremA.Y10F
