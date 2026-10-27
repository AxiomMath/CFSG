module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporClsSpec
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67RedAut
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Fam
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Cls67

open Subgroup

theorem triples_false_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ (r s : ℕ) (a b y : H), r.Prime → s.Prime → Odd r → Odd s → r ≠ s → a ^ r = 1 →
      b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 → a * b = b * a →
        a * y = y * a → b * y = y * b → False) :
    ∀ (r s : ℕ) (a b y : G), r.Prime → s.Prime → Odd r → Odd s → r ≠ s → a ^ r = 1 →
      b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 → a * b = b * a →
        a * y = y * a → b * y = y * b → False := by
  intro r s a b y hr hs hrodd hsodd hrs ha hb hy ha1 hb1 hy1 hab hay hby
  have ha' : e a ^ r = 1 := by rw [← map_pow, ha, map_one]
  have hb' : e b ^ r = 1 := by rw [← map_pow, hb, map_one]
  have hy' : e y ^ s = 1 := by rw [← map_pow, hy, map_one]
  have ha1' : e a ≠ 1 := fun h1 => ha1 (e.injective (by rw [h1, map_one]))
  have hy1' : e y ≠ 1 := fun h1 => hy1 (e.injective (by rw [h1, map_one]))
  have hb1' : e b ∉ Subgroup.zpowers (e a) := by
    intro hm
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hm
    exact hb1 (Subgroup.mem_zpowers_iff.2 ⟨m, e.injective (by rw [map_zpow, hm])⟩)
  have hab' : e a * e b = e b * e a := by rw [← map_mul, ← map_mul, hab]
  have hay' : e a * e y = e y * e a := by rw [← map_mul, ← map_mul, hay]
  have hby' : e b * e y = e y * e b := by rw [← map_mul, ← map_mul, hby]
  exact h r s (e a) (e b) (e y) hr hs hrodd hsodd hrs ha' hb' hy' ha1' hb1' hy1' hab' hay' hby'

theorem center_eq_bot_of_simple_card {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hY : ¬ (Nat.card Y).Prime) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative Y := Subgroup.center_eq_top_iff.mp h
    exact hY (Group.is_simple_iff_prime_card.mp inferInstance)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Cls67
