module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelDefs
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCESp6EvenUnitaryCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCHSp6SuzukiLayerCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6EvenSymplecticCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCASp6SmallReeCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBKSp6LagrangianAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCFOddLinearTwoSocleCore
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup CFSG.LocalAnalysis.ComponentInitial


theorem sector_evenLinear_of_GL3Source {Y : Type} [Group Y] [Finite Y] {D : Subgroup Y} {a : Y}
    {J : Subgroup Y} (h : GL3Source D a J) (hstd : CFSG.IsStandardSubgroup J) (hs : Sector D) :
    ∃ n f : ℕ, 2 ≤ n ∧ 1 ≤ f ∧ ∃ (k : Type) (_ : Field k), Nat.card k = 2 ^ f ∧
      Nonempty (D ≃* LinearFlag.projectiveSL n k) := by
  have : D.Normal := h.normal
  obtain ⟨ψ⟩ := h.gl3
  have hJq := SteinbergCA.isQuasisimple_of_equiv_GL_three_two ψ
  have hC : centralizer {a} = zpowers a ⊔ J := h.sup_eq.symm
  have hcomp := SteinbergCH.isComponentOf_centralizer_of_eq_sup hJq h.le_centralizer hC
  rcases hs with h1 | ⟨p, f, -, hpo, -, hm⟩ | ⟨p, f, hm⟩ | ⟨n, f, -, -, hm⟩ |
    ⟨r, f, hr, hf, hm⟩ | ⟨ℓ, f, hm⟩ | ⟨n, hn, ⟨φ⟩⟩
  · exact h1
  · exact absurd hm (SteinbergCF.not_lieModel_psl_two_of_centralizer_eq_zpowers_sup h.simple
      h.nonab h.centralizer_eq h.orderOf_eq h.le hC h.le_centralizer ⟨ψ.symm⟩ hpo)
  · exact absurd hm (SteinbergCH.layer_not_suzukiModel h.simple h.nonab h.centralizer_eq
      h.orderOf_eq h.le hJq h.le_centralizer hC p f).1
  · exfalso
    rcases hm with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact SteinbergCE.not_statedClassicalModel_PSU_of_GL_three_two_component h.simple h.nonab
        h.centralizer_eq h.orderOf_eq h.le hcomp ⟨ψ⟩ n f hc
    all_goals exact absurd ht (by decide)
  · exact absurd hm (SteinbergBI.not_lieModel_PSp_of_GL_three_two_centralizer h.simple h.nonab
      h.centralizer_eq h.orderOf_eq h.le h.le_centralizer h.sup_eq ⟨ψ⟩ r f hr hf)
  · exact absurd hm (SteinbergCA.not_reeTitsModel_twistedG2_of_GL_three_two_component h.simple
      h.nonab h.centralizer_eq h.orderOf_eq h.le hcomp ⟨ψ⟩ ℓ f).2
  · exact ((SteinbergBK.Sp6AlternatingExclusion.isEmpty_alternating_of_GL3_component h.simple
      h.nonab h.centralizer_eq h.orderOf_eq h.le hcomp
      (SteinbergBK.Sp6AlternatingExclusion.componentType_isStandardSubgroup hstd) ψ n
      hn).false φ).elim

end CFSG.EvenSmallLie.Child3
