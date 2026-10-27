module

public import CFSG.ClassicalInvolution.Asc77.AscR10E19
public import CFSG.ClassicalInvolution.Asc77.AscR10E7
public import CFSG.ClassicalInvolution.Asc77.AscR10E8
public import CFSG.ClassicalInvolution.Asc77.AscR10E12
public import CFSG.ClassicalInvolution.Asc77.AscR10E16
public import CFSG.ClassicalInvolution.Asc77.AscR10E6
public import CFSG.ClassicalInvolution.Asc77.AscR10D3e
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthTw

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups
open CFSG.ClassicalInvolution.Asc77.T3CII (ne_two_of_pow_eq_three neZero_of_pow_eq_three
  StdDich3)



section Main

variable {p e : ℕ} [Fact p.Prime]

theorem orthBranch_twistedE6_three (hadm : StatedLieAdmissible .twistedE6 0 p e) :
    OrthBranch3 p .twistedE6 0 e := by
  intro h3
  have hp2 := ne_two_of_pow_eq_three h3
  have hq2 : 5 ≤ p ^ (2 * e) := by
    rw [pow_mul', h3]
    norm_num
  have hθ : IsLongRoot .E6 betaTw :=
    isLongRoot_of_isRoot_of_simplyLaced (Or.inl rfl) isRoot_betaTw
  have hlongD : Generic.IsLongestRoot (Generic.modelUniv .twistedE6 0 p e Fact.out).D
      (proj betaTw) := isLongestRoot_twistedDatum_proj (frobQ p e) isRoot_betaTw rho_betaTw
  refine (orthBranch_of_hullEmbedding3 (t := .twistedE6) (τ := .E6) (f := 2 * e) h3 hq2
    trivial (by decide) (by decide) (by decide) hadm (psiTw p e) (fun x => ?_)
    (ker_twistedE6Phi_le_center p e (GaloisField p (2 * e)))
    (ker_twistedE6Phi_sq_three h3 (GaloisField p (2 * e)))
    (CFSG.ClassicalInvolution.Balance.Bootstrap.twistedE6SignGroup 0 p e)
    (fun c hc => exists_sign_of_mem_twistedE6SignGroup p e hc)
    (CFSG.ClassicalInvolution.Balance.Bootstrap.twistedE6_pairFrame hadm hp2)
    (fundamentalSingleClass .twistedE6 0 p e Fact.out trivial hadm (by decide) (by decide))
    (Rθ := stdRankTw p e) ⟨1, proj betaTw, Or.inl hlongD, (Generic.conjSub_one _).symm⟩ hθ
    (map_stdRankTw_le p e) (sat_stdRankTw p e hp2)
    fun _ γ hγ _ => isLongRoot_of_isRoot_of_simplyLaced (Or.inl rfl) hγ.1) h3
  exact psiTw_mem_adjointGroup p e x

theorem a2BranchLeft_twistedE6_three (hadm : StatedLieAdmissible .twistedE6 0 p e) :
    A2BranchLeft3 p .twistedE6 0 e :=
  fun h3 _ h₁ _ h₂ _ _ hc₁ hc₂ ho₁ ho₂ hcomm hn =>
    Levi.a2BranchLeft_twistedE6_aux_three hadm Levi.a2UnitaryTw_three
      (ne_two_of_pow_eq_three h3) h3 h₁ h₂ hc₁ hc₂ ho₁ ho₂ hcomm hn

theorem stdDich3Gen_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 p e) :
    StdDich3Gen p .twistedE6 0 e :=
  stdDich3Gen_of_branches (orthBranch_twistedE6_three hadm)
    (a2BranchLeft_twistedE6_three hadm).a2Branch3

theorem stdDich3_twistedE6 (hadm : StatedLieAdmissible .twistedE6 0 3 1) :
    StdDich3 .twistedE6 0 :=
  stdDich3_of_gen (stdDich3Gen_twistedE6 hadm)

end Main

theorem stdDich3Exc : CFSG.ClassicalInvolution.Asc77.T3CII.StdDich3Exc := by
  intro t n hadm ht
  have hn : n = 0 := by
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> exact hadm.2.2
  subst hn
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact stdDich3_f4 hadm
  · exact stdDich3_e6 hadm
  · exact stdDich3_e7 hadm
  · exact stdDich3_e8 hadm
  · exact stdDich3_twistedE6 hadm

end CFSG.ClassicalInvolution.ModelFacts
