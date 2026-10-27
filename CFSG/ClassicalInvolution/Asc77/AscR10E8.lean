module

public import CFSG.ClassicalInvolution.Asc77.AscR10E3
public import CFSG.ClassicalInvolution.Asc77.AscR10E4
public import CFSG.ClassicalInvolution.Asc77.AscR10E6
public import CFSG.ClassicalInvolution.Asc77.AscR10E7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ClassicalInvolution.Asc77.T3CII (ne_two_of_pow_eq_three neZero_of_pow_eq_three
  StdDich3)



section Main

variable {p e : ℕ} [Fact p.Prime]

theorem orthBranch_f4_three (hadm : StatedLieAdmissible .F4 0 p e) : OrthBranch3 p .F4 0 e := by
  intro h3
  have hp2 := ne_two_of_pow_eq_three h3
  have : NeZero e := neZero_of_pow_eq_three h3
  have hθ : Generic.IsLongestRoot (Generic.modelUniv .F4 0 p e Fact.out).D thetaF4 :=
    isLongestRoot_f4Datum_of_iform_eq_four isRoot_thetaF4 iform_thetaF4_self
  refine (orthBranch_of_adjointEmbedding3 (t := .F4) h3 trivial (by decide) (by decide) hadm
    (excEmbed .F4 p e) (fun x => x.2) ?_ ?_ (excSignGroup .F4 p e)
    (fun c hc => mem_excSignGroup.1 hc) (pairFrame_f4 hp2 hadm)
    (fundamentalSingleClass .F4 0 p e Fact.out trivial hadm (by decide) (by decide))
    (Rθ := stdRankOne (Generic.modelUniv .F4 0 p e Fact.out).D thetaF4)
    ⟨1, thetaF4, Or.inl hθ, (Generic.conjSub_one _).symm⟩
    (isLongRoot_f4_of_iform_eq_four isRoot_thetaF4 iform_thetaF4_self) map_stdRankOne_f4
    fun b _ hγ hclass => isLongRoot_f4_of_class_eq b hγ hclass) h3
  · change (adjointGroup .F4 (GaloisField p e)).subtype.ker ≤ _
    rw [Subgroup.ker_subtype]
    exact bot_le
  · intro x hx
    have h1 : x = 1 := Subtype.ext hx
    rw [h1, mul_one]

theorem a2BranchLeft_f4_three (hadm : StatedLieAdmissible .F4 0 p e) : A2BranchLeft3 p .F4 0 e :=
  fun h3 _ h₁ _ h₂ _ _ hc₁ hc₂ ho₁ ho₂ hcomm hn =>
    a2BranchLeft_f4_aux_odd hadm a2UnitaryF4_odd (ne_two_of_pow_eq_three h3) h₁ h₂ hc₁ hc₂ ho₁
      ho₂ hcomm hn

theorem stdDich3Gen_f4 (hadm : StatedLieAdmissible .F4 0 p e) : StdDich3Gen p .F4 0 e :=
  stdDich3Gen_of_branches (orthBranch_f4_three hadm) (a2BranchLeft_f4_three hadm).a2Branch3

theorem stdDich3_f4 (hadm : StatedLieAdmissible .F4 0 3 1) : StdDich3 .F4 0 :=
  stdDich3_of_gen (stdDich3Gen_f4 hadm)

theorem orthBranch_e8_three (hadm : StatedLieAdmissible .E8 0 p e) : OrthBranch3 p .E8 0 e := by
  intro h3
  have hp2 := ne_two_of_pow_eq_three h3
  have : NeZero e := neZero_of_pow_eq_three h3
  have hlong : ∀ k : Fin (Generic.modelUniv .E8 0 p e Fact.out).D.rank,
      Generic.IsLongestRoot (Generic.modelUniv .E8 0 p e Fact.out).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .E8 0 p e Fact.out trivial hadm k trivial
  have hθ : Generic.IsLongestRoot (Generic.modelUniv .E8 0 p e Fact.out).D thetaE8 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl hlong (mem_adjDatum_roots.2 isRoot_thetaE8)
  refine (orthBranch_of_adjointEmbedding3 (t := .E8) h3 trivial (by decide) (by decide) hadm
    (excEmbed .E8 p e) (fun x => x.2) ?_ ?_ (excSignGroup .E8 p e)
    (fun c hc => mem_excSignGroup.1 hc) (pairFrame_e8 hp2 hadm)
    (fundamentalSingleClass .E8 0 p e Fact.out trivial hadm (by decide) (by decide))
    (Rθ := stdRankOne (Generic.modelUniv .E8 0 p e Fact.out).D thetaE8)
    ⟨1, thetaE8, Or.inl hθ, (Generic.conjSub_one _).symm⟩
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inr rfl)) isRoot_thetaE8) map_stdRankOne_e8
    fun _ γ hγ _ => isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inr rfl)) hγ.1) h3
  · change (adjointGroup .E8 (GaloisField p e)).subtype.ker ≤ _
    rw [Subgroup.ker_subtype]
    exact bot_le
  · intro x hx
    have h1 : x = 1 := Subtype.ext hx
    rw [h1, mul_one]

theorem a2BranchLeft_e8_three (hadm : StatedLieAdmissible .E8 0 p e) : A2BranchLeft3 p .E8 0 e :=
  fun h3 _ h₁ _ h₂ _ _ hc₁ hc₂ ho₁ ho₂ hcomm hn =>
    a2BranchLeft_e8_aux_odd hadm a2UnitaryE8_odd (ne_two_of_pow_eq_three h3) h₁ h₂ hc₁ hc₂ ho₁
      ho₂ hcomm hn

theorem stdDich3Gen_e8 (hadm : StatedLieAdmissible .E8 0 p e) : StdDich3Gen p .E8 0 e :=
  stdDich3Gen_of_branches (orthBranch_e8_three hadm) (a2BranchLeft_e8_three hadm).a2Branch3

theorem stdDich3_e8 (hadm : StatedLieAdmissible .E8 0 3 1) : StdDich3 .E8 0 :=
  stdDich3_of_gen (stdDich3Gen_e8 hadm)

end Main

end CFSG.ClassicalInvolution.ModelFacts
