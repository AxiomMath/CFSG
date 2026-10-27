module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REvenExcA
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenTriality
public import CFSG.Sporadic.Schreier.TitsInner

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace L34R

theorem not_isL34Type_outer_E6
    (hO : LieOrderFormulasInput) {K : Type} [Group K] {n f : ℕ}
    (hadm : StatedLieAdmissible .E6 n 2 f) (hm : LieModel K .E6 n 2 f)
    {α : MulAut K} (hα2 : orderOf α = 2) (hαo : α ∉ (MulAut.conj : K →* MulAut K).range)
    {P : Subgroup (fixedSubgroup α)} (hP : IsPComponent 2 P) :
    ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hu
  have : Finite (ModGL .E6 F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .E6 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨τ', n', f', hτ', hadm', hm'⟩ :=
    even_E6_outer_lieModel_tag hf hF β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  refine not_isL34Type_of_nonclassical hO ?_ hadm' hm'
  rcases hτ' with rfl | rfl | rfl <;> decide

theorem not_isL34Type_outer_twistedE6
    (hO : LieOrderFormulasInput) {K : Type} [Group K] {n f : ℕ}
    (hadm : StatedLieAdmissible .twistedE6 n 2 f) (hm : LieModel K .twistedE6 n 2 f)
    {α : MulAut K} (hα2 : orderOf α = 2) (hαo : α ∉ (MulAut.conj : K →* MulAut K).range)
    {P : Subgroup (fixedSubgroup α)} (hP : IsPComponent 2 P) :
    ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.E6.tag M) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨hadm', hm'⟩ :=
    even_twistedE6_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  exact not_isL34Type_of_nonclassical hO (by decide) hadm' hm'

theorem not_isL34Type_outer_trialityD4
    (hO : LieOrderFormulasInput) {K : Type} [Group K] {n f : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 n 2 f) (hm : LieModel K .trialityD4 n 2 f)
    {α : MulAut K} (hα2 : orderOf α = 2) (hαo : α ∉ (MulAut.conj : K →* MulAut K).range)
    {P : Subgroup (fixedSubgroup α)} (hP : IsPComponent 2 P) :
    ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .D4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.D4.tag M) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.D4 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', hadm', hm'⟩ :=
    even_triality_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  exact not_isL34Type_of_nonclassical hO (by decide) hadm' hm'

theorem false_of_outer_suzukiRee
    {K : Type} [Group K] {τ : StatedLieTag} {n f : ℕ}
    (hτ : τ = .twistedB2 ∨ τ = .twistedF4 ∨ τ = .Tits) (hadm : StatedLieAdmissible τ n 2 f)
    (hm : LieModel K τ n 2 f) {α : MulAut K} (hα2 : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : K →* MulAut K).range) : False := by
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  apply hαo
  rcases hτ with rfl | rfl | rfl
  · refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K f (Or.inl ?_) α
      hα
    rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
  · refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K f
      (Or.inr (Or.inl ?_)) α hα
    rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
  · obtain rfl : f = 1 := hadm.2.2.2.2
    refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
      (Or.inr (Or.inr ?_)) α hα
    rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)

end L34R

end CFSG.ComponentClassification.GrSLit
