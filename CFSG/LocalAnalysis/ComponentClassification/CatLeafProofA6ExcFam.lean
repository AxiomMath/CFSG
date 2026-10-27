module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Exc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Twisted
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Split
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6ToralE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6ToralE8
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6ToralF4

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree (ReeTag)

theorem oddLieA6CentreFor_of_explicit
    {t : StatedLieTag} {τ : Tag} (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      UntwistedChevalleyModel J τ (p ^ f))
    (hexp : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
      Nat.card K = p ^ f → ∀ β : MulAut (adjointGroup τ K), orderOf β = 2 →
        A6CentreForm (fixedSubgroup β)) :
    OddLieA6CentreFor t := by
  intro J _ n p f hp hp2 hadm hm α hα
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ
    (hmodel J p f (GH74.chevalleyExceptionalModel_of_lieModel ht hm))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact a6CentreForm_of_mulEquiv (fixedSubgroupCongrEquiv e α)
    (hexp F p f hp hp2 hadm.2.1 hF _ hβ)

theorem oddLieA6CentreFor_F4
    : OddLieA6CentreFor .F4 :=
  oddLieA6CentreFor_of_explicit (τ := .F4) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ _ _ hp hp2 hf hK β hβ =>
      a6_F4_E8_G2_explicit (Or.inl rfl) oddExcInnerDiagA6Form_F4 hp hp2
        (fun h => absurd h (by decide)) hf hK β hβ

theorem oddLieA6CentreFor_E8
    : OddLieA6CentreFor .E8 :=
  oddLieA6CentreFor_of_explicit (τ := .E8) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ _ _ hp hp2 hf hK β hβ =>
      a6_F4_E8_G2_explicit (Or.inr (Or.inl rfl)) oddExcInnerDiagA6Form_E8 hp hp2
        (fun h => absurd h (by decide)) hf hK β hβ

theorem oddLieA6CentreFor_E7
    : OddLieA6CentreFor .E7 :=
  oddLieA6CentreFor_of_explicit (τ := .E7) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ _ _ hp hp2 hf hK β hβ => a6_E7_explicit oddExcInnerDiagA6Form_E7 hp hp2 hf hK β hβ

theorem oddLieA6CentreFor_E6
    : OddLieA6CentreFor .E6 :=
  oddLieA6CentreFor_of_explicit (τ := .E6) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ _ _ hp hp2 hf hK β hβ =>
      a6_E6_explicit oddExcInnerDiagA6Form_E6 oddE6GraphA6Form_holds hp hp2 hf hK β hβ

theorem oddLieA6CentreFor_G2
    : OddLieA6CentreFor .G2 := by
  intro J _ n p f hp hp2 hadm hm α hα
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2 : UntwistedChevalleyModel J
      .G2 (p ^ f))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  refine a6CentreForm_of_mulEquiv (fixedSubgroupCongrEquiv e α) ?_
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP F ReeTag.G2.prime :=
      LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three hf hF
    exact a6_G2_three_explicit oddExcInnerDiagA6Form_G2 hf hF (MulAut.congr e α) hβ
  · exact a6_F4_E8_G2_explicit (Or.inr (Or.inr rfl)) oddExcInnerDiagA6Form_G2 hp hp2
      (fun _ => hp3) hf hF _ hβ

theorem oddLieA6CentreFor_twistedE6
    : OddLieA6CentreFor .twistedE6 := by
  intro J _ n p f hp hp2 hadm hm α hα
  obtain rfl : n = 0 := hadm.2.2
  by_cases hi : α ∈ (MulAut.conj : J →* MulAut J).range
  · exact oddTwistedE6InnerA6Form_holds J p f hp hp2 hadm hm α hα hi
  · exact oddTwistedE6OuterA6Form_holds J p f hp hp2 hadm hm α hα hi

theorem oddLieA6CentreFor_trialityD4
    : OddLieA6CentreFor .trialityD4 := by
  intro J _ n p f hp hp2 hadm hm α hα
  obtain rfl : n = 0 := hadm.2.2
  by_cases hi : α ∈ (MulAut.conj : J →* MulAut J).range
  · exact oddTrialityInnerA6Form_holds J p f hp hp2 hadm hm α hα hi
  · exact oddTrialityOuterA6Form_holds J p f hp hp2 hadm hm α hα hi

theorem oddLieA6CentreFor_twistedG2
    : OddLieA6CentreFor .twistedG2 := by
  intro J _ n p f hp hp2 hadm hm α hα
  have hn0 : n = 0 := hadm.2.2.1
  have hp3 : p = 3 := hadm.2.2.2.1
  subst hn0
  subst hp3
  exact oddReeA6Form_holds J f hadm hm α hα

end CFSG.ComponentClassification.CatLeafProof
