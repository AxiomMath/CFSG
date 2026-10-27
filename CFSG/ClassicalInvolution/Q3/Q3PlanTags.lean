module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSL
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSU
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSpFinal
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Tags

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank

@[expose] def ClassicalMembersFundamental3Tag (t : StatedLieTag) : Prop :=
  ∀ (n : ℕ) (hp : Nat.Prime 3), IsFundTag t → StatedLieAdmissible t n 3 1 →
    ∀ (L : Subgroup (modelUniv t n 3 1 hp).K) (z : (modelUniv t n 3 1 hp).K),
      IsClassicalMember3 L z → classicalInvolutionOddCore L = ⊥ →
        L ∈ fundamentalSubgroups t (modelUniv t n 3 1 hp).D

theorem classicalMembersFundamental3_of_tags
    (h : ∀ t, IsFundTag t → ClassicalMembersFundamental3Tag t) :
    ClassicalMembersFundamental3 :=
  fun t n hp hFT hadm L z hL hO => h t hFT n hp hFT hadm L z hL hO

@[expose] def ExceptionalFundTag3 (t : StatedLieTag) : Prop :=
  t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4

theorem isFundTag_cases {t : StatedLieTag} (ht : IsFundTag t) :
    ExceptionalFundTag3 t ∨ t = .PSL ∨ t = .PSp ∨ t = .PSU ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus := by
  cases t <;> simp_all [IsFundTag, ExceptionalFundTag3]

theorem oddCentralizerFreeTag_of_classical {t : StatedLieTag} (ht : IsFundTag t)
    (hne : ¬ ExceptionalFundTag3 t) : OddCentralizerFreeTag t := by
  rcases isFundTag_cases ht with h | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h hne
  · exact oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_PSL
  · exact oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_PSp
  · exact oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_PSU
  · exact oddCentralizerFreeTag_POmegaOdd
  · exact oddCentralizerFreeTag_POmegaPlus
  · exact oddCentralizerFreeTag_POmegaMinus

theorem classicalIsFundamental3_of_tags
    (hF : ∀ t, IsFundTag t → ClassicalMembersFundamental3Tag t)
    (hE : ∀ t, IsFundTag t → ExceptionalFundTag3 t → OddCentralizerFreeTag t) :
    ClassicalIsFundamental3 :=
  classicalIsFundamental3_of_models (classicalMembersFundamental3_of_tags hF)
    modelFiniteCenterTwoGroup3
    (modelOddCentralizerFree3_of_tags fun t ht => by
      by_cases hex : ExceptionalFundTag3 t
      · exact hE t ht hex
      · exact oddCentralizerFreeTag_of_classical ht hex)

end CFSG.ClassicalInvolution.Q3
