module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Four
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Three

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def yamadaD₅ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaC₅ d t ⊓ centralizer (yamadaV₁ d t : Set G)

@[expose] noncomputable def yamadaS₃ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaR₃ d t ⊓ centralizer (yamadaV₁ d t : Set G)

@[expose] noncomputable def yamadaM₃ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaL₃ d t ⊓ centralizer (yamadaY₂ d t : Set G)

@[expose] noncomputable def yamadaD₃ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaS₃ d t ⊓ yamadaC₅ d t

@[expose] noncomputable def yamadaF₃ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaM₃ d t ⊓ yamadaD₃ d t

@[expose] noncomputable def yamadaW₃ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaL₃ d t ⊓ centralizer (yamadaW₂ d t : Set G)

end CFSG.LocalAnalysis.EvenBN.TrialityD4
