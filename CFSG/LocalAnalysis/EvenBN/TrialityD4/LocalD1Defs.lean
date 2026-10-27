module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroLayer

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def yamadaD₁ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  (yamadaC₁ d t ⊓ jZeroLayer d) ⊔ d.D.map L.subtype

@[expose] noncomputable def yamadaV₁ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaD₁ d t ⊓ centralizer (yamadaD₁ d t : Set G)

@[expose] noncomputable def yamadaS₁ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  d.S.map L.subtype ⊔ yamadaD₁ d t

@[expose] noncomputable def yamadaM₁ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaL₂ d t ⊓ yamadaS₁ d t

@[expose] noncomputable def yamadaF₁ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaM₁ d t ⊓ yamadaD₁ d t

@[expose] noncomputable def yamadaW₁ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  d.W.map L.subtype ⊔ yamadaV₁ d t

@[expose] noncomputable def yamadaY₁ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  d.Y.map L.subtype ⊔ yamadaV₁ d t

@[expose] noncomputable def yamadaY₂ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaV₁ d t ⊔ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom

@[expose] noncomputable def yamadaW₂ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  d.W.map L.subtype ⊔ yamadaY₂ d t

@[expose] noncomputable def yamadaF₂ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  d.F.map L.subtype ⊔ yamadaY₂ d t

@[expose] noncomputable def yamadaM₂ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  d.M.map L.subtype ⊔ yamadaY₂ d t

@[expose] noncomputable def yamadaS₂ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  d.S.map L.subtype ⊔ yamadaY₂ d t

end CFSG.LocalAnalysis.EvenBN.TrialityD4
