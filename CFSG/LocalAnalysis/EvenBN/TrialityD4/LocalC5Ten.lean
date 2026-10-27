module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Eight

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def yamadaL₆ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  pCoreOf 2 (normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G))

@[expose] noncomputable def yamadaR₆ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaL₆ d t ⊔ d.S.map L.subtype

@[expose] noncomputable def yamadaM₆ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaL₆ d t ⊓ centralizer (yamadaY₂ d t : Set G)

@[expose] noncomputable def yamadaF₄ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaM₄ d t ⊓ yamadaD₄ d t

theorem yamadaL₆_le (d : TrialityD4Data L q) (t : G) :
    yamadaL₆ d t ≤ normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G) :=
  LieType.BorelTits.pCoreOf_le 2 _

theorem le_normalizer_yamadaL₆ (d : TrialityD4Data L q) (t : G) :
    normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G) ≤
      normalizer (yamadaL₆ d t : Set G) :=
  LieType.BorelTits.le_normalizer_pCoreOf 2 _

theorem yamadaL₆_le_yamadaR₆ (d : TrialityD4Data L q) (t : G) : yamadaL₆ d t ≤ yamadaR₆ d t :=
  le_sup_left

theorem S_map_le_yamadaR₆ (d : TrialityD4Data L q) (t : G) :
    d.S.map L.subtype ≤ yamadaR₆ d t :=
  le_sup_right

theorem yamadaM₆_le_yamadaL₆ (d : TrialityD4Data L q) (t : G) : yamadaM₆ d t ≤ yamadaL₆ d t :=
  inf_le_left

theorem yamadaF₄_le_yamadaM₄ (d : TrialityD4Data L q) (t : G) : yamadaF₄ d t ≤ yamadaM₄ d t :=
  inf_le_left

theorem yamadaF₄_le_yamadaD₄ (d : TrialityD4Data L q) (t : G) : yamadaF₄ d t ≤ yamadaD₄ d t :=
  inf_le_right

theorem isPGroup_yamadaL₆ [Finite G] (d : TrialityD4Data L q) (t : G) :
    IsPGroup 2 (yamadaL₆ d t) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  LieType.BorelTits.pCoreOf_isPGroup 2 _

end Defs

end CFSG.LocalAnalysis.EvenBN.TrialityD4
