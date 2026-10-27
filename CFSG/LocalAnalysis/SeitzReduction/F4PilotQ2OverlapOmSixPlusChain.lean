module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmChain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmMinusData

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix Subgroup CFSG.Assembly.LowTwoRank

abbrev omQ6p : (omPI6 → ZMod 2) → ZMod 2 := StatedQuadPlus 3 (ZMod 2)

abbrev omCodeP6 (c : ℕ) : Matrix omPI6 omPI6 (ZMod 2) := omOfCode omPEnc6 c

@[expose] def omMiHSZ : GL omPI6 (ZMod 2) := ⟨omNHS, omNHS, omNHS_sq, omNHS_sq⟩

@[expose] def omMiHLZ : GL omPI6 (ZMod 2) := ⟨omNHL, omNHL, omNHL_sq, omNHL_sq⟩

abbrev omMiTS0 : Finset omPI6 := ∅

abbrev omMiTS1 : Finset omPI6 := insert (Sum.inl 0 : omPI6) omMiTS0

@[expose] def omMiWS0 : Fin 3 → ℕ :=
  ![4433510466, 34630287489, 4569825473]

@[expose] def omMiVS0 : Fin 3 → ℕ :=
  ![4433510466, 34630287489, 4569825473]

theorem omMiCS0 : Nat.card (omChain omQ6p omMiHSZ omMiTS0) =
    3 * Nat.card (omChain omQ6p omMiHSZ omMiTS1) :=
  card_omChain_level 3 (fun k => omCodeP6 (omMiWS0 k)) (fun k => omCodeP6 (omMiVS0 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omMiTS2 : Finset omPI6 := insert (Sum.inl 1 : omPI6) omMiTS1

@[expose] def omMiWS1 : Fin 2 → ℕ :=
  ![34630287489, 4699848835]

@[expose] def omMiVS1 : Fin 2 → ℕ :=
  ![34630287489, 4699848835]

theorem omMiCS1 : Nat.card (omChain omQ6p omMiHSZ omMiTS1) =
    2 * Nat.card (omChain omQ6p omMiHSZ omMiTS2) :=
  card_omChain_level 2 (fun k => omCodeP6 (omMiWS1 k)) (fun k => omCodeP6 (omMiVS1 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omMiTS3 : Finset omPI6 := insert (Sum.inl 2 : omPI6) omMiTS2

@[expose] def omMiWS2 : Fin 8 → ℕ :=
  ![4565631105, 34630287489, 4565696897, 51810156929,
    4565663877, 43220222085, 4565729669, 60400091525]

@[expose] def omMiVS2 : Fin 8 → ℕ :=
  ![4565631105, 34630287489, 21745502337, 51810156929,
    13155565729, 43220222085, 30335436961, 60400091525]

theorem omMiCS2 : Nat.card (omChain omQ6p omMiHSZ omMiTS2) =
    8 * Nat.card (omChain omQ6p omMiHSZ omMiTS3) :=
  card_omChain_level 8 (fun k => omCodeP6 (omMiWS2 k)) (fun k => omCodeP6 (omMiVS2 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omMiTS4 : Finset omPI6 := insert (Sum.inr 2 : omPI6) omMiTS3

@[expose] def omMiWS3 : Fin 4 → ℕ :=
  ![34630287489, 34630355073, 34630320289, 34630387873]

@[expose] def omMiVS3 : Fin 4 → ℕ :=
  ![34630287489, 34630355073, 34630320289, 34630387873]

theorem omMiCS3 : Nat.card (omChain omQ6p omMiHSZ omMiTS3) =
    4 * Nat.card (omChain omQ6p omMiHSZ omMiTS4) :=
  card_omChain_level 4 (fun k => omCodeP6 (omMiWS3 k)) (fun k => omCodeP6 (omMiVS3 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omMiTS5 : Finset omPI6 := insert (Sum.inr 0 : omPI6) omMiTS4

@[expose] def omMiWS4 : Fin 2 → ℕ :=
  ![34630287489, 34630288017]

@[expose] def omMiVS4 : Fin 2 → ℕ :=
  ![34630287489, 34630288017]

theorem omMiCS4 : Nat.card (omChain omQ6p omMiHSZ omMiTS4) =
    2 * Nat.card (omChain omQ6p omMiHSZ omMiTS5) :=
  card_omChain_level 2 (fun k => omCodeP6 (omMiWS4 k)) (fun k => omCodeP6 (omMiVS4 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omMiTS6 : Finset omPI6 := insert (Sum.inr 1 : omPI6) omMiTS5

@[expose] def omMiWS5 : Fin 1 → ℕ :=
  ![34630287489]

@[expose] def omMiVS5 : Fin 1 → ℕ :=
  ![34630287489]

theorem omMiCS5 : Nat.card (omChain omQ6p omMiHSZ omMiTS5) =
    1 * Nat.card (omChain omQ6p omMiHSZ omMiTS6) :=
  card_omChain_level 1 (fun k => omCodeP6 (omMiWS5 k)) (fun k => omCodeP6 (omMiVS5 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem omMi_card_CS :
    Nat.card (omIsoGroup omQ6p ⊓ centralizer ({omMiHSZ} : Set (GL omPI6 (ZMod 2))) :
      Subgroup (GL omPI6 (ZMod 2))) = 384 := by
  rw [← omChain_empty, omMiCS0, omMiCS1, omMiCS2, omMiCS3, omMiCS4, omMiCS5,
    show omMiTS6 = Finset.univ by decide, omChain_univ, Subgroup.card_bot]

abbrev omMiTL0 : Finset omPI6 := ∅

abbrev omMiTL1 : Finset omPI6 := insert (Sum.inl 0 : omPI6) omMiTL0

@[expose] def omMiWL0 : Fin 1 → ℕ :=
  ![34630287489]

@[expose] def omMiVL0 : Fin 1 → ℕ :=
  ![34630287489]

theorem omMiCL0 : Nat.card (omChain omQ6p omMiHLZ omMiTL0) =
    1 * Nat.card (omChain omQ6p omMiHLZ omMiTL1) :=
  card_omChain_level 1 (fun k => omCodeP6 (omMiWL0 k)) (fun k => omCodeP6 (omMiVL0 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omMiTL2 : Finset omPI6 := insert (Sum.inl 1 : omPI6) omMiTL1

@[expose] def omMiWL1 : Fin 6 → ℕ :=
  ![34395407361, 34630287489, 7350657153, 4330751491,
    4699848835, 37549531267]

@[expose] def omMiVL1 : Fin 6 → ℕ :=
  ![34395407361, 34630287489, 7350657153, 4464968721,
    4699848835, 37549531267]

theorem omMiCL1 : Nat.card (omChain omQ6p omMiHLZ omMiTL1) =
    6 * Nat.card (omChain omQ6p omMiHLZ omMiTL2) :=
  card_omChain_level 6 (fun k => omCodeP6 (omMiWL1 k)) (fun k => omCodeP6 (omMiVL1 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omMiTL3 : Finset omPI6 := insert (Sum.inr 1 : omPI6) omMiTL2

@[expose] def omMiWL2 : Fin 4 → ℕ :=
  ![34630287489, 21745569153, 4565631633, 51810226065]

@[expose] def omMiVL2 : Fin 4 → ℕ :=
  ![34630287489, 21745569153, 4565631633, 51810226065]

theorem omMiCL2 : Nat.card (omChain omQ6p omMiHLZ omMiTL2) =
    4 * Nat.card (omChain omQ6p omMiHLZ omMiTL3) :=
  card_omChain_level 4 (fun k => omCodeP6 (omMiWL2 k)) (fun k => omCodeP6 (omMiVL2 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omMiTL4 : Finset omPI6 := insert (Sum.inl 2 : omPI6) omMiTL3

@[expose] def omMiWL3 : Fin 4 → ℕ :=
  ![4565631105, 34630287489, 4565663877, 43220222085]

@[expose] def omMiVL3 : Fin 4 → ℕ :=
  ![4565631105, 34630287489, 13155565729, 43220222085]

theorem omMiCL3 : Nat.card (omChain omQ6p omMiHLZ omMiTL3) =
    4 * Nat.card (omChain omQ6p omMiHLZ omMiTL4) :=
  card_omChain_level 4 (fun k => omCodeP6 (omMiWL3 k)) (fun k => omCodeP6 (omMiVL3 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omMiTL5 : Finset omPI6 := insert (Sum.inr 2 : omPI6) omMiTL4

@[expose] def omMiWL4 : Fin 2 → ℕ :=
  ![34630287489, 34630320289]

@[expose] def omMiVL4 : Fin 2 → ℕ :=
  ![34630287489, 34630320289]

theorem omMiCL4 : Nat.card (omChain omQ6p omMiHLZ omMiTL4) =
    2 * Nat.card (omChain omQ6p omMiHLZ omMiTL5) :=
  card_omChain_level 2 (fun k => omCodeP6 (omMiWL4 k)) (fun k => omCodeP6 (omMiVL4 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omMiTL6 : Finset omPI6 := insert (Sum.inr 0 : omPI6) omMiTL5

@[expose] def omMiWL5 : Fin 1 → ℕ :=
  ![34630287489]

@[expose] def omMiVL5 : Fin 1 → ℕ :=
  ![34630287489]

theorem omMiCL5 : Nat.card (omChain omQ6p omMiHLZ omMiTL5) =
    1 * Nat.card (omChain omQ6p omMiHLZ omMiTL6) :=
  card_omChain_level 1 (fun k => omCodeP6 (omMiWL5 k)) (fun k => omCodeP6 (omMiVL5 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem omMi_card_CL :
    Nat.card (omIsoGroup omQ6p ⊓ centralizer ({omMiHLZ} : Set (GL omPI6 (ZMod 2))) :
      Subgroup (GL omPI6 (ZMod 2))) = 192 := by
  rw [← omChain_empty, omMiCL0, omMiCL1, omMiCL2, omMiCL3, omMiCL4, omMiCL5,
    show omMiTL6 = Finset.univ by decide, omChain_univ, Subgroup.card_bot]


end CFSG.SeitzReduction.F4Pilot
