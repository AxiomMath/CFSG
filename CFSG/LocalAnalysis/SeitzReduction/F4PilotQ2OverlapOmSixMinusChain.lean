module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmChain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmPlusData

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Matrix Subgroup CFSG.Assembly.LowTwoRank

abbrev omQ6m : (omMI6 → ZMod 2) → ZMod 2 := StatedQuadMinus 3 (ZMod 2) 1 1

abbrev omCode6 (c : ℕ) : Matrix omMI6 omMI6 (ZMod 2) := omOfCode omMEnc6 c

@[expose] def omPlHSZ : GL omMI6 (ZMod 2) := ⟨omPHS, omPHS, omPHS_sq, omPHS_sq⟩

@[expose] def omPlHLZ : GL omMI6 (ZMod 2) := ⟨omPHL, omPHL, omPHL_sq, omPHL_sq⟩

abbrev omPlTS0 : Finset omMI6 := ∅

abbrev omPlTS1 : Finset omMI6 := insert (Sum.inl 0 : omMI6) omPlTS0

@[expose] def omPlWS0 : Fin 3 → ℕ :=
  ![17717821506, 34630287489, 17718886593]

@[expose] def omPlVS0 : Fin 3 → ℕ :=
  ![17717821506, 34630287489, 17718886593]

theorem omPlCS0 : Nat.card (omChain omQ6m omPlHSZ omPlTS0) =
    3 * Nat.card (omChain omQ6m omPlHSZ omPlTS1) :=
  card_omChain_level 3 (fun k => omCode6 (omPlWS0 k)) (fun k => omCode6 (omPlVS0 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omPlTS2 : Finset omMI6 := insert (Sum.inl 1 : omMI6) omPlTS1

@[expose] def omPlWS1 : Fin 2 → ℕ :=
  ![34630287489, 17719902339]

@[expose] def omPlVS1 : Fin 2 → ℕ :=
  ![34630287489, 17719902339]

theorem omPlCS1 : Nat.card (omChain omQ6m omPlHSZ omPlTS1) =
    2 * Nat.card (omChain omQ6m omPlHSZ omPlTS2) :=
  card_omChain_level 2 (fun k => omCode6 (omPlWS1 k)) (fun k => omCode6 (omPlVS1 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omPlTS3 : Finset omMI6 := insert (Sum.inr (Sum.inr 0) : omMI6) omPlTS2

@[expose] def omPlWS2 : Fin 12 → ℕ :=
  ![17718853761, 34630287489, 51810156673, 17853073025,
    43220223617, 60400092801, 17785962645, 38925254805,
    56105123989, 17920181909, 47515190933, 64695060117]

@[expose] def omPlVS2 : Fin 12 → ℕ :=
  ![17718853761, 34630287489, 51810156673, 26308790913,
    43220223617, 60400092801, 22013821093, 38925254805,
    56105123989, 30603758245, 47515190933, 64695060117]

theorem omPlCS2 : Nat.card (omChain omQ6m omPlHSZ omPlTS2) =
    12 * Nat.card (omChain omQ6m omPlHSZ omPlTS3) :=
  card_omChain_level 12 (fun k => omCode6 (omPlWS2 k)) (fun k => omCode6 (omPlVS2 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omPlTS4 : Finset omMI6 := insert (Sum.inr (Sum.inr 1) : omMI6) omPlTS3

@[expose] def omPlWS3 : Fin 8 → ℕ :=
  ![34630287489, 35167158401, 34764507777, 35301378689,
    34697396389, 35234267301, 34831616677, 35368487589]

@[expose] def omPlVS3 : Fin 8 → ℕ :=
  ![34630287489, 35167158401, 34764507777, 35301378689,
    34697396389, 35234267301, 34831616677, 35368487589]

theorem omPlCS3 : Nat.card (omChain omQ6m omPlHSZ omPlTS3) =
    8 * Nat.card (omChain omQ6m omPlHSZ omPlTS4) :=
  card_omChain_level 8 (fun k => omCode6 (omPlWS3 k)) (fun k => omCode6 (omPlVS3 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omPlTS5 : Finset omMI6 := insert (Sum.inr (Sum.inl 0) : omMI6) omPlTS4

@[expose] def omPlWS4 : Fin 2 → ℕ :=
  ![34630287489, 34630287753]

@[expose] def omPlVS4 : Fin 2 → ℕ :=
  ![34630287489, 34630287753]

theorem omPlCS4 : Nat.card (omChain omQ6m omPlHSZ omPlTS4) =
    2 * Nat.card (omChain omQ6m omPlHSZ omPlTS5) :=
  card_omChain_level 2 (fun k => omCode6 (omPlWS4 k)) (fun k => omCode6 (omPlVS4 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omPlTS6 : Finset omMI6 := insert (Sum.inr (Sum.inl 1) : omMI6) omPlTS5

@[expose] def omPlWS5 : Fin 1 → ℕ :=
  ![34630287489]

@[expose] def omPlVS5 : Fin 1 → ℕ :=
  ![34630287489]

theorem omPlCS5 : Nat.card (omChain omQ6m omPlHSZ omPlTS5) =
    1 * Nat.card (omChain omQ6m omPlHSZ omPlTS6) :=
  card_omChain_level 1 (fun k => omCode6 (omPlWS5 k)) (fun k => omCode6 (omPlVS5 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem omPl_card_CS :
    Nat.card (omIsoGroup omQ6m ⊓ centralizer ({omPlHSZ} : Set (GL omMI6 (ZMod 2))) :
      Subgroup (GL omMI6 (ZMod 2))) = 1152 := by
  rw [← omChain_empty, omPlCS0, omPlCS1, omPlCS2, omPlCS3, omPlCS4, omPlCS5,
    show omPlTS6 = Finset.univ by decide, omChain_univ, Subgroup.card_bot]

abbrev omPlTL0 : Finset omMI6 := ∅

abbrev omPlTL1 : Finset omMI6 := insert (Sum.inl 0 : omMI6) omPlTL0

@[expose] def omPlWL0 : Fin 1 → ℕ :=
  ![34630287489]

@[expose] def omPlVL0 : Fin 1 → ℕ :=
  ![34630287489]

theorem omPlCL0 : Nat.card (omChain omQ6m omPlHLZ omPlTL0) =
    1 * Nat.card (omChain omQ6m omPlHLZ omPlTL1) :=
  card_omChain_level 1 (fun k => omCode6 (omPlWL0 k)) (fun k => omCode6 (omPlVL0 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omPlTL2 : Finset omMI6 := insert (Sum.inl 1 : omMI6) omPlTL1

@[expose] def omPlWL1 : Fin 6 → ℕ :=
  ![34628715009, 34630287489, 34672754817, 34628715267,
    34631336067, 34673803395]

@[expose] def omPlVL1 : Fin 6 → ℕ :=
  ![34628715009, 34630287489, 34672754817, 34629763593,
    34631336067, 34673803395]

theorem omPlCL1 : Nat.card (omChain omQ6m omPlHLZ omPlTL1) =
    6 * Nat.card (omChain omQ6m omPlHLZ omPlTL2) :=
  card_omChain_level 6 (fun k => omCode6 (omPlWL1 k)) (fun k => omCode6 (omPlVL1 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omPlTL3 : Finset omMI6 := insert (Sum.inr (Sum.inl 1) : omMI6) omPlTL2

@[expose] def omPlWL2 : Fin 4 → ℕ :=
  ![34630287489, 34764507777, 34630287753, 34764508041]

@[expose] def omPlVL2 : Fin 4 → ℕ :=
  ![34630287489, 34764507777, 34630287753, 34764508041]

theorem omPlCL2 : Nat.card (omChain omQ6m omPlHLZ omPlTL2) =
    4 * Nat.card (omChain omQ6m omPlHLZ omPlTL3) :=
  card_omChain_level 4 (fun k => omCode6 (omPlWL2 k)) (fun k => omCode6 (omPlVL2 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omPlTL4 : Finset omMI6 := insert (Sum.inr (Sum.inr 0) : omMI6) omPlTL3

@[expose] def omPlWL3 : Fin 2 → ℕ :=
  ![34630287489, 38925254805]

@[expose] def omPlVL3 : Fin 2 → ℕ :=
  ![34630287489, 38925254805]

theorem omPlCL3 : Nat.card (omChain omQ6m omPlHLZ omPlTL3) =
    2 * Nat.card (omChain omQ6m omPlHLZ omPlTL4) :=
  card_omChain_level 2 (fun k => omCode6 (omPlWL3 k)) (fun k => omCode6 (omPlVL3 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omPlTL5 : Finset omMI6 := insert (Sum.inr (Sum.inr 1) : omMI6) omPlTL4

@[expose] def omPlWL4 : Fin 4 → ℕ :=
  ![34630287489, 35167158401, 34697396389, 35234267301]

@[expose] def omPlVL4 : Fin 4 → ℕ :=
  ![34630287489, 35167158401, 34697396389, 35234267301]

theorem omPlCL4 : Nat.card (omChain omQ6m omPlHLZ omPlTL4) =
    4 * Nat.card (omChain omQ6m omPlHLZ omPlTL5) :=
  card_omChain_level 4 (fun k => omCode6 (omPlWL4 k)) (fun k => omCode6 (omPlVL4 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev omPlTL6 : Finset omMI6 := insert (Sum.inr (Sum.inl 0) : omMI6) omPlTL5

@[expose] def omPlWL5 : Fin 1 → ℕ :=
  ![34630287489]

@[expose] def omPlVL5 : Fin 1 → ℕ :=
  ![34630287489]

theorem omPlCL5 : Nat.card (omChain omQ6m omPlHLZ omPlTL5) =
    1 * Nat.card (omChain omQ6m omPlHLZ omPlTL6) :=
  card_omChain_level 1 (fun k => omCode6 (omPlWL5 k)) (fun k => omCode6 (omPlVL5 k))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem omPl_card_CL :
    Nat.card (omIsoGroup omQ6m ⊓ centralizer ({omPlHLZ} : Set (GL omMI6 (ZMod 2))) :
      Subgroup (GL omMI6 (ZMod 2))) = 192 := by
  rw [← omChain_empty, omPlCL0, omPlCL1, omPlCL2, omPlCL3, omPlCL4, omPlCL5,
    show omPlTL6 = Finset.univ by decide, omChain_univ, Subgroup.card_bot]


end CFSG.SeitzReduction.F4Pilot
