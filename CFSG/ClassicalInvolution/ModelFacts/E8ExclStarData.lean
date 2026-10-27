module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelFrameData
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclRoots
public import Certificates.Certificate113

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts

local notation "e0V" => (Pi.single (e7Idx 0) 1 : V7)

@[expose] def starC : V7 := simpleV 1

@[expose] def star1 : V7 := simpleV 3

@[expose] def star2 : V7 := ![0, 1, 0, 1, 1, 0, 0]

@[expose] def starLam1 : V7 := ![9, 12, 17, 24, 18, 12, 6]

@[expose] def starLam2 : V7 := ![14, 20, 27, 39, 30, 20, 10]

@[expose] def starLam3 : V7 := ![16, 23, 31, 45, 35, 24, 12]

theorem starC_mem : starC ∈ rootFinset .E7 := by decide +kernel
theorem star1_mem : star1 ∈ rootFinset .E7 := by decide +kernel
theorem star2_mem : star2 ∈ rootFinset .E7 := by decide +kernel

theorem isRoot_starC : IsRoot .E7 starC := mem_rootFinset.1 starC_mem
theorem isRoot_star1 : IsRoot .E7 star1 := mem_rootFinset.1 star1_mem
theorem isRoot_star2 : IsRoot .E7 star2 := mem_rootFinset.1 star2_mem

section Levi

theorem starLam1_J : ∀ j ∈ JofL [0, 2, 3], iform starLam1 (Pi.single j 1) = 0 := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 3] → iform starLam1 (Pi.single j 1) = 0 := by
    decide +kernel
  exact this

theorem starLam1_B : ∀ σ ∈ rootFinset .E7, |iform starLam1 σ| ≤ 9 := by decide +kernel

theorem starLam1_ker : ∀ σ ∈ rootFinset .E7, iform starLam1 σ = 0 →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 3]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform starLam1 σ = 0 →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 3] → σ i = 0 := by decide +kernel
  intro σ hσ h0
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0)

theorem starLam2_J : ∀ j ∈ JofL [0, 1, 2, 3, 4], iform starLam2 (Pi.single j 1) = 0 := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 1, 2, 3, 4] →
      iform starLam2 (Pi.single j 1) = 0 := by decide +kernel
  exact this

theorem starLam2_B : ∀ σ ∈ rootFinset .E7, |iform starLam2 σ| ≤ 14 := by decide +kernel

theorem starLam2_ker : ∀ σ ∈ rootFinset .E7, iform starLam2 σ = 0 →
    σ ∈ parabolicRoots .E7 (JofL [0, 1, 2, 3, 4]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform starLam2 σ = 0 →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 1, 2, 3, 4] → σ i = 0 := by decide +kernel
  intro σ hσ h0
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0)

theorem starLam3_J : ∀ j ∈ JofL [0, 1, 2, 3, 4, 5], iform starLam3 (Pi.single j 1) = 0 := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 1, 2, 3, 4, 5] →
      iform starLam3 (Pi.single j 1) = 0 := by decide +kernel
  exact this

theorem starLam3_B : ∀ σ ∈ rootFinset .E7, |iform starLam3 σ| ≤ 16 := by decide +kernel

theorem starLam3_ker : ∀ σ ∈ rootFinset .E7, iform starLam3 σ = 0 →
    σ ∈ parabolicRoots .E7 (JofL [0, 1, 2, 3, 4, 5]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform starLam3 σ = 0 →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 1, 2, 3, 4, 5] → σ i = 0 := by decide +kernel
  intro σ hσ h0
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0)

theorem star_cut1 : ∀ σ ∈ rootFinset .E7, iform lamSign σ = 0 → Even (iform starC σ) →
    σ ∈ parabolicRoots .E7 (JofL [0, 2, 3]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform lamSign σ = 0 → Even (iform starC σ) →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 2, 3] → σ i = 0 := by decide +kernel
  intro σ hσ h0 hev
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0 hev)

theorem star_cut2 : ∀ σ ∈ rootFinset .E7, iform starLam1 σ = 0 → Even (iform star1 σ) →
    σ ∈ parabolicRoots .E7 (JofL [0, 1, 2, 3, 4]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform starLam1 σ = 0 → Even (iform star1 σ) →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 1, 2, 3, 4] → σ i = 0 := by decide +kernel
  intro σ hσ h0 hev
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0 hev)

theorem star_cut3 : ∀ σ ∈ rootFinset .E7, iform starLam2 σ = 0 → Even (iform star2 σ) →
    σ ∈ parabolicRoots .E7 (JofL [0, 1, 2, 3, 4, 5]) := by
  have h : ∀ σ ∈ rootFinset .E7, iform starLam2 σ = 0 → Even (iform star2 σ) →
      ∀ i : Fin (Tag.rank .E7), i.val ∈ [0, 1, 2, 3, 4, 5] → σ i = 0 := by decide +kernel
  intro σ hσ h0 hev
  exact mem_parabolicRoots_JofL (mem_rootFinset.1 hσ) (h σ hσ h0 hev)

theorem starC_even_J1 : ∀ j ∈ JofL [0, 2, 3], Even (iform starC (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 2, 3] → Even (iform starC (Pi.single j 1)) := by
    decide +kernel
  exact this

theorem starC_even_J2 : ∀ j ∈ JofL [0, 1, 2, 3, 4], Even (iform starC (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 1, 2, 3, 4] →
      Even (iform starC (Pi.single j 1)) := by decide +kernel
  exact this

theorem star1_even_J2 : ∀ j ∈ JofL [0, 1, 2, 3, 4], Even (iform star1 (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 1, 2, 3, 4] →
      Even (iform star1 (Pi.single j 1)) := by decide +kernel
  exact this

theorem starC_even_J3 : ∀ j ∈ JofL [0, 1, 2, 3, 4, 5], Even (iform starC (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 1, 2, 3, 4, 5] →
      Even (iform starC (Pi.single j 1)) := by decide +kernel
  exact this

theorem star1_even_J3 : ∀ j ∈ JofL [0, 1, 2, 3, 4, 5], Even (iform star1 (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 1, 2, 3, 4, 5] →
      Even (iform star1 (Pi.single j 1)) := by decide +kernel
  exact this

theorem star2_even_J3 : ∀ j ∈ JofL [0, 1, 2, 3, 4, 5], Even (iform star2 (Pi.single j 1)) := by
  have : ∀ j : Fin (Tag.rank .E7), j.val ∉ [0, 1, 2, 3, 4, 5] →
      Even (iform star2 (Pi.single j 1)) := by decide +kernel
  exact this

end Levi

section Pin

@[expose] def starPinC : List (List ℕ) :=
[
  [], [1], [3], [1, 3], [3, 1], [4, 3], [1, 3, 1], [4, 1, 3], [4, 3, 1], [5, 4, 3], [3, 4, 1, 3],
  [4, 1, 3, 1], [5, 4, 1, 3], [5, 4, 3, 1], [6, 5, 4, 3], [3, 4, 1, 3, 1], [5, 3, 4, 1, 3],
  [5, 4, 1, 3, 1], [6, 5, 4, 1, 3], [6, 5, 4, 3, 1], [4, 5, 3, 4, 1, 3], [5, 3, 4, 1, 3, 1],
  [6, 5, 3, 4, 1, 3], [6, 5, 4, 1, 3, 1], [4, 5, 3, 4, 1, 3, 1], [6, 4, 5, 3, 4, 1, 3],
  [6, 5, 3, 4, 1, 3, 1], [5, 6, 4, 5, 3, 4, 1, 3], [6, 4, 5, 3, 4, 1, 3, 1],
  [5, 6, 4, 5, 3, 4, 1, 3, 1]
]

theorem star_pinC : ∀ γ ∈ rootFinset .E7, iform thetaLit γ = 0 → iform e0V γ = 0 →
    ∃ ω ∈ starPinC, wordAct ω γ = starC ∨ wordAct ω γ = -starC := by decide +kernel

theorem starPinC_fix : ∀ ω ∈ starPinC,
    (wordAct ω thetaLit = thetaLit ∨ wordAct ω thetaLit = -thetaLit) ∧
    (wordAct ω e0V = e0V ∨ wordAct ω e0V = -e0V) := by decide +kernel

@[expose] def starPin1 : List (List ℕ) :=
  [[], [1], [4], [4, 1], [5, 4], [5, 4, 1], [6, 5, 4], [6, 5, 4, 1]]

theorem star_pin1 : ∀ γ ∈ rootFinset .E7, iform thetaLit γ = 0 → iform e0V γ = 0 →
    (iform starC γ = 1 ∨ iform starC γ = -1) →
    ∃ ω ∈ starPin1, wordAct ω γ = star1 ∨ wordAct ω γ = -star1 := by decide +kernel

theorem starPin1_fix : ∀ ω ∈ starPin1,
    (wordAct ω thetaLit = thetaLit ∨ wordAct ω thetaLit = -thetaLit) ∧
    (wordAct ω e0V = e0V ∨ wordAct ω e0V = -e0V) ∧
    (wordAct ω starC = starC ∨ wordAct ω starC = -starC) := by decide +kernel

@[expose] def starPin2 : List (List ℕ) :=
  [[], [5], [6, 5]]

theorem star_pin2 : ∀ γ ∈ rootFinset .E7, iform thetaLit γ = 0 → iform e0V γ = 0 →
    (iform starC γ = 1 ∨ iform starC γ = -1) → iform star1 γ = 0 →
    ∃ ω ∈ starPin2, wordAct ω γ = star2 ∨ wordAct ω γ = -star2 := by decide +kernel

theorem starPin2_fix : ∀ ω ∈ starPin2,
    (wordAct ω thetaLit = thetaLit ∨ wordAct ω thetaLit = -thetaLit) ∧
    (wordAct ω e0V = e0V ∨ wordAct ω e0V = -e0V) ∧
    (wordAct ω starC = starC ∨ wordAct ω starC = -starC) ∧
    (wordAct ω star1 = star1 ∨ wordAct ω star1 = -star1) := by decide +kernel

theorem star_no_root : ∀ γ ∈ rootFinset .E7, (iform starC γ = 1 ∨ iform starC γ = -1) →
    iform thetaLit γ = 0 → iform e0V γ = 0 → iform star1 γ = 0 → iform star2 γ = 0 → False := by
  decide +kernel

end Pin

end CFSG.ClassicalInvolution.ModelFacts.E7Model
