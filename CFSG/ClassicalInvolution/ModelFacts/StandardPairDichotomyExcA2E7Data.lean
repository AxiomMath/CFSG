module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import Certificates.Certificate113
public import Certificates.Certificate114
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.UnitaryFrames

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem

@[expose] def thetaE7' : Fin (Tag.rank .E7) → ℤ := ![2, 2, 3, 4, 3, 2, 1]

theorem thetaE7_eq_vec : thetaE7 = thetaE7' := by
  set X : Fin (Tag.rank .E7) → ℤ := thetaE7 - thetaE7' with hX
  have hXj : ∀ j, iform X (Pi.single j 1) = 0 := by
    intro j
    rw [hX, iform_sub_left, iform_thetaE7_single]
    revert j
    unfold thetaE7'
    decide +kernel
  have hX0 : X = 0 := by
    by_contra hne
    have hpos := iform_self_pos hne
    rw [iform_eq_sum_single X X] at hpos
    simp only [hXj, mul_zero, Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  exact sub_eq_zero.1 hX0

@[expose] def IsPartnerE7 (δ : Fin (Tag.rank .E7) → ℤ) : Prop :=
  IsRoot .E7 δ ∧ iform thetaE7 δ = -1

@[expose] def deltaE7 : Fin (Tag.rank .E7) → ℤ := ![-1, 0, 0, 0, 0, 0, 0]

theorem isPartnerE7_deltaE7 : IsPartnerE7 deltaE7 := by
  refine ⟨mem_rootFinset.1 ?_, ?_⟩
  · decide +kernel
  · rw [thetaE7_eq_vec]
    decide +kernel

@[expose] def wordActE7 (l : List (Fin (Tag.rank .E7))) (v : Fin (Tag.rank .E7) → ℤ) :
    Fin (Tag.rank .E7) → ℤ :=
  l.foldr (fun j w => reflect .E7 j w) v

@[expose] def partnerWordsE7 : List (List (Fin 7)) :=
  [[],
    [2],
    [3, 2],
    [1, 3, 2],
    [4, 3, 2],
    [4, 1, 3, 2],
    [5, 4, 3, 2],
    [3, 4, 1, 3, 2],
    [5, 4, 1, 3, 2],
    [6, 5, 4, 3, 2],
    [2, 3, 4, 1, 3, 2],
    [5, 3, 4, 1, 3, 2],
    [6, 5, 4, 1, 3, 2],
    [5, 2, 3, 4, 1, 3, 2],
    [4, 5, 3, 4, 1, 3, 2],
    [6, 5, 3, 4, 1, 3, 2],
    [4, 5, 2, 3, 4, 1, 3, 2],
    [6, 5, 2, 3, 4, 1, 3, 2],
    [6, 4, 5, 3, 4, 1, 3, 2],
    [3, 4, 5, 2, 3, 4, 1, 3, 2],
    [6, 4, 5, 2, 3, 4, 1, 3, 2],
    [5, 6, 4, 5, 3, 4, 1, 3, 2],
    [1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
    [6, 3, 4, 5, 2, 3, 4, 1, 3, 2],
    [5, 6, 4, 5, 2, 3, 4, 1, 3, 2],
    [6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
    [5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2],
    [5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
    [4, 5, 6, 3, 4, 5, 2, 3, 4, 1, 3, 2],
    [4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
    [3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2],
    [2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2]]

theorem partnerWordsE7_spec : ∀ l ∈ partnerWordsE7, ∀ j ∈ l, j.val ≠ 0 := by
  decide +kernel

theorem partnerWordsE7_cover : ∀ δ ∈ rootFinset .E7, iform thetaE7' δ = -1 →
    ∃ l ∈ partnerWordsE7, wordActE7 l deltaE7 = δ := by
  decide +kernel

theorem exists_word_partnerE7 {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsPartnerE7 δ) :
    ∃ l : List (Fin (Tag.rank .E7)), (∀ j ∈ l, j ∈ JE7) ∧ wordActE7 l deltaE7 = δ := by
  rw [IsPartnerE7, thetaE7_eq_vec] at hδ
  obtain ⟨l, hl, h⟩ := partnerWordsE7_cover δ (mem_rootFinset.2 hδ.1) hδ.2
  exact ⟨l, fun j hj => partnerWordsE7_spec l hl j hj, h⟩

variable {F : Type} [Field F]

theorem thetaDiag_reflect_E7 (j : Fin (Tag.rank .E7)) (δ : Fin (Tag.rank .E7) → ℤ) (c : Fˣ) :
    thetaDiag (reflect .E7 j δ) c =
      fun l => thetaDiag δ c l * thetaDiag δ c j ^ (-Tag.cartan .E7 j l) := by
  funext l
  have h : iform δ (Pi.single l 1) - iform δ (Pi.single j 1) * Tag.cartan .E7 j l =
      iform δ (Pi.single l 1) + iform δ (Pi.single j 1) * (-Tag.cartan .E7 j l) := by ring
  simp only [thetaDiag, iform_reflect_single, h, zpow_add, ← zpow_mul]

end CFSG.ClassicalInvolution.ModelFacts.Levi
