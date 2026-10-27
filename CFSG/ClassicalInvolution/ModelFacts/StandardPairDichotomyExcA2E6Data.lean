module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import Certificates.Certificate113
public import Certificates.Certificate114
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.UnitaryFrames

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem

@[expose] def thetaE6' : Fin (Tag.rank .E6) → ℤ := ![1, 2, 2, 3, 2, 1]

theorem thetaE6_eq : thetaE6 = thetaE6' := by
  set X : Fin (Tag.rank .E6) → ℤ := thetaE6 - thetaE6' with hX
  have hXj : ∀ j, iform X (Pi.single j 1) = 0 := by
    intro j
    rw [hX, iform_sub_left, iform_thetaE6_single]
    revert j
    unfold thetaE6'
    decide +kernel
  have hX0 : X = 0 := by
    by_contra hne
    have hpos := iform_self_pos hne
    rw [iform_eq_sum_single X X] at hpos
    simp only [hXj, mul_zero, Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  exact sub_eq_zero.1 hX0

@[expose] def IsPartnerE6 (δ : Fin (Tag.rank .E6) → ℤ) : Prop :=
  IsRoot .E6 δ ∧ iform thetaE6 δ = -1

@[expose] def deltaE6 : Fin (Tag.rank .E6) → ℤ := ![0, -1, 0, 0, 0, 0]

theorem isPartnerE6_deltaE6 : IsPartnerE6 deltaE6 := by
  refine ⟨mem_rootFinset.1 ?_, ?_⟩
  · decide +kernel
  · rw [thetaE6_eq]
    decide +kernel

@[expose] def wordActE6 (l : List (Fin (Tag.rank .E6))) (v : Fin (Tag.rank .E6) → ℤ) :
    Fin (Tag.rank .E6) → ℤ :=
  l.foldr (fun j w => reflect .E6 j w) v

@[expose] def partnerWordsE6 : List (List (Fin 6)) :=
  [[],
    [3],
    [2, 3],
    [4, 3],
    [0, 2, 3],
    [4, 2, 3],
    [5, 4, 3],
    [4, 0, 2, 3],
    [3, 4, 2, 3],
    [5, 4, 2, 3],
    [3, 4, 0, 2, 3],
    [5, 4, 0, 2, 3],
    [5, 3, 4, 2, 3],
    [2, 3, 4, 0, 2, 3],
    [5, 3, 4, 0, 2, 3],
    [4, 5, 3, 4, 2, 3],
    [5, 2, 3, 4, 0, 2, 3],
    [4, 5, 3, 4, 0, 2, 3],
    [4, 5, 2, 3, 4, 0, 2, 3],
    [3, 4, 5, 2, 3, 4, 0, 2, 3]]

theorem partnerWordsE6_spec : ∀ l ∈ partnerWordsE6, ∀ j ∈ l, j.val ≠ 1 := by
  decide +kernel

theorem partnerWordsE6_cover : ∀ δ ∈ rootFinset .E6, iform thetaE6' δ = -1 →
    ∃ l ∈ partnerWordsE6, wordActE6 l deltaE6 = δ := by
  decide +kernel

theorem exists_word_partnerE6 {δ : Fin (Tag.rank .E6) → ℤ} (hδ : IsPartnerE6 δ) :
    ∃ l : List (Fin (Tag.rank .E6)), (∀ j ∈ l, j ∈ JE6) ∧ wordActE6 l deltaE6 = δ := by
  rw [IsPartnerE6, thetaE6_eq] at hδ
  obtain ⟨l, hl, h⟩ := partnerWordsE6_cover δ (mem_rootFinset.2 hδ.1) hδ.2
  exact ⟨l, fun j hj => partnerWordsE6_spec l hl j hj, h⟩

variable {F : Type} [Field F]

theorem thetaDiag_reflect_E6 (j : Fin (Tag.rank .E6)) (δ : Fin (Tag.rank .E6) → ℤ) (c : Fˣ) :
    thetaDiag (reflect .E6 j δ) c =
      fun l => thetaDiag δ c l * thetaDiag δ c j ^ (-Tag.cartan .E6 j l) := by
  funext l
  have h : iform δ (Pi.single l 1) - iform δ (Pi.single j 1) * Tag.cartan .E6 j l =
      iform δ (Pi.single l 1) + iform δ (Pi.single j 1) * (-Tag.cartan .E6 j l) := by ring
  simp only [thetaDiag, iform_reflect_single, h, zpow_add, ← zpow_mul]

end CFSG.ClassicalInvolution.ModelFacts.Levi
