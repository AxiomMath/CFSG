module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Descent
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem

@[expose] def thetaE8' : Fin (Tag.rank .E8) → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem thetaE8_eq : thetaE8 = thetaE8' := by
  set X : Fin (Tag.rank .E8) → ℤ := thetaE8 - thetaE8' with hX
  have hXj : ∀ j, iform X (Pi.single j 1) = 0 := by
    intro j
    rw [hX, iform_sub_left, iform_thetaE8_single]
    revert j
    unfold thetaE8'
    decide +kernel
  have hX0 : X = 0 := by
    by_contra hne
    have hpos := iform_self_pos hne
    rw [iform_eq_sum_single X X] at hpos
    simp only [hXj, mul_zero, Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  exact sub_eq_zero.1 hX0

@[expose] def IsPartnerE8 (δ : Fin (Tag.rank .E8) → ℤ) : Prop :=
  IsRoot .E8 δ ∧ iform thetaE8 δ = -1

@[expose] def deltaE8 : Fin (Tag.rank .E8) → ℤ := ![0, 0, 0, 0, 0, 0, 0, -1]

theorem isPartnerE8_deltaE8 : IsPartnerE8 deltaE8 := by
  refine ⟨mem_rootFinset.1 ?_, ?_⟩
  · decide +kernel
  · rw [thetaE8_eq]
    decide +kernel

@[expose] def idxE8 (n : ℕ) (h : n < 8 := by decide) : Fin (Tag.rank .E8) := ⟨n, h⟩

@[expose] def wordActE8 (l : List (Fin (Tag.rank .E8))) (v : Fin (Tag.rank .E8) → ℤ) :
    Fin (Tag.rank .E8) → ℤ :=
  l.foldr (fun j w => reflect .E8 j w) v

@[expose] def partnerWordsE8 : List (List (Fin 8)) :=
  [[],
    [6],
    [5, 6],
    [4, 5, 6],
    [3, 4, 5, 6],
    [1, 3, 4, 5, 6],
    [2, 3, 4, 5, 6],
    [0, 2, 3, 4, 5, 6],
    [2, 1, 3, 4, 5, 6],
    [0, 2, 1, 3, 4, 5, 6],
    [3, 2, 1, 3, 4, 5, 6],
    [3, 0, 2, 1, 3, 4, 5, 6],
    [4, 3, 2, 1, 3, 4, 5, 6],
    [2, 3, 0, 2, 1, 3, 4, 5, 6],
    [4, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 4, 3, 2, 1, 3, 4, 5, 6],
    [4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 4, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 5, 4, 3, 2, 1, 3, 4, 5, 6],
    [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6],
    [1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6]]

theorem partnerWordsE8_spec : ∀ l ∈ partnerWordsE8, ∀ j ∈ l, j.val ≤ 6 := by
  decide +kernel

theorem partnerWordsE8_cover : ∀ δ ∈ rootFinset .E8, iform thetaE8' δ = -1 →
    ∃ l ∈ partnerWordsE8, wordActE8 l deltaE8 = δ := by
  decide +kernel

theorem exists_word_partnerE8 {δ : Fin (Tag.rank .E8) → ℤ} (hδ : IsPartnerE8 δ) :
    ∃ l : List (Fin (Tag.rank .E8)), (∀ j ∈ l, j ∈ JE8) ∧ wordActE8 l deltaE8 = δ := by
  rw [IsPartnerE8, thetaE8_eq] at hδ
  obtain ⟨l, hl, h⟩ := partnerWordsE8_cover δ (mem_rootFinset.2 hδ.1) hδ.2
  exact ⟨l, fun j hj => partnerWordsE8_spec l hl j hj, h⟩

variable {F : Type} [Field F]

theorem thetaDiag_reflect (j : Fin (Tag.rank .E8)) (δ : Fin (Tag.rank .E8) → ℤ) (c : Fˣ) :
    thetaDiag (reflect .E8 j δ) c =
      fun l => thetaDiag δ c l * thetaDiag δ c j ^ (-Tag.cartan .E8 j l) := by
  funext l
  have h : iform δ (Pi.single l 1) - iform δ (Pi.single j 1) * Tag.cartan .E8 j l =
      iform δ (Pi.single l 1) + iform δ (Pi.single j 1) * (-Tag.cartan .E8 j l) := by ring
  simp only [thetaDiag, iform_reflect_single, h, zpow_add, ← zpow_mul]

end CFSG.ClassicalInvolution.ModelFacts.Levi
