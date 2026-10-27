module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignFourCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignFour

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)

@[expose] def SpUnitaryOddFourOrthInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K')
        (_ : CharP h.fixedField 2) (C₀ : GL (Fin (2 * 3 + 1)) K') (hC : IsPrimeFormGram C₀)
        (hC₀ : ((C₀ : GL (Fin (2 * 3 + 1)) K') :
          Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) K') = 1),
        ∀ β : StatedSp 3 h.fixedField ≃*
            matrixIsometryGroup (1 : Matrix (Fin (2 * 3 + 1)) (Fin (2 * 3 + 1)) h.fixedField),
          ∃ ι : K ≃+* h.fixedField, Nonempty (UnitaryOddNeighbourParam h e t k hC hC₀ β ι)) →
        ∀ a ∈ pieceCore e ({0} : Finset (Fin (3 + 1))),
          ∀ b ∈ pieceCore e ({2} : Finset (Fin (3 + 1))), Commute a b

@[expose] def SpUnitaryEvenFourOrthInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K')
        (_ : CharP h.fixedField 2) (C₀ : GL (Fin (2 * 3)) K') (hC : IsPrimeFormGram C₀)
        (hC₀ : (C₀ : Matrix (Fin (2 * 3)) (Fin (2 * 3)) K') = blockSwapJ (2 * 3) 3)
        (ι : K ≃+* h.fixedField), Nonempty (UnitaryNeighbourParam h e t k hC hC₀ ι)) →
        ∀ a ∈ pieceCore e ({0} : Finset (Fin (3 + 1))),
          ∀ b ∈ pieceCore e ({2} : Finset (Fin (3 + 1))), Commute a b

@[expose] def SpUnitaryEvenFourAlignInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K')
        (_ : CharP h.fixedField 2) (C₀ : GL (Fin (2 * 3)) K') (hC : IsPrimeFormGram C₀)
        (hC₀ : (C₀ : Matrix (Fin (2 * 3)) (Fin (2 * 3)) K') = blockSwapJ (2 * 3) 3)
        (ι : K ≃+* h.fixedField), Nonempty (UnitaryNeighbourParam h e t k hC hC₀ ι)) →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = (2 ^ f) ^ 2 →
        ∀ (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c),
        (∀ k : Fin (3 + 1),
          Nonempty (CtuParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 f) ι hι e k)) →
          ∃ P : ∀ k : Fin (3 + 1), CtuParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 f) ι hι e k,
            CtuParamAgree P

theorem spUnitaryOddParamCTFourInput_of_orth (h : SpUnitaryOddFourOrthInput) :
    SpUnitaryOddParamCTFourInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hP
  obtain ⟨F, _, _, _, hF, ι, hι, hP'⟩ :=
    spUnitaryOddCtuParamInput_holds G L hset 3 f K le_rfl hKc hf e t ht hKt hP
  obtain ⟨Q, hQ⟩ := exists_ctuParamAgree_odd_four hKc hF hf le_rfl fun k => (hP' k).some
  exact spGlobalCoverType_four_of_ctuParamAgree hKc hf hF (Or.inr ⟨rfl, rfl⟩) Q hQ
    (h G L hset f K hKc hf e t ht hKt hP)

theorem spUnitaryParamCTFourInput_of_align_orth (ha : SpUnitaryEvenFourAlignInput)
    (h : SpUnitaryEvenFourOrthInput) : SpUnitaryParamCTFourInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hP
  obtain ⟨F, _, _, _, hF, ι, hι, hP'⟩ :=
    spUnitaryEvenCtuParamInput_holds G L hset 3 f K le_rfl hKc hf e t ht hKt hP
  obtain ⟨Q, hQ⟩ := ha G L hset f K hKc hf e t ht hKt hP F hF ι hι hP'
  exact spGlobalCoverType_four_of_ctuParamAgree hKc hf hF (Or.inl ⟨rfl, rfl⟩) Q hQ
    (h G L hset f K hKc hf e t ht hKt hP)

theorem spUnitaryOddParamCTInput_of_orth (h : SpUnitaryOddFourOrthInput) :
    SpUnitaryOddParamCTInput :=
  spUnitaryOddParamCTInput_of_four (spUnitaryOddParamCTFourInput_of_orth h)

theorem spUnitaryParamCTInput_of_align_orth (ha : SpUnitaryEvenFourAlignInput)
    (h : SpUnitaryEvenFourOrthInput) : SpUnitaryParamCTInput :=
  spUnitaryParamCTInput_of_four (spUnitaryParamCTFourInput_of_align_orth ha h)

end CFSG.SeitzReduction.SymplecticPilot
