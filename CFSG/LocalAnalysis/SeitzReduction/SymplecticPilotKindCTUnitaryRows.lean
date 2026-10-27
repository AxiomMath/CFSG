module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)

@[expose] def SpUnitaryEvenCtuParamInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 3 ≤ m → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp (m + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (m + 1), ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K')
        (_ : CharP h.fixedField 2) (C₀ : GL (Fin (2 * m)) K') (hC : IsPrimeFormGram C₀)
        (hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m)
        (ι : K ≃+* h.fixedField), Nonempty (UnitaryNeighbourParam h e t k hC hC₀ ι)) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (_ : Nat.card F = (2 ^ f) ^ 2)
        (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c),
        ∀ k : Fin (m + 1), Nonempty (CtuParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 f) ι hι e k)

@[expose] def SpUnitaryOddCtuParamInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (m f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 3 ≤ m → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp (m + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (m + 1), ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K')
        (_ : CharP h.fixedField 2) (C₀ : GL (Fin (2 * m + 1)) K') (hC : IsPrimeFormGram C₀)
        (hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') :
          Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1),
        ∀ β : StatedSp m h.fixedField ≃*
            matrixIsometryGroup (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField),
          ∃ ι : K ≃+* h.fixedField, Nonempty (UnitaryOddNeighbourParam h e t k hC hC₀ β ι)) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (_ : Nat.card F = (2 ^ f) ^ 2)
        (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c),
        ∀ k : Fin (m + 1), Nonempty (CtuParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k)

@[expose] def CtuAlignInput (ε : ℕ) (hε : ε ≤ 1) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (N f : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K 2], 5 ≤ N → Nat.card K = 2 ^ f → 2 ≤ f → ∀ (e : L ≃* StatedSp N K) (F : Type)
    [Field F] [Finite F] [CharP F 2], Nat.card F = (2 ^ f) ^ 2 → ∀ (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c),
    (∀ k : Fin N, Nonempty (CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k)) →
      ∃ P : ∀ k : Fin N, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k, CtuParamAgree P

@[expose] def SpUnitaryParamCTFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp (3 + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (3 + 1), ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K')
        (_ : CharP h.fixedField 2) (C₀ : GL (Fin (2 * 3)) K') (hC : IsPrimeFormGram C₀)
        (hC₀ : (C₀ : Matrix (Fin (2 * 3)) (Fin (2 * 3)) K') = blockSwapJ (2 * 3) 3)
        (ι : K ≃+* h.fixedField), Nonempty (UnitaryNeighbourParam h e t k hC hC₀ ι)) →
        SpGlobalCoverType e f .unitaryEven

@[expose] def SpUnitaryOddParamCTFourInput : Prop :=
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
        SpGlobalCoverType e f .unitaryOdd

theorem spUnitaryParamCTInput_of_inputs (hT : SpUnitaryEvenCtuParamInput)
    (hA : CtuAlignInput 0 (Nat.zero_le 1)) (h4 : SpUnitaryParamCTFourInput) :
    SpUnitaryParamCTInput := by
  intro G _ _ L hset m f K _ _ _ hm hKc hf e t ht hKt hP
  rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | hm4
  · exact h4 G L hset f K hKc hf e t ht hKt hP
  · obtain ⟨F, _, _, _, hF, ι, hι, hP'⟩ := hT G L hset m f K hm hKc hf e t ht hKt hP
    obtain ⟨Q, hQ⟩ := hA G L (m + 1) f K (by omega) hKc hf e F hF ι hι hP'
    exact spGlobalCoverType_of_ctuParamAgree hKc hf (by omega) hF (Or.inl ⟨rfl, rfl⟩) Q hQ

theorem spUnitaryOddParamCTInput_of_inputs (hT : SpUnitaryOddCtuParamInput)
    (hA : CtuAlignInput 1 le_rfl) (h4 : SpUnitaryOddParamCTFourInput) :
    SpUnitaryOddParamCTInput := by
  intro G _ _ L hset m f K _ _ _ hm hKc hf e t ht hKt hP
  rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | hm4
  · exact h4 G L hset f K hKc hf e t ht hKt hP
  · obtain ⟨F, _, _, _, hF, ι, hι, hP'⟩ := hT G L hset m f K hm hKc hf e t ht hKt hP
    obtain ⟨Q, hQ⟩ := hA G L (m + 1) f K (by omega) hKc hf e F hF ι hι hP'
    exact spGlobalCoverType_of_ctuParamAgree hKc hf (by omega) hF (Or.inr ⟨rfl, rfl⟩) Q hQ

end CFSG.SeitzReduction.SymplecticPilot
