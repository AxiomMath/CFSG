module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenParam

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne levi)

@[expose] def SpThreeUnitaryOddOrthInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .unitaryOdd) → SpThreeUOddStandard e →
        ∀ a ∈ pieceCore e ({0} : Finset (Fin 3)),
          ∀ b ∈ pieceCore e ({2} : Finset (Fin 3)), Commute a b

@[expose] def SpThreeUnitaryOddSiegelAlignInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .unitaryOdd) → SpThreeUOddStandard e →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
        (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c),
        (∀ k : Fin 3, Nonempty (CtuParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k)) →
      ∀ (F' : Type) [Field F'] [Finite F'] (ι' : K →+* F') (σ' : F' ≃+* F'), σ' ≠ 1 →
        σ' * σ' = 1 → (∀ x : F', σ' x = x ↔ x ∈ Set.range ι') →
        Nonempty (SiegelFieldParam e t ι' σ') →
      ∃ (P : ∀ k : Fin 3, CtuParam 1 le_rfl (unitaryInvolution F 2 f) ι hι e k)
        (ρ₁ : levi (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
          (2 * 3 + 1)) {⟨0, by omega⟩, ⟨1, by omega⟩} →* G),
        (∀ (x : SU (unitaryInvolution F 2 f) (2 * 3 + 1))
          (hx : x ∈ rankOne (rootGroup (unitaryInvolution F 2 f)
            (unitaryInvolution_involutive hF) (2 * 3 + 1)) ⟨0, by omega⟩),
          ρ₁ ⟨x, CFSG.LieType.CurtisTits.rankOne_le_levi _ (by simp) hx⟩ =
            (P 2).Φ ⟨x, rankOne_le_ctuBlock le_rfl ⟨0, by omega⟩ (by simp) (by simp) hx⟩) ∧
        ∀ (x : SU (unitaryInvolution F 2 f) (2 * 3 + 1))
          (hx : x ∈ rankOne (rootGroup (unitaryInvolution F 2 f)
            (unitaryInvolution_involutive hF) (2 * 3 + 1)) ⟨1, by omega⟩),
          ρ₁ ⟨x, CFSG.LieType.CurtisTits.rankOne_le_levi _ (by simp) hx⟩ =
            (P 0).Φ ⟨x, rankOne_le_ctuBlock le_rfl ⟨1, by omega⟩ (by simp) (by simp) hx⟩

theorem spThreeUnitaryOddCTInput_of_orth_align (hO : SpThreeUnitaryOddOrthInput)
    (hA : SpThreeUnitaryOddSiegelAlignInput) : SpThreeUnitaryOddCTInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot hstd F _ _ _ hF ι hι hP F' _ _ ι' σ'
    hσ1 hσσ hfix hS
  obtain ⟨P, ρ₁, hρ₀, hρ₁⟩ :=
    hA G L hset f K hKc hf e t hto hKt hroot hstd F hF ι hι hP F' ι' σ' hσ1 hσσ hfix hS
  exact spGlobalCoverType_three_of_ctuParam hKc hf hF (Or.inr ⟨rfl, rfl⟩) P
    (hO G L hset f K hKc hf e t hto hKt hroot hstd) ρ₁ hρ₀ hρ₁

theorem spThreeKindCoverInput_unitaryOdd_of_orth_align
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3)
    (hO : SpThreeUnitaryOddOrthInput) (hA : SpThreeUnitaryOddSiegelAlignInput) :
    SpThreeKindCoverInput .unitaryOdd :=
  spThreeKindCoverInput_unitaryOdd_of_CT hcat hdet (spThreeUnitaryOddCTInput_of_orth_align hO hA)

end CFSG.SeitzReduction.SymplecticPilot
