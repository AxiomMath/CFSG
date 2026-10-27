module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.BorelTits (unitaryInvolution)

@[expose] def SpTwoUniParamInput (κ : Sp2mKind) (ε : ℕ) (hε : ε ≤ 1) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (_ : Nat.card F = (2 ^ 1) ^ 2)
        (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
        ∀ k : Fin (n + 1), Nonempty (NsUniParam ε hε (unitaryInvolution F 2 1) ι hι e k)

@[expose] def SpTwoUniAlignInput (ε : ℕ) (hε : ε ≤ 1) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (N : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K 2], 5 ≤ N → Nat.card K = 2 → ∀ (e : L ≃* StatedSp N K) (F : Type)
    [Field F] [Finite F] [CharP F 2], Nat.card F = (2 ^ 1) ^ 2 → ∀ (ι : K →+* F)
    (hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c),
    (∀ k : Fin N, Nonempty (NsUniParam ε hε (unitaryInvolution F 2 1) ι hι e k)) →
      ∃ P : ∀ k : Fin N, NsUniParam ε hε (unitaryInvolution F 2 1) ι hι e k, NsUniParamAgree P

theorem spTwoUnitaryCoverInput_of_inputs {κ : Sp2mKind} {ε : ℕ} (hε : ε ≤ 1)
    (hP : SpTwoUniParamInput κ ε hε) (hA : SpTwoUniAlignInput ε hε) :
    SpTwoUnitaryCoverInput κ ε := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  obtain ⟨F, _, _, _, hF, ι, hι, hpar⟩ := hP G L hset n K hK hn e t ht hKt hroot
  obtain ⟨P, hagree⟩ := hA G L (n + 1) K (by omega) hK e F hF ι hι hpar
  exact nsUnitaryCover_of_nsUniParamAgree (by omega) hF P hagree

end CFSG.SeitzReduction.SymplecticPilot
