module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ElemAbelianComplement
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Spor
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.T3
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Fields

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

@[expose] def T9Lie : Prop :=
  ∀ (L : Type) [Group L] [Finite L], LieCentralQuotient L → CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsKGroup L → Nat.card (Subgroup.center L) = 1 →
      CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 → GLATwoLocalRank 3 L = 0 →
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 2

@[expose] def TFAaLie : Prop :=
  ∀ (L : Type) [Group L] [Finite L], LieCentralQuotient L → CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsKGroup L → Nat.card (Subgroup.center L) = 1 →
      CFSG.Open.pRank 3 (⊤ : Subgroup L) = 1 → GLATwoLocalRank 3 L = 1 →
        ∀ H : Subgroup (MulAut L), IsElemAbelian 3 H → Nat.card H = 9 → FieldBonus L 3 H

@[expose] def TFAbLie : Prop :=
  ∀ (L : Type) [Group L] [Finite L], LieCentralQuotient L → CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsKGroup L → Nat.card (Subgroup.center L) = 3 →
      CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 → GLATwoLocalRank 3 L = 1 →
        ∀ H : Subgroup (MulAut L), IsElemAbelian 3 H → Nat.card H = 27 → FieldBonus L 3 H

theorem pRank_mulAut_le_of_meets {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hcen : Subgroup.center S = ⊥) (k : ℕ)
    (h : ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ (k + 1) →
      ∃ x ∈ D ⊓ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S, x ≠ 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ CFSG.Open.pRank p (⊤ : Subgroup S) + k := by
  have h1 := pRank_le_pRank_add_of_forall_inf_ne_bot hp
    (CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S) k (fun D hD hc hbot => by
      obtain ⟨x, hx, hx1⟩ := h D hD hc
      rw [hbot, Subgroup.mem_bot] at hx
      exact hx1 hx)
  have h2 : CFSG.Open.pRank p (CFSG.HardMathSupport.Solomon.LocalBalance.innerAut S) =
      CFSG.Open.pRank p (⊤ : Subgroup S) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (innerAutEquiv hcen)).symm
  omega

theorem tables112_T1a_lie (hO : LieOuterRank) (hT1b : T1bLie) :
    ∀ (L : Type) [Group L] [Finite L], LieCentralQuotient L → CFSG.Open.IsQuasisimple L →
      CFSG.Open.IsKGroup L → ∀ p : ℕ, p.Prime → p ≠ 2 →
        CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) + 2 := by
  intro L _ _ hF hq hK p hp hp2
  by_cases hZ : p ∣ Nat.card (Subgroup.center L)
  · have := hT1b L hF hq hK p hp hp2 (Or.inr hZ)
    omega
  · obtain ⟨idx, he⟩ := hF
    have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
    have h1 := pRank_mulAut_le_of_quasisimple hp.one_lt hq
    have h2 := pRank_mulAut_le_of_meets hp (center_quotient_eq_bot_of_quasisimple hq) 2
      (hO (L ⧸ Subgroup.center L) ‹_› (exists_noncomm_quotient_center_of_quasisimple hq) idx he
        p hp hp2)
    have h3 := pRank_quotient_center_eq_of_not_dvd hp hZ
    omega

theorem tables112On_lie_of (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpM : Tables.Multiplier.SporadicMultipliers) (hO : LieOuterRank) (hT1b : T1bLie)
    (hT2 : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L → ∀ p
        : ℕ, p.Prime → p ≠ 2 → 2 * CFSG.Open.pRank p (Subgroup.center L) ≤ CFSG.Open.pRank p (⊤ :
        Subgroup L)) (hT9 : T9Lie) (hA : TFAaLie) (hB : TFAbLie) :
    Tables112On LieCentralQuotient where
  T0 := fun L _ _ _ hq hK => table112_T0 L hq hK
  T1a := tables112_T1a_lie hO hT1b
  T1b := hT1b
  T2 := fun L _ _ _ hq hK => hT2 L hq hK
  T3 := fun L _ _ _ hq hK => Tables.Multiplier.tables112_T3_field hGA hSpM L hq hK
  T11 := fun L _ _ _ hq hK => Tables.Multiplier.tables112_T11_field hGA hSpM L hq hK
  T9 := hT9
  TFA_a := hA
  TFA_b := hB

theorem tables112_of_inputs (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSpM : Tables.Multiplier.SporadicMultipliers) (hO : LieOuterRank) (hT1b : T1bLie)
    (hT2 : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L → ∀ p
        : ℕ, p.Prime → p ≠ 2 → 2 * CFSG.Open.pRank p (Subgroup.center L) ≤ CFSG.Open.pRank p (⊤ :
        Subgroup L)) (hT9 : T9Lie) (hA : TFAaLie) (hB : TFAbLie) (hOut : SporadicOuterLeTwo)
    (hCov : SporadicCoverRank) (hTwo : SporadicCoverRankTwo) : Tables112 :=
  tables112_of_families Tables.Alt.tables112On_alt
    (tables112On_lie_of hGA hSpM hO hT1b hT2 hT9 hA hB)
    (tables112On_spor_of hOut hCov hTwo hSpM)

end CFSG.HardMathSupport.Timmesfeld.Coordinator
