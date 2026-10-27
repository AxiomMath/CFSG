module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Base
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.CaseII
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.StageOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Next

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup CFSG.EvenSporadicStandard

variable {G : Type} [Group G] [Finite G]

@[expose] def AscentStep (H : LocalSetting G) : Prop :=
  ∀ S Λ : Subgroup G, Stage H S Λ → 2 ∣ S.index →
    ∃ S' Λ' : Subgroup G, Stage H S' Λ' ∧ 2 ∣ S'.index ∧ Nat.card S' = 8 * Nat.card S

theorem ascentStep_of_caseTwoImpossible {H : LocalSetting G} (hII : CaseTwoImpossible H) :
    AscentStep H := by
  intro S Λ h hidx
  rcases h.RC_cases hidx with hR | hR
  · exfalso
    refine hII S Λ h hidx fun P hP hPR => ?_
    rw [hR] at hPR
    exact h.le_S_of_isPGroup_of_le_sup_DC hP hPR
  · obtain ⟨T, Λ', hTcard, hst, hidx'⟩ := h.next hR
    exact ⟨T, Λ', hst, hidx', hTcard⟩

theorem exists_stage_ge (H : LocalSetting G) (h0 : Stage H H.V H.E) (hV : 2 ∣ H.V.index)
    (hstep : AscentStep H) (n : ℕ) :
    ∃ S Λ : Subgroup G, Stage H S Λ ∧ 2 ∣ S.index ∧ 8 ^ n ≤ Nat.card S := by
  induction n with
  | zero =>
    refine ⟨H.V, H.E, h0, hV, ?_⟩
    rw [pow_zero, H.card_V]
    norm_num
  | succ n ih =>
    obtain ⟨S, Λ, hS, hidx, hcard⟩ := ih
    obtain ⟨S', Λ', hS', hidx', hcard'⟩ := hstep S Λ hS hidx
    refine ⟨S', Λ', hS', hidx', ?_⟩
    rw [hcard', pow_succ]
    omega

theorem false_of_initial_stage (H : LocalSetting G) (h0 : Stage H H.V H.E) (hV : 2 ∣ H.V.index) :
    False := by
  have hII : CaseTwoImpossible H := caseTwoImpossible H
  obtain ⟨S, Λ, -, hidx, hcard⟩ :=
    exists_stage_ge H h0 hV (ascentStep_of_caseTwoImpossible hII) (Nat.card G)
  have h1 : Nat.card S ≤ Nat.card G := Subgroup.card_le_card_group S
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h2 : Nat.card G < 8 ^ Nat.card G :=
    lt_of_lt_of_le (Nat.lt_pow_self (by norm_num)) le_rfl
  omega

theorem false_of_local (hW : J1Std.WalterAbelian) (H : LocalSetting G) : False := by
  have hV : 2 ∣ H.V.index := base_not_sylow_local hW H
  exact false_of_initial_stage H (H.exists_stage_one hV) hV

theorem false_of_setting (hW : J1Std.WalterAbelian) (H : Setting G) : False :=
  false_of_local hW H.toLocal

end CFSG.EvenSporadicStandard.ReeStd
