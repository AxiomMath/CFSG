module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Base
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.StageOne

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def AscentStep (H : Setting G) : Prop :=
  ∀ S Λ : Subgroup G, Stage H S Λ → 2 ∣ S.index →
    ∃ S' Λ' : Subgroup G, Stage H S' Λ' ∧ 2 ∣ S'.index ∧ Nat.card S' = 8 * Nat.card S

theorem exists_stage_ge (H : Setting G) (hstep : AscentStep H) (hV : 2 ∣ H.V.index) (n : ℕ) :
    ∃ S Λ : Subgroup G, Stage H S Λ ∧ 2 ∣ S.index ∧ 8 ^ n ≤ Nat.card S := by
  induction n with
  | zero =>
    refine ⟨H.V, H.E, H.exists_stage_one hV, hV, ?_⟩
    rw [pow_zero, H.card_V]
    norm_num
  | succ n ih =>
    obtain ⟨S, Λ, hS, hidx, hcard⟩ := ih
    obtain ⟨S', Λ', hS', hidx', hcard'⟩ := hstep S Λ hS hidx
    refine ⟨S', Λ', hS', hidx', ?_⟩
    rw [hcard', pow_succ]
    omega

theorem false_of_step (hW : WalterAbelian) (H : Setting G) (hstep : AscentStep H) : False := by
  obtain ⟨S, Λ, -, -, hcard⟩ := exists_stage_ge H hstep (base_not_sylow hW H) (Nat.card G)
  have h1 : Nat.card S ≤ Nat.card G := Subgroup.card_le_card_group S
  have h2 : Nat.card G < 8 ^ Nat.card G :=
    lt_of_lt_of_le (Nat.lt_pow_self (by norm_num)) le_rfl
  omega

end CFSG.EvenSporadicStandard.J1Std
