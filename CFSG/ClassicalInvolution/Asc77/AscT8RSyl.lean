module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64I
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.AschTight.Sec6GenTargets
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

namespace T8R

section Syl

variable {G : Type} [Group G] [Finite G]

theorem natCard_isSylow2In_eq {V P : Subgroup G} (h : IsSylow2In V P) :
    Nat.card V = 2 ^ (Nat.card P).factorization 2 := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 ↥P))
  have h1 := h.natCard_eq (isSylow2In_map_sylow P Q)
  rw [h1, Subgroup.card_map_of_injective P.subtype_injective]
  exact Sylow.card_eq_multiplicity Q

theorem natCard_le_of_eq_sup_oddCoreOf {X J T P : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ oddCoreOf X) (hT : IsSylow2In T J) (hPX : P ≤ X) (hP : IsPGroup 2 P) :
    Nat.card P ≤ Nat.card T := by
  have hN : Odd (Nat.card (oddCoreOf X)) := oddCoreOf_odd_natCard X
  have hPN : P ≤ Subgroup.normalizer (oddCoreOf X : Set G) := fun x hx =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hPX hx))
  have hJN : J ≤ Subgroup.normalizer (oddCoreOf X : Set G) := fun x hx =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hJX hx))
  have h1 := card_sup_mul_card_inf_of_le_normalizer hPN
  have h2 := card_sup_mul_card_inf_of_le_normalizer hJN
  have hinf : P ⊓ oddCoreOf X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (eq_one_of_isPGroup_of_mem_odd hN hx.2
      (hP.to_le (Subgroup.zpowers_le.mpr hx.1)))
  rw [hinf, Subgroup.card_bot, mul_one] at h1
  have hsup : J ⊔ oddCoreOf X = X := hX.symm
  rw [hsup] at h2
  have hdvd : Nat.card (P ⊔ oddCoreOf X : Subgroup G) ∣ Nat.card X :=
    Subgroup.card_dvd_of_le (sup_le hPX (oddCoreOf_le_self X))
  rw [h1] at hdvd
  have h3 : Nat.card P * Nat.card (oddCoreOf X) * Nat.card (J ⊓ oddCoreOf X : Subgroup G) ∣
      Nat.card J * Nat.card (oddCoreOf X) := by
    rw [← h2]
    exact Nat.mul_dvd_mul_right hdvd _
  have h4 : Nat.card P ∣ Nat.card J := by
    have h5 : Nat.card P * Nat.card (J ⊓ oddCoreOf X : Subgroup G) * Nat.card (oddCoreOf X) ∣
        Nat.card J * Nat.card (oddCoreOf X) := by
      have e : Nat.card P * Nat.card (J ⊓ oddCoreOf X : Subgroup G) * Nat.card (oddCoreOf X) =
          Nat.card P * Nat.card (oddCoreOf X) * Nat.card (J ⊓ oddCoreOf X : Subgroup G) := by
        ring
      rw [e]
      exact h3
    have h6 := Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h5
    exact (Dvd.intro _ rfl).trans h6
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hJ0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
  rw [hn] at h4 ⊢
  have h7 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hJ0).mp h4
  rw [natCard_isSylow2In_eq hT]
  exact Nat.pow_le_pow_right (by norm_num) h7

theorem isSylow2In_of_eq_sup_oddCoreOf {X J T : Subgroup G} (hJX : J ≤ X)
    (hX : X = J ⊔ oddCoreOf X) (hT : IsSylow2In T J) : IsSylow2In T X := by
  refine ⟨hT.1.trans hJX, hT.2.1, fun P' hP'X hP'2 hTP' => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hTP'
    (natCard_le_of_eq_sup_oddCoreOf hJX hX hT hP'X hP'2)).symm

end Syl

end T8R

end CFSG.ClassicalInvolution.Asc77
