module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBRho
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem sec4I_seven_dvd_map (hL : IsOmega7Group L) (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega)
    {K : Subgroup G} (hKL : K ≤ L) (hK : IsTwoU43 (↥K ⧸ oddCore ↥K)) :
    7 ∣ Nat.card ((K.subgroupOf L).map (sec4IRho e)) := by
  let Q := ↥K ⧸ oddCore ↥K
  let φ : ↥K →* ProjOrth Sec4IQ := (sec4IRho e).comp (Subgroup.inclusion hKL)
  unfold IsTwoU43 at hK
  obtain ⟨hcenterQ, hmodel⟩ := hK
  have hQuotCard : Nat.card (Q ⧸ Subgroup.center Q) = 3265920 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_three
      (hmodel.statedClassicalModel_of_ne_zero (by norm_num))
  have hQ : Nat.card Q = 3265920 * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hQuotCard,
      hcenterQ]
  have hKcard : Nat.card ↥K = Nat.card Q * Nat.card (oddCore ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore ↥K)
  have hker_le : (φ.ker).map (Subgroup.inclusion hKL) ≤ (sec4ICover e).ker := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    refine MonoidHom.mem_ker.mpr ?_
    have hk1 : sec4IRho e (Subgroup.inclusion hKL k) = 1 := MonoidHom.mem_ker.mp hk
    exact Subtype.ext hk1
  have hcard_map : Nat.card φ.ker = Nat.card ((φ.ker).map (Subgroup.inclusion hKL)) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (φ.ker) (Subgroup.inclusion hKL)
      (Subgroup.inclusion_injective hKL)).toEquiv
  have hker_odd : Odd (Nat.card φ.ker) := by
    rw [hcard_map]
    exact (sec4ICover_odd hL e).odd_card_ker.of_dvd_nat (Subgroup.card_dvd_of_le hker_le)
  have hNle : φ.ker ≤ oddCore ↥K :=
    le_oddCore_of_normal (MonoidHom.normal_ker φ) hker_odd
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hNle
  have hrange : φ.range = (K.subgroupOf L).map (sec4IRho e) := by
    rw [show φ = (sec4IRho e).comp (Subgroup.inclusion hKL) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range]
  have hmain : Nat.card φ.range = 3265920 * 2 * m := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥φ.ker))
    rw [Subgroup.card_ker_mul_card_range φ, hKcard, hQ, hm]
    ring
  have h7 : 7 ∣ 3265920 := by norm_num
  have hdiv : 7 ∣ Nat.card φ.range := by
    rw [hmain]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h7 2) m
  rwa [← hrange]

end CFSG.OddStandard.SmallF3.Omega
