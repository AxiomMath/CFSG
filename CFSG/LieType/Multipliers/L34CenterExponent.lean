module

public import CFSG.GH74.GLS.Classes
public import CFSG.LieType.Multipliers.L34Upper

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.P10

open CFSG Subgroup

theorem exponent_center_dvd_four
    {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) (h2 : IsPGroup 2 ↥(center Q))
    (hL : GH74.GLS.IsL34Quotient Q) : Monoid.exponent ↥(center Q) ∣ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQperf : Group.IsPerfect Q := hQ.1
  set q : Q →* Q ⧸ center Q := QuotientGroup.mk' (center Q) with hqdef
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker ≤ center Q := by rw [hqdef, QuotientGroup.ker_mk']
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker
  obtain ⟨-, ⟨eM⟩⟩ := LieType.Multipliers.L34Upper.multiplier_PSL_three_four (Q ⧸ center Q) hL
  let e := (RankThree.PerfectCover.hopfMultiplierEquivGriess (Q ⧸ center Q)).symm.trans eM
  have hadd : ∀ x : ZMod 3 × ZMod 4 × ZMod 4, 12 • x = 0 := by decide
  have h12 : ∀ m : ↥(RankThree.PerfectCover.hopfMultiplier (Q ⧸ center Q)), m ^ 12 = 1 := by
    intro m
    apply e.injective
    rw [map_pow, map_one]
    exact congrArg Multiplicative.ofAdd (hadd (Multiplicative.toAdd (e m)))
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro z
  have hz : (z : Q) ∈ q.ker := by
    rw [hqdef, QuotientGroup.ker_mk']
    exact z.2
  rw [← hmap] at hz
  obtain ⟨m, hm, hmz⟩ := hz
  have hz12 : z ^ 12 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hmz, ← map_pow, OneMemClass.coe_one]
    have h1 := congrArg Subtype.val (h12 ⟨m, hm⟩)
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1
    rw [h1, map_one]
  obtain ⟨a, ha⟩ := h2 z
  have hord : orderOf z ∣ 12 := orderOf_dvd_of_pow_eq_one hz12
  have h4 : orderOf z ∣ 4 := by
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ha)
    rw [hc] at hord ⊢
    have hc2 : c ≤ 2 := by
      by_contra hc2
      have h8 : 2 ^ 3 ∣ 2 ^ c := pow_dvd_pow 2 (by omega)
      have h9 := h8.trans hord
      norm_num at h9
    have h10 : 2 ^ c ∣ 2 ^ 2 := pow_dvd_pow 2 hc2
    simpa using h10
  exact orderOf_dvd_iff_pow_eq_one.mp h4

end CFSG.ComponentClassification.GS82PumpInputs.P10
