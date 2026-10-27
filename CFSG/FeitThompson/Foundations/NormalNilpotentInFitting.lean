module

public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Foundations.NilpotentNormalizerCondition
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] [Finite G]

private theorem pow_factorization_dvd_natCard_fittingRaw_inf {N : Subgroup G} (hN : N.Normal)
    (hnil : Group.IsNilpotent N) {p : ℕ} (hp : p.Prime) :
    p ^ (Nat.card N).factorization p ∣ Nat.card (fittingRaw G ⊓ N : Subgroup G) := by
  have : N.Normal := hN
  have : Group.IsNilpotent N := hnil
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p N))
  have hchar : (S : Subgroup N).Characteristic := sylow_characteristic_of_isNilpotent S
  have hnorm : ((S : Subgroup N).map N.subtype).Normal := inferInstance
  have hpg : IsPGroup p ((S : Subgroup N).map N.subtype) := S.isPGroup'.map N.subtype
  have hle : (S : Subgroup N).map N.subtype ≤ fittingRaw G ⊓ N :=
    le_inf (le_fittingRaw_of_isPGroup hp hnorm hpg) (Subgroup.map_subtype_le _)
  have hcard : Nat.card ((S : Subgroup N).map N.subtype)
      = p ^ (Nat.card N).factorization p := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, S.card_eq_multiplicity]
  exact hcard ▸ Subgroup.card_dvd_of_le hle

theorem le_fittingRaw_of_normal_of_isNilpotent {N : Subgroup G} (hN : N.Normal)
    (hnil : Group.IsNilpotent N) : N ≤ fittingRaw G := by
  have h0N : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have h0K : Nat.card (fittingRaw G ⊓ N : Subgroup G) ≠ 0 := Nat.card_pos.ne'
  have hdvd : Nat.card N ∣ Nat.card (fittingRaw G ⊓ N : Subgroup G) := by
    rw [← Nat.factorization_le_iff_dvd h0N h0K]
    refine Finsupp.le_def.2 fun p => ?_
    by_cases hp : p.Prime
    · exact (hp.pow_dvd_iff_le_factorization h0K).1
        (pow_factorization_dvd_natCard_fittingRaw_inf hN hnil hp)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hKeq : (fittingRaw G ⊓ N : Subgroup G) = N :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (Nat.le_of_dvd Nat.card_pos hdvd)
  exact hKeq ▸ inf_le_left

theorem IsCentralSeries.le_fittingRaw {N : Subgroup G} (hN : N.Normal) {X : ℕ → Subgroup N}
    {r : ℕ} (hX : IsCentralSeries X r) : N ≤ fittingRaw G :=
  le_fittingRaw_of_normal_of_isNilpotent hN hX.isNilpotent

theorem isNilpotent_of_le_fittingRaw {N : Subgroup G} (h : N ≤ fittingRaw G) :
    Group.IsNilpotent N :=
  Group.nilpotent_of_mulEquiv (G := (N.subgroupOf (fittingRaw G) : Subgroup (fittingRaw G)))
    (Subgroup.subgroupOfEquivOfLe h)

theorem normal_isNilpotent_iff_le_fittingRaw {N : Subgroup G} (hN : N.Normal) :
    Group.IsNilpotent N ↔ N ≤ fittingRaw G :=
  ⟨le_fittingRaw_of_normal_of_isNilpotent hN, isNilpotent_of_le_fittingRaw⟩

theorem fittingRaw_eq_top_of_isNilpotent (G : Type*) [Group G] [Finite G]
    [Group.IsNilpotent G] : fittingRaw G = ⊤ :=
  eq_top_iff.2 (le_fittingRaw_of_normal_of_isNilpotent (Subgroup.normal_of_characteristic ⊤)
    inferInstance)

end

end CFSG.FeitThompson
