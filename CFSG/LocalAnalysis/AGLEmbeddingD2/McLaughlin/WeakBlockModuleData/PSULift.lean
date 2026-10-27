module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSULift

public section

namespace CFSG.AGLEmbedding

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PerfectCover

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_lift_su_compat_three (hGA : CFSG.Open.GriessAllModelsStatement)
    (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ} (hn : 4 ≤ n) (h3n : 3 ∣ n) {X : Type} [Group X]
    [Finite X] (hc : StatedClassicalModel X .PSU n 2 1) (hX : Subgroup.center X = ⊥)
    (π : SU (unitaryInvolution F 2 1) n →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 1) n))
    {E : Type} [Group E] [Finite E] (hE : Group.IsPerfect E) (p : E →* X)
    (hp : Function.Surjective p) (hk : p.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 p.ker)
    (hkc : Nat.card p.ker = 3) :
    ∃ α : SU (unitaryInvolution F 2 1) n →* E, Function.Surjective α ∧ p.comp α = π ∧
      Nat.Coprime 3 (Nat.card α.ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨e, he16, hcard⟩ := card_hopfMultiplier_of_model_psu_two hGA hc
  have hperf : Group.IsPerfect (SU (unitaryInvolution F 2 1) n) :=
    (isQuasisimple_SU (n := n) hF (by omega) (fun h => by simp at h; omega)).1
  obtain ⟨z, hzc, hz3⟩ := exists_mem_center_orderOf_eq_three hF h3n (by omega)
  have hzker : z ∈ π.ker := by
    have : π z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨w, rfl⟩ := hπ w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hzc w]
    rw [hX, Subgroup.mem_bot] at this
    exact this
  have h3k : 3 ∣ Nat.card π.ker := by
    have := Subgroup.orderOf_dvd_natCard π.ker hzker
    rwa [hz3] at this
  obtain ⟨m, hm⟩ := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hperf π hπ hker
  have hcard' : Nat.card (hopfMultiplier X) = 3 * e := by rw [hcard, Nat.gcd_eq_right h3n]
  obtain ⟨t, ht⟩ := h3k
  have hem : e = t * m := by
    have : 3 * e = 3 * (t * m) := by rw [← hcard', hm, ht]; ring
    omega
  have hm3 : Nat.Coprime 3 m := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hm3'
    have : 3 ∣ e := hem ▸ Dvd.dvd.mul_left hm3' t
    have := this.trans he16
    norm_num at this
  have ht3 : Nat.Coprime 3 t := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    have : 3 ∣ e := hem ▸ Dvd.dvd.mul_right h m
    have := this.trans he16
    norm_num at this
  obtain ⟨α, hα, hcomp⟩ := exists_lift_of_coprime_multiplier_index hperf hE π hπ hker p hp hk
    Nat.prime_three h3 m hm3 hm
  refine ⟨α, hα, hcomp, ?_⟩
  have hK1 : Nat.card (SU (unitaryInvolution F 2 1) n) = Nat.card X * Nat.card π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]
  have hK2 : Nat.card (SU (unitaryInvolution F 2 1) n) = Nat.card E * Nat.card α.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv]
  have hE1 : Nat.card E = Nat.card X * Nat.card p.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup p.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective p hp).toEquiv]
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have : Nat.card X * (3 * t) = Nat.card X * (3 * Nat.card α.ker) := by
    rw [← ht, ← hK1, hK2, hE1, hkc]; ring
  have hker_eq : Nat.card α.ker = t := by
    have := Nat.eq_of_mul_eq_mul_left hXpos this
    omega
  rw [hker_eq]
  exact ht3

end CFSG.AGLEmbedding
