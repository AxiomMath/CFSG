module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH3Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH3Elem
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH3Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResArith
public import CFSG.LieType.Multipliers.U42
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherClassicalSchreier
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.LocalAnalysis.ComponentInitial

namespace CResH3

variable {K : Type} [Field K]

theorem no3A6_of_statedProj (h : UnitaryFieldData 2 1 K) {n : ℕ} (hn1 : 1 ≤ n) (hn5 : n ≤ 5)
    (hgcd : Nat.gcd n (2 ^ 1 + 1) = 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {E : Type} [Group E]
    [Finite E] (e : E ≃* StatedProj (StatedSU n (2 ^ 1) K)) :
    ∀ T : Subgroup E, commutator T = ⊤ → Nat.card T = 1080 → ∀ w ∈ T, orderOf w = 3 →
      (∀ t ∈ T, t * w = w * t) → False := by
  intro T hT hcard w hw hw3 hwc
  have hbot : (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ 1) K) = ⊥ := by
    have h1 := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn1).2.2
    rw [hgcd] at h1
    exact Subgroup.card_eq_one.mp h1
  let pe : StatedProj (StatedSU n (2 ^ 1) K) ≃* StatedSU n (2 ^ 1) K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let ι : E →* Matrix (Fin n) (Fin n) K :=
    (Units.coeHom (Matrix (Fin n) (Fin n) K)).comp
      ((StatedSU n (2 ^ 1) K).subtype.comp (pe.toMonoidHom.comp e.toMonoidHom))
  have hι : Function.Injective ι := fun a b hab =>
    e.injective (pe.injective (Subtype.val_injective (Units.ext hab)))
  have hunit : ∀ g : E, ((ι g).map h.bar).transpose * ι g = 1 := fun g =>
    ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 (pe (e g)).2).2
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) 5 (by rw [hcard]; norm_num)
  refine false_of_perfect_unitary h hn5 hT (ι.comp T.subtype) (hι.comp Subtype.val_injective)
    (fun t => hunit t) (w := ⟨w, hw⟩) (x := x) ?_ ?_ hx
  · rw [Subgroup.orderOf_mk]
    exact hw3
  · intro t
    exact Subtype.ext (hwc t t.2)

end CResH3

theorem card_of_statedClassicalModel_psu_four_two {E : Type} [Group E]
    (hc : StatedClassicalModel E .PSU 4 2 1) : Nat.card E = 25920 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hc

theorem card_of_statedClassicalModel_psu_five_two {E : Type} [Group E]
    (hc : StatedClassicalModel E .PSU 5 2 1) : Nat.card E = 13685760 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hc

theorem eData_U42 {E : Type}
    [Group E] (h : LieModel E .PSU 4 2 1) : EData E := by
  have hc : StatedClassicalModel E .PSU 4 2 1 :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hcard := card_of_statedClassicalModel_psu_four_two hc
  have : IsSimpleGroup E := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity E 4 2 1 hc).2
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hc
  have hU : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  refine eData_of_parts' hcard (by norm_num) (by norm_num) ?_ ?_
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier hc).2
    (CResH3.no3A6_of_statedProj hU (by norm_num) (by norm_num) (by norm_num) hK e)
  · obtain ⟨S₀, hab, h2, hS⟩ := CResH3.exists_elemAb hU (Or.inl rfl) e
    exact ⟨4, ⟨S₀, hab, h2, hS⟩, Or.inl fun p r hp hp2 hdvd => rank_U42 p r hp hp2 (hcard ▸ hdvd)⟩
  · obtain ⟨-, ⟨f⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two E h
    have h2 : Nat.card (CFSG.Open.griessHopfMultiplier E) = 2 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact (Nat.dvd_prime Nat.prime_two).2 (Or.inr h2)

theorem eData_U52
    {E : Type} [Group E] (h : LieModel E .PSU 5 2 1) : EData E := by
  have hc : StatedClassicalModel E .PSU 5 2 1 :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hcard := card_of_statedClassicalModel_psu_five_two hc
  have : IsSimpleGroup E := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity E 5 2 1 hc).2
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hc
  have hU : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  refine eData_of_parts' hcard (by norm_num) (by norm_num) ?_ ?_
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_classical_model_schreier hc).2
    (CResH3.no3A6_of_statedProj hU (by norm_num) (by norm_num) (by norm_num) hK e)
  · obtain ⟨S₀, hab, h2, hS⟩ := CResH3.exists_elemAb hU (Or.inr rfl) e
    exact ⟨4, ⟨S₀, hab, h2, hS⟩, Or.inl fun p r hp hp2 hdvd => rank_U52 p r hp hp2 (hcard ▸ hdvd)⟩
  · obtain ⟨-, ⟨f⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row hc
      (by decide)
    rw [Nat.card_congr f.toEquiv, card_generic_prod_exceptional]
    simp [genericOrders, exceptionalOrders]

end CFSG.EvenSporadicStandard.M24Std
