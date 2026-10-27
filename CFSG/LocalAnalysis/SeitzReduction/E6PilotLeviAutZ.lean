module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAut
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLeviStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

theorem ordA_one_lt_ordA_two {f : ℕ} (hf : 1 ≤ f) :
    CFSG.Open.ordA 1 (2 ^ f) < CFSG.Open.ordA 2 (2 ^ f) := by
  set q := 2 ^ f with hqdef
  have hq : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2 : Finset.Icc 2 (1 + 1) = {2} := by decide
  have h3 : Finset.Icc 2 (2 + 1) = {2, 3} := by decide
  simp only [CFSG.Open.ordA, h2, h3, Finset.prod_singleton, Finset.prod_insert
    (show (2 : ℕ) ∉ ({3} : Finset ℕ) by decide)]
  norm_num
  set A := q * (q ^ 2 - 1) with hA
  have hq2 : 3 ≤ q ^ 2 - 1 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hq3 : 7 ≤ q ^ 3 - 1 := by
    have : 8 ≤ q ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have hA1 : 1 ≤ A := Nat.mul_pos (by omega) (by omega)
  have hB : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = A * (q ^ 2 * (q ^ 3 - 1)) := by
    rw [hA]
    ring
  have hd1 : A / Nat.gcd 2 (q - 1) ≤ A := Nat.div_le_self _ _
  have hd3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (q - 1))
  have hd3' : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hfac : 28 ≤ q ^ 2 * (q ^ 3 - 1) := by
    have : 4 ≤ q ^ 2 := by nlinarith
    calc 28 = 4 * 7 := by norm_num
      _ ≤ q ^ 2 * (q ^ 3 - 1) := Nat.mul_le_mul this hq3
  have hlt : A + 1 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
    rw [Nat.le_div_iff_mul_le hd3', hB]
    calc (A + 1) * Nat.gcd 3 (q - 1) ≤ (A + 1) * 3 := Nat.mul_le_mul_left _ hd3
      _ ≤ A * 28 := by omega
      _ ≤ A * (q ^ 2 * (q ^ 3 - 1)) := Nat.mul_le_mul_left _ hfac
  omega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem highRootSL2_subgroupOf_eq_map_conj_zJ :
    (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) =
      ((zJ K).subgroupOf (adjointGroup .E6 K)).map (MulAut.conj (e6RepConj K 2)).toMonoidHom := by
  rw [← EPilot.map_conj_rootPair_eq_highRootSL2 (K := K) e6RepWeyl_two_smul_alpha2]
  exact subgroupOf_map_conj_eq_map_conj_subgroupOf zJ_le_adjointGroup (e6RepConj K 2)

theorem isSimpleCentralizingFactor_perfectCore_zDLevi (hq : 4 ≤ Nat.card K) :
    IsSimpleCentralizingFactor (perfectCore (zDLevi K))
      ((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)) := by
  set n := e6RepConj K 2 with hn
  set S₀ := (zS K).subgroupOf (adjointGroup .E6 K) with hS₀
  set J₀ := (zJ K).subgroupOf (adjointGroup .E6 K) with hJ₀
  have hJC := zJ_le_adjointGroup (K := K)
  have hSC := zS_le_adjointGroup (K := K)
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_eClasses K
  have hf2 : 2 ≤ f := by
    by_contra h
    have : f = 1 := by omega
    rw [hK, this] at hq
    norm_num at hq
  refine ⟨S₀.map (MulAut.conj n).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [perfectCore_zDLevi_eq hq, zDLevi_eq_conj_zJ_sup_zS, subgroupOf_sup hJC hSC,
      Subgroup.map_sup, highRootSL2_subgroupOf_eq_map_conj_zJ]
  ·
    rw [highRootSL2_subgroupOf_eq_map_conj_zJ, centralizer_map_conj_eq_map_centralizer]
    refine Subgroup.map_mono fun s hs => mem_centralizer_iff.2 fun j hj => ?_
    exact Subtype.ext (mem_centralizer_iff.1 (zS_le_centralizer_zJ (mem_subgroupOf.1 hs)) j
      (mem_subgroupOf.1 hj))
  ·
    have := isSimpleGroup_zS (K := K)
    exact ((S₀.equivMapOfInjective _ (MulAut.conj n).injective).symm.trans
      (subgroupOfEquivOfLe hSC)).isSimpleGroup
  ·
    rw [← map_center_eq ((subgroupOfEquivOfLe hSC).symm.trans
      (S₀.equivMapOfInjective _ (MulAut.conj n).injective)), center_zS_eq_bot, Subgroup.map_bot]
  ·
    rw [highRootSL2_subgroupOf_eq_map_conj_zJ, card_map_of_injective (MulAut.conj n).injective,
      card_map_of_injective (MulAut.conj n).injective,
      Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv,
      F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) (lieModel_zJ hK hf2),
      F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) (lieModel_zS hK)]
    exact ordA_one_lt_ordA_two hf

variable (K) in
@[expose] noncomputable def f5Levi : Fin 3 → Subgroup (adjointGroup .E6 K) :=
  ![EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1), yLevi K, perfectCore (zDLevi K)]

theorem factF5_E6_f5Levi (hq : 4 ≤ Nat.card K) (κ κ' : Fin 3) (ι : f5Levi K κ ≃* f5Levi K κ') :
    κ = κ' ∧ ∃ m ∈ f5Levi K κ',
      ((((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)).subgroupOf (f5Levi K κ)).map
          ι.toMonoidHom).map (f5Levi K κ').subtype =
        ((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)).map
          (MulAut.conj m).toMonoidHom :=
  factF5_E6 rfl rfl (isSimpleCentralizingFactor_perfectCore_zDLevi hq) κ κ' ι

theorem exists_map_eq_map_conj_f5Levi (hq : 4 ≤ Nat.card K) (κ κ' : Fin 3)
    (ι : f5Levi K κ ≃* f5Levi K κ') :
    ∃ c : adjointGroup .E6 K,
      ((((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)).subgroupOf (f5Levi K κ)).map
          ι.toMonoidHom).map (f5Levi K κ').subtype =
        ((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)).map
          (MulAut.conj c).toMonoidHom := by
  obtain ⟨-, m, -, hm⟩ := factF5_E6_f5Levi hq κ κ' ι
  exact ⟨m, hm⟩

end CFSG.SeitzReduction.E6Pilot
