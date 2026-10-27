module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SylowNormalizerComplementGeneration
import CFSG.FeitThompson.Local.BlackburnCoprimeCentralProduct
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open scoped commutatorElement

universe u

variable {G : Type*} [Group G]

private def conjHom (R : Subgroup G) {V : Subgroup G} (hVn : V ≤ normalizer (R : Set G)) :
    ↥V →* MulAut ↥R :=
  R.normalizerMonoidHom.comp (Subgroup.inclusion hVn)

private theorem coe_conjHom_apply (R : Subgroup G) {V : Subgroup G}
    (hVn : V ≤ normalizer (R : Set G)) (a : ↥V) (x : ↥R) :
    ((conjHom R hVn a x : ↥R) : G) = (a : G) * (x : G) * (a : G)⁻¹ := (rfl)

private theorem map_closure_displacement (R : Subgroup G) {V : Subgroup G}
    (hVn : V ≤ normalizer (R : Set G)) :
    Subgroup.map R.subtype
        (closure {y : ↥R | ∃ (x : ↥R) (a : ↥V), x⁻¹ * conjHom R hVn a x = y}) = ⁅R, V⁆ := by
  rw [MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext g
  constructor
  · rintro ⟨y, ⟨x, a, rfl⟩, rfl⟩
    refine ⟨(x : G)⁻¹, R.inv_mem x.2, (a : G), a.2, ?_⟩
    simp only [coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjHom_apply,
      commutatorElement_def]
    group
  · rintro ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    refine ⟨(⟨g₁⁻¹, R.inv_mem hg₁⟩ : ↥R)⁻¹ * conjHom R hVn ⟨g₂, hg₂⟩ ⟨g₁⁻¹, R.inv_mem hg₁⟩,
      ⟨_, _, rfl⟩, ?_⟩
    simp only [coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjHom_apply,
      commutatorElement_def]
    group

private theorem map_center_eq_range_inf_centralizer {H : Type*} [Group H]
    (f : H →* G) (hf : Function.Injective f) :
    Subgroup.map f (center H) = f.range ⊓ centralizer (f.range : Set G) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, mem_centralizer_iff.2 ?_⟩
    rintro z ⟨w, rfl⟩
    rw [← map_mul, ← map_mul, mem_center_iff.1 hy w]
  · rintro x ⟨⟨y, rfl⟩, hcent⟩
    refine ⟨y, mem_center_iff.2 fun w => hf ?_, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.1 hcent (f w) ⟨w, rfl⟩

theorem FPL_low_rank_sylow_central_product
    (h₁ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FPL_low_rank_sylow_central_product.{u} := by
  intro G _ _ hG p hp hpodd R hRsyl hrank hRnab
  have := Fact.mk hp
  have : Finite G := Finite.of_fintype G
  have hRne : R ≠ ⊥ := by
    rintro rfl
    exact hRnab (IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _)
  obtain ⟨-, hRcard⟩ := hRsyl
  rw [Subgroup.card_top] at hRcard
  have hRp : IsPGroup p ↥R := IsPGroup.of_card hRcard
  obtain ⟨⟨V, hVL, hVp, hVidx⟩, hall⟩ :=
    FPL_global_sylow_complement_generation h₁ G hG p hp R hRne ⟨le_top, by
      rw [Subgroup.card_top]; exact hRcard⟩ (normalizer (R : Set G)) rfl
  obtain ⟨-, -, hcomm, -⟩ := hall V hVL hVp hVidx
  have hVn : V ≤ normalizer (R : Set G) := hVL
  have hgen : closure {y : ↥R | ∃ (x : ↥R) (a : ↥V), x⁻¹ * conjHom R hVn a x = y} = ⊤ :=
    Subgroup.map_injective R.subtype_injective (by
      rw [map_closure_displacement, hcomm, ← MonoidHom.range_eq_map, range_subtype])
  have hVodd : Odd (Nat.card ↥V) := Odd.of_dvd_nat hG.odd (Subgroup.card_subgroup_dvd_card V)
  have hVcop : (Nat.card ↥V).Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hVp).symm
  have h3 : 3 ∉ elementaryAbelianRanks p ↥R :=
    (elementaryAbelianPRank_le_two_iff hp.one_lt).1 hrank
  obtain ⟨-, B₀, C₀, hsup, hB₀nab, hB₀card, hB₀exp, hC₀nt, hC₀cyc, hC₀Z,
    hinf, hZtors, hZcard⟩ :=
    three_lt_and_exists_central_product hp hpodd hRp hRnab h3 hVodd hVcop (conjHom R hVn) hgen
  have hcompinj : Function.Injective (R.subtype.comp B₀.subtype) := by
    rw [MonoidHom.coe_comp]
    exact R.subtype_injective.comp B₀.subtype_injective
  have hrangecomp : (R.subtype.comp B₀.subtype).range = Subgroup.map R.subtype B₀ := by
    rw [MonoidHom.range_comp, range_subtype]
  have hZmap : Subgroup.map R.subtype (Subgroup.map B₀.subtype (center ↥B₀))
      = Subgroup.map R.subtype B₀
        ⊓ centralizer ((Subgroup.map R.subtype B₀ : Subgroup G) : Set G) := by
    rw [Subgroup.map_map, map_center_eq_range_inf_centralizer _ hcompinj, hrangecomp]
  refine ⟨Subgroup.map R.subtype B₀, Subgroup.map R.subtype C₀,
    Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, range_subtype]
  ·
    rw [← hB₀card]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective B₀ _ R.subtype_injective).toEquiv).symm
  ·
    intro hc
    have e := Subgroup.equivMapOfInjective B₀ R.subtype R.subtype_injective
    exact hB₀nab (IsMulCommutative.of_comm fun a b => e.injective (by
      rw [map_mul, map_mul]; exact isMulCommutative_iff.1 hc _ _))
  ·
    rintro b ⟨y, hy, rfl⟩
    rw [coe_subtype, ← Subgroup.coe_pow, hB₀exp y hy, Subgroup.coe_one]
  ·
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective]
    exact (Subgroup.nontrivial_iff_ne_bot C₀).1 hC₀nt
  ·
    exact (Subgroup.equivMapOfInjective C₀ R.subtype R.subtype_injective).isCyclic.1 hC₀cyc
  ·
    calc Subgroup.map R.subtype C₀ ≤ Subgroup.map R.subtype (center ↥R) :=
          Subgroup.map_mono hC₀Z
    _ = R ⊓ centralizer (R : Set G) := by
          rw [map_center_eq_range_inf_centralizer _ R.subtype_injective, range_subtype]
  ·
    rw [← Subgroup.map_inf _ _ _ R.subtype_injective, hinf, hZmap]
  ·
    rw [← Subgroup.map_inf _ _ _ R.subtype_injective, hinf, Subgroup.coe_map]
    ext g
    simp only [Set.mem_image, coe_subtype, Set.mem_ofPred_eq, hZtors, Subgroup.mem_map]
    constructor
    · rintro ⟨x, ⟨hxC, hxp⟩, rfl⟩
      exact ⟨⟨x, hxC, rfl⟩, by rw [← Subgroup.coe_pow, hxp, Subgroup.coe_one]⟩
    · rintro ⟨⟨x, hxC, rfl⟩, hgp⟩
      refine ⟨x, ⟨hxC, ?_⟩, rfl⟩
      exact R.subtype_injective (by
        rw [coe_subtype, Subgroup.coe_pow, Subgroup.coe_one]
        simpa using hgp)
  ·
    rw [← Subgroup.map_inf _ _ _ R.subtype_injective, hinf, ← hZcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ R.subtype_injective).toEquiv).symm

end

end CFSG.FeitThompson.Proofs
