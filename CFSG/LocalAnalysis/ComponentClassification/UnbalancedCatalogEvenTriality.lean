module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Chevalley.GraphFixedNoncentralSolvable
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace EvenCatalog

abbrev trialityOrbit : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩

theorem card_trialityOrbit : (TwistTag.D4.orbit trialityOrbit).card = 3 := by decide

variable {K : Type} [Field K]

theorem mem_orbitField_trialityOrbit {σ : K ≃+* K} (hσ : σ ^ 3 = 1) (x : K) :
    x ∈ orbitField TwistTag.D4 K σ.toRingHom trialityOrbit := by
  rw [mem_orbitField, card_trialityOrbit]
  change (σ ^ 3) x = x
  rw [hσ]
  rfl

end EvenCatalog

open EvenCatalog

theorem even_triality_root_group_odd_core (K : Type) [Field K] [Finite K] (hK : ringChar K = 2)
    (σ : K ≃+* K) (hσ : orderOf σ = 3) :
    CFSG.oddCore (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ := by
  have : CharP K 2 := hK ▸ ringChar.charP K
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set a := trialityOrbit
  set L := orbitField TwistTag.D4 K σ.toRingHom a
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨x, hx⟩ : ∃ x : K, σ x ≠ x := by
    by_contra h
    push Not at h
    have h1 : σ = 1 := RingEquiv.ext h
    rw [h1, orderOf_one] at hσ
    omega
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (map_zero σ)
  have hx1 : x ≠ 1 := by rintro rfl; exact hx (map_one σ)
  set t : L := ⟨x, mem_orbitField_trialityOrbit hσ3 x⟩
  have ht0 : t ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have ht2 : t ^ 2 ≠ 1 := by
    intro h
    have h' : x ^ 2 = 1 := congrArg Subtype.val h
    have h'' : (x + 1) ^ 2 = 0 := by
      have e : (x + 1) ^ 2 = x ^ 2 + 1 + 2 * x := by ring
      rw [e, h', CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
    exact hx1 (by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h''
      rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at this)
  have hperf : commutator (SL2 L) = ⊤ := Matrix.SL2.commutator_eq_top ht0 ht2
  obtain ⟨ρ, hρu, -, -, -, -, hρrange, hle, -, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom a
  have hρC : ∀ g, ρ g ∈ C := fun g => hle (hρrange ▸ ⟨g, rfl⟩)
  set ρ' : SL2 L →* C := ρ.codRestrict C hρC
  set z : C := ρ' (uSL 1)
  have hz : (z : ModGL TwistTag.D4.tag K) = orbitX TwistTag.D4 K σ.toRingHom a 1 := hρu 1
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : orbitX TwistTag.D4 K σ.toRingHom a 1 = orbitX TwistTag.D4 K σ.toRingHom a 0 := by
      rw [orbitX_zero]
      exact Subtype.ext (by rw [← hz, h]; rfl)
    exact one_ne_zero (orbitX_injective σ.toRingHom a h1)
  have hz2 : z ^ 2 = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, hz, Subgroup.coe_one, sq, ← Subgroup.coe_mul, ← orbitX_add,
      CharTwo.add_self_eq_zero, orbitX_zero, Subgroup.coe_one]
  by_contra hne
  set R := CFSG.oddCore C
  have hnc : ¬ R ≤ Subgroup.center C := by
    rw [exceptional_fixed_center_trivial TwistTag.D4 K σ, le_bot_iff]
    exact hne
  have hsolv := fixed_noncentral_normal_solvable_quotient TwistTag.D4 K σ R hnc
  have hzR : z ∈ R := by
    have h := map_eq_one_of_commutator_eq_top hperf ((QuotientGroup.mk' R).comp ρ') (uSL 1)
    rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact not_mem_oddCore_of_sq_eq_one hz1 hz2 hzR

end CFSG.ComponentClassification.UnbalancedCatalog
