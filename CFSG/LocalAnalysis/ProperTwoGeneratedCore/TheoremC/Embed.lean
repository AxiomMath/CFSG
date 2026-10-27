module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Statement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.EmbedRestrict
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneComponent

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ShultStronglyClosedTI

variable {X : Type} [Group X] [Finite X] {Y : Subgroup X} {u z : X} {P : Sylow 2 X}
  {J : Subgroup X}

namespace HighRankCaseTwo

theorem twoCore_le_point (hJ : HighRankCaseTwo Y u z P J) : CFSG.Open.pCore 2 X ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((twoCore_isPGroup X).le_sylow_of_normal P).trans hJ.sylow_le

theorem twoCore_subgroupOf_le_center (hJ : HighRankCaseTwo Y u z P J) :
    (CFSG.Open.pCore 2 X).subgroupOf J ≤ Subgroup.center J := by
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hJ.component.1
      (inferInstance : ((CFSG.Open.pCore 2 X).subgroupOf J).Normal) with h | h
  · exact absurd ((Subgroup.subgroupOf_eq_top.mp h).trans hJ.twoCore_le_point) hJ.not_le
  · exact h

theorem center_le_twoCore_subgroupOf (hc : CoreConfig Y u z) (hJ : HighRankCaseTwo Y u z P J) :
    Subgroup.center J ≤ (CFSG.Open.pCore 2 X).subgroupOf J := by
  intro c hcZ
  have h := (component_center_le_twoCore hc.oddCore_eq_bot hJ.component).2
    (Subgroup.mem_map_of_mem J.subtype hcZ)
  exact h

theorem twoCore_subgroupOf_eq_center (hc : CoreConfig Y u z) (hJ : HighRankCaseTwo Y u z P J) :
    (CFSG.Open.pCore 2 X).subgroupOf J = Subgroup.center J :=
  le_antisymm hJ.twoCore_subgroupOf_le_center (hJ.center_le_twoCore_subgroupOf hc)

theorem le_normalClosure_lever (hc : CoreConfig Y u z) (hJ : HighRankCaseTwo Y u z P J) :
    J ≤ Subgroup.normalClosure ({z} : Set X) := by
  rcases CFSG.LocalAnalysis.ComponentInitial.component_normal_subgroup hJ.component
      (inferInstance : (Subgroup.normalClosure ({z} : Set X)).Normal) with h | h
  · exact h
  · refine absurd (le_trans (fun j hj => ?_) hc.lever_centralizer_le) hJ.not_le
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hjc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hj
    exact ((Subgroup.mem_centralizer_iff.mp hjc) z (Subgroup.subset_normalClosure rfl)).symm

theorem exists_involution_not_mem_twoCore (hc : CoreConfig Y u z)
    (hJ : HighRankCaseTwo Y u z P J) :
    ∃ w ∈ Y, w ∈ J ∧ orderOf w = 2 ∧ w ∉ CFSG.Open.pCore 2 X := by
  rcases hJ.lever with hzJ | ⟨-, -, -, t, ⟨htP, htJ⟩, ht2, ⟨c, hcJ, hct⟩, -⟩
  · refine ⟨z, hc.lever_mem, hzJ, hc.lever_order, fun hzQ => hJ.not_le ?_⟩
    have hzc : (⟨z, hzJ⟩ : J) ∈ Subgroup.center J := hJ.twoCore_subgroupOf_le_center hzQ
    refine le_trans (fun j hj => ?_) hc.lever_centralizer_le
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨j, hj⟩)
  · refine ⟨t, hJ.sylow_le htP, htJ, ht2, fun htQ => hct ?_⟩
    have htc : (⟨t, htJ⟩ : J) ∈ Subgroup.center J := hJ.twoCore_subgroupOf_le_center htQ
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp htc ⟨c, hcJ⟩)

theorem quotient_centralSylow (hJ : HighRankCaseTwo Y u z P J) :
    InvolutionPointCentralSylow (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π := QuotientGroup.mk' (CFSG.Open.pCore 2 X)
  let S : Sylow 2 (X ⧸ CFSG.Open.pCore 2 X) := P.mapSurjective (QuotientGroup.mk'_surjective _)
  have hS : (S : Subgroup (X ⧸ CFSG.Open.pCore 2 X)) = (P : Subgroup X).map π :=
    Sylow.coe_mapSurjective _ _
  have hzS : π z ∈ (S : Subgroup (X ⧸ CFSG.Open.pCore 2 X)) := by
    rw [hS]
    exact Subgroup.mem_map_of_mem π hJ.lever_mem
  refine ⟨S, hzS, Subgroup.mem_center_iff.mpr fun s => Subtype.ext ?_⟩
  have hs : (s : X ⧸ CFSG.Open.pCore 2 X) ∈ (P : Subgroup X).map π := hS ▸ s.2
  obtain ⟨p, hp, hps⟩ := Subgroup.mem_map.mp hs
  change (s : X ⧸ CFSG.Open.pCore 2 X) * π z = π z * s
  rw [← hps, ← map_mul, ← map_mul, (hJ.lever_comm p hp).eq]

theorem quotient_le_hull (hc : CoreConfig Y u z) (hJ : HighRankCaseTwo Y u z P J) :
    J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) ≤
      involutionPointHull (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z) := by
  rw [minimalLocalFailure_hull_eq_normalClosure, ← Set.image_singleton]
  exact (Subgroup.map_mono (hJ.le_normalClosure_lever hc)).trans
    (Subgroup.map_normalClosure_le _ _)

theorem quotient_not_le (hJ : HighRankCaseTwo Y u z P J) :
    ¬ J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) ≤
      Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) := by
  intro h
  apply hJ.not_le
  have h' := Subgroup.map_le_iff_le_comap.mp h
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hJ.twoCore_le_point] at h'

theorem quotient_even_card (hc : CoreConfig Y u z) (hJ : HighRankCaseTwo Y u z P J) :
    Even (Nat.card ((Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X))).subgroupOf
      (J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X))))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hwY, hwJ, hw2, hwQ⟩ := hJ.exists_involution_not_mem_twoCore hc
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 X)
  have hw2' : w ^ 2 = 1 := hw2 ▸ pow_orderOf_eq_one w
  have hπw : orderOf (π w) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hw2', map_one]
    · rw [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hwQ
  let w' : J.map π := ⟨π w, Subgroup.mem_map_of_mem π hwJ⟩
  have hw' : orderOf w' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hπw
  have h := Subgroup.orderOf_dvd_natCard ((Y.map π).subgroupOf (J.map π))
    (x := w') (Subgroup.mem_map_of_mem π hwY)
  rw [hw'] at h
  exact even_iff_two_dvd.mpr h

theorem ker_subgroupMap_eq_center (hc : CoreConfig Y u z) (hJ : HighRankCaseTwo Y u z P J) :
    ((QuotientGroup.mk' (CFSG.Open.pCore 2 X)).subgroupMap J).ker = Subgroup.center J := by
  rw [← hJ.twoCore_subgroupOf_eq_center hc]
  ext j
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← OneMemClass.coe_eq_one]
  change QuotientGroup.mk' _ (j : X) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem map_subgroupMap_eq (hJ : HighRankCaseTwo Y u z P J) :
    (Y.subgroupOf J).map ((QuotientGroup.mk' (CFSG.Open.pCore 2 X)).subgroupMap J) =
      (Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X))).subgroupOf
        (J.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X))) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact Subgroup.mem_map_of_mem _ hj
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨j, rfl⟩ := MonoidHom.subgroupMap_surjective _ J x
    refine ⟨j, ?_, rfl⟩
    have h : y⁻¹ * (j : X) ∈ CFSG.Open.pCore 2 X := QuotientGroup.eq.mp hyx
    have h' := Y.mul_mem hy (hJ.twoCore_le_point h)
    rwa [mul_inv_cancel_left] at h'

end HighRankCaseTwo

theorem highRankStrongEmbedding (h2 : TheoremTwo) (hloc : QuotientLocalEmbedding) :
    HighRankStrongEmbedding := by
  intro X _ _ Y u z P J IH hc hJ
  have hT := h2 (X ⧸ CFSG.Open.pCore 2 X) _ _ (hloc X Y u z IH hc) hJ.quotient_centralSylow
  have hres := fusionStronglyEmbedded_subgroupOf_of_le (hJ.quotient_le_hull hc) hT
    hJ.quotient_not_le (hJ.quotient_even_card hc)
  rw [← hJ.map_subgroupMap_eq] at hres
  exact fusionStronglyEmbedded_map_of_ker_eq (MonoidHom.subgroupMap_surjective _ J)
    (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk', hJ.ker_subgroupMap_eq_center hc]) hres

end CFSG.ProperTwoGeneratedCore.TheoremC
