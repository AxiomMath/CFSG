module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourHsylBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveFamily
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaThreeFamily

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedProj StatedScalars)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (singularSubspaces flag Xstar)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus reindexVectorEquiv reindexQuadraticForm_map
    regular_coordinateQuadPlus projectivePointFamily)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedPointFamily statedDerivedReindexEquiv_symm_vector)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (statedProjectiveSubspaceStabilizer mem_statedProjectiveSubspaceStabilizer_mk
    mem_statedDerivedSubspaceStabilizer)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (stated_pointFamily_orbit_subset plusCoordinateEquiv plusCoordinate_pointFamily
    familyTransport_automorphism automorphismTransport_symm_apply)
open CFSG.ComponentClassification.UnbalancedCatalog.ThreeFamily
  (conjugacyFamily_eq_image statedPointFamily_eq_image)
open scoped Pointwise

section Bridge

variable {F : Type} [Field F] [CharP F 2] {m : ℕ}

theorem toLinEquiv_statedOmegaPlusEquiv_symm_projHom (hm : 1 ≤ m)
    (u : orthDerived (coordinateQuadPlus m F)) (x : Fin m ⊕ Fin m → F) :
    toLinEquiv (Fin m ⊕ Fin m) F
        (((statedOmegaPlusEquiv F m hm).symm (projHom _ u) : StatedOmega (StatedQuadPlus m F)) :
          GL (Fin m ⊕ Fin m) F) x =
      (reindexVectorEquiv (K := F) (plusIndexEquiv m)).symm
        ((u : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F))
          (reindexVectorEquiv (plusIndexEquiv m) x)) := by
  have hsymm : (statedOmegaPlusEquiv F m hm).symm (projHom _ u) =
      (statedDerivedPlusEquiv F m).symm ((derivedEquiv _).symm u) := by
    rw [MulEquiv.symm_apply_eq]
    simp only [statedOmegaPlusEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  rw [hsymm]
  have h := statedDerivedReindexEquiv_symm_vector (plusIndexEquiv m) (quadPlus m F)
    (coe_quadPlus m F) ((derivedEquiv _).symm u) (reindexVectorEquiv (plusIndexEquiv m) x)
  rw [LinearEquiv.symm_apply_apply] at h
  refine h.trans ?_
  congr 1
  have h1 := coe_derivedEquiv (coordinateQuadPlus m F) ((derivedEquiv _).symm u)
  rw [MulEquiv.apply_symm_apply] at h1
  rw [h1]
  rfl

omit [CharP F 2] in
theorem polar_coordinateQuadPlus_reindex (x y : Fin m ⊕ Fin m → F) :
    polar (coordinateQuadPlus m F) (reindexVectorEquiv (plusIndexEquiv m) x)
        (reindexVectorEquiv (plusIndexEquiv m) y) = polar (quadPlus m F) x y := by
  have h : ∀ v, coordinateQuadPlus m F (reindexVectorEquiv (plusIndexEquiv m) v) =
      quadPlus m F v := reindexQuadraticForm_map (plusIndexEquiv m) (quadPlus m F)
  simp only [polar, ← map_add, h]

end Bridge

section Stated

variable {K : Type} [Field K] [Finite K]

theorem exists_two_ne_of_ne_fin_four {a k : Fin 4} (hak : a ≠ k) :
    ∃ b c : Fin 4, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ b ≠ k ∧ c ≠ k := by
  revert a k
  decide

omit [Finite K] in
theorem span_single_inl_mem_singularSubspaces {n : ℕ} (a : Fin n) :
    (K ∙ (Pi.single (Sum.inl a) 1 : Fin n ⊕ Fin n → K)) ∈ singularSubspaces (quadPlus n K) 1 := by
  refine ⟨finrank_span_singleton ?_, fun x hx => ?_⟩
  · intro h
    have := congrFun h (Sum.inl a)
    simp at this
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [QuadraticMap.map_smul, (isHypCoord_quadPlus (K := K) a).map_left, smul_zero]

theorem stated_smul_pointFamily_eq_of_fix {a k : Fin 4} (hak : a ≠ k)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
    (hfix : ∀ u w : Fin 4 ⊕ Fin 4 → K, quadPlus 4 K u = 0 → quadPlus 4 K w = 0 →
      polar (quadPlus 4 K) u w = 0 → u (.inl k) = 0 → u (.inr k) = 0 → u (.inr a) = 0 →
      w (.inl k) = 0 → w (.inr k) = 0 → w (.inr a) = 0 →
      ∃ g : StatedOmega (StatedQuadPlus 4 K),
        (∀ x, toLinEquiv _ K (g : GL (Fin 4 ⊕ Fin 4) K) x =
          x + polar (quadPlus 4 K) x u • w - polar (quadPlus 4 K) x w • u) ∧
        β (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ g) :
    β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  classical
  obtain ⟨b, c, hab, hac, hbc, hbk, hck⟩ := exists_two_ne_of_ne_fin_four hak
  by_contra hne
  obtain ⟨-, -, hsX, hsXs, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.orthogonal_geometry_split_maximal_family_orbits
      (K := K) (r := 4) (by norm_num)
  have hO := stated_pointFamily_orbit_subset (K := K) (n := 4) rfl (MulAction.mem_orbit _ β)
  have hsol : ∀ U ∈ β • statedPointFamily (coe_quadPlus 4 K),
      ∃ M ∈ singularSubspaces (quadPlus 4 K) 4,
        U = statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) M := by
    rcases hO with h | h | h
    · exact absurd h hne
    · intro U hU
      rw [h, conjugacyFamily_eq_image (by norm_num)] at hU
      obtain ⟨M, hM, rfl⟩ := hU
      exact ⟨M, hsX hM, rfl⟩
    · intro U hU
      rw [h, conjugacyFamily_eq_image (by norm_num)] at hU
      obtain ⟨M, hM, rfl⟩ := hU
      exact ⟨M, hsXs hM, rfl⟩
  set L₀ : Submodule K (Fin 4 ⊕ Fin 4 → K) := K ∙ (Pi.single (Sum.inl a) 1) with hL₀
  have hL₀s := span_single_inl_mem_singularSubspaces (K := K) a
  set H := statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) L₀ with hH
  have hHF : H ∈ statedPointFamily (coe_quadPlus 4 K) := by
    rw [statedPointFamily_eq_image]
    exact ⟨L₀, hL₀s, rfl⟩
  obtain ⟨M, hM, hMH⟩ := hsol (β • H) (Set.smul_mem_smul_set hHF)
  refine false_of_invariant_solid_quadPlus hab hac hak hbc hbk hck hM.1 hM.2 ?_
  intro u w hu hw huw huk huk' hua hwk hwk' hwa x hx
  obtain ⟨g, hg, hβg⟩ := hfix u w hu hw huw huk huk' hua hwk hwk' hwa
  have hga : toLinEquiv _ K (g : GL (Fin 4 ⊕ Fin 4) K) (Pi.single (Sum.inl a) 1) =
      Pi.single (Sum.inl a) 1 := by
    rw [hg, polar_comm, (isHypCoord_quadPlus a).polar_left, polar_comm,
      (isHypCoord_quadPlus a).polar_left, hua, hwa, zero_smul, zero_smul, add_zero, sub_zero]
  have hgH : QuotientGroup.mk' _ g ∈ H := by
    rw [hH, mem_statedProjectiveSubspaceStabilizer_mk, mem_statedDerivedSubspaceStabilizer, hL₀,
      Submodule.map_span, Set.image_singleton]
    exact congrArg (fun v => K ∙ v) hga
  have hgM : QuotientGroup.mk' _ g ∈ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) M := by
    rw [← hMH]
    have h := Subgroup.smul_mem_pointwise_smul (QuotientGroup.mk' _ g) β H hgH
    rwa [MulAut.smul_def, hβg] at h
  rw [mem_statedProjectiveSubspaceStabilizer_mk, mem_statedDerivedSubspaceStabilizer] at hgM
  rw [← hg, ← hgM]
  exact Submodule.mem_map_of_mem hx

end Stated

section Coordinate

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_image_of_fix_pairPerp_four (k : Fin 4)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hD : ∀ x ∈ pairPerp (K := K) k, β x = x) :
    β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  obtain ⟨a, hak⟩ := exists_ne k
  rw [mem_image_iff_smul_pointFamily le_rfl]
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  set ψ := plusCoordinateEquiv 4 K with hψ
  set βs := (MulAut.congr ψ).symm β with hβs
  have hβ : MulAut.congr ψ βs = β := MulEquiv.apply_symm_apply _ _
  have hs : βs • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
    refine stated_smul_pointFamily_eq_of_fix hak βs ?_
    intro u w hu hw huw huk huk' hua hwk hwk' hwa
    set r := reindexVectorEquiv (K := K) (plusIndexEquiv 4) with hr
    have hu' : coordinateQuadPlus 4 K (r u) = 0 :=
      (reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K) u).trans hu
    have hw' : coordinateQuadPlus 4 K (r w) = 0 :=
      (reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K) w).trans hw
    have huw' : polar (coordinateQuadPlus 4 K) (r u) (r w) = 0 := by
      rw [hr, polar_coordinateQuadPlus_reindex]
      exact huw
    set e : orthDerived (coordinateQuadPlus 4 K) :=
      ⟨eichler _ (r u) (r w), eichler_mem_orthDerived hQ hT _ _⟩ with he
    refine ⟨(statedOmegaPlusEquiv K 4 (by norm_num)).symm (projHom _ e), fun x => ?_, ?_⟩
    · rw [toLinEquiv_statedOmegaPlusEquiv_symm_projHom]
      change r.symm (eichler _ (r u) (r w) (r x)) = _
      rw [eichler_apply hu' huw', hw', zero_mul, add_zero, hr, polar_coordinateQuadPlus_reindex,
        polar_coordinateQuadPlus_reindex, ← map_smul, ← map_smul, ← map_add, ← map_sub,
        LinearEquiv.symm_apply_apply]
    · have hmk : ψ (QuotientGroup.mk' _ ((statedOmegaPlusEquiv K 4 (by norm_num)).symm
          (projHom _ e))) = projHom _ e := by
        rw [hψ, plusCoordinateEquiv_mk 4 K (by norm_num), MulEquiv.apply_symm_apply]
      have hePerp : projHom _ e ∈ pairPerp (K := K) k := by
        refine ⟨e, mem_subgroupOf.mpr ((isHypCoord_coordinateQuadPlus k).eichler_mem_stabSub
          ⟨?_, ?_⟩ ⟨?_, ?_⟩), rfl⟩ <;>
          rw [hr, CFSG.ComponentClassification.CatalogueBOrthogonalPointData.reindexVectorEquiv_apply,
            Equiv.symm_apply_apply]
        · exact huk
        · exact huk'
        · exact hwk
        · exact hwk'
      rw [hβs, automorphismTransport_symm_apply, hmk, hD _ hePerp]
      exact ψ.symm_apply_eq.mpr hmk.symm
  have h1 := familyTransport_automorphism ψ (statedPointFamily (coe_quadPlus 4 K)) βs
  rw [hs, hβ, plusCoordinate_pointFamily] at h1
  exact h1.symm

theorem exists_mem_pairTorus_eq_conj_four (hq : 3 ≤ Nat.card K) (k : Fin 4)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hX : ∀ x ∈ pairTorus (K := K) k, β x = x) (hD : ∀ x ∈ pairPerp (K := K) k, β x = x) :
    ∃ x ∈ pairTorus (K := K) k, β = MulAut.conj x := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by norm_num : 3 ≤ 4) k
  exact exists_mem_pairTorusOf_eq_conj (regular_coordinateQuadPlus 4 K (by norm_num)).1
    (isHypCoord_coordinateQuadPlus k) (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hik.symm) (pairDisjoint_plus hjk.symm)
    (pairDisjoint_plus hij) hq (mem_image_of_fix_pairPerp_four k hD) hX hD

theorem eq_one_of_two_pow_fix_pairTorus_four (hq : 3 ≤ Nat.card K) (k : Fin 4)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))} {m : ℕ} (hβ : β ^ 2 ^ m = 1)
    (hX : ∀ x ∈ pairTorus (K := K) k, β x = x) (hD : ∀ x ∈ pairPerp (K := K) k, β x = x) :
    β = 1 := by
  obtain ⟨i, j, hik, hjk, hij⟩ := exists_two_ne (by norm_num : 3 ≤ 4) k
  exact eq_one_of_two_pow_fix_pairTorusOf (regular_coordinateQuadPlus 4 K (by norm_num)).1
    (isHypCoord_coordinateQuadPlus k) (isHypCoord_coordinateQuadPlus i)
    (isHypCoord_coordinateQuadPlus j) (pairDisjoint_plus hik.symm) (pairDisjoint_plus hjk.symm)
    (pairDisjoint_plus hij) hq (mem_image_of_fix_pairPerp_four k hD) hβ hX hD

end Coordinate

section TransportFour

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_of_odd_of_commute_pairTorus_four {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 3 ≤ Nat.card K) (k : Fin 4)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {X D : Subgroup G}
    (hXe : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X := by
  subst hXe hDe
  obtain ⟨f, hKf⟩ := exists_card_eq_two_pow (K := K)
  exact mem_of_odd_of_commute_of_mulEquiv e (odd_card_pairTorus hKf k)
    (fun β hX hD => exists_mem_pairTorus_eq_conj_four hq k hX hD) htC ht hCtN hK

variable [Finite G]

theorem neighbour_standard_pairTorus_four (hL : CFSG.Open.standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hq : 4 ≤ Nat.card K) (k : Fin 4)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K))
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
  neighbour_standard_of_mulEquiv hL htC ht hK e (centralizer_pairTorus hq k)
    (isHypCoord_coordinateQuadPlus k).pairTorusOf_le_centralizer_pairPerpOf
    (F4Pilot.le_centralizer_self_of_isCyclic (isCyclic_pairTorus k))
    (isQuasisimple_pairPerp (by norm_num) k)
    (fun _ hX hD _ hβ => eq_one_of_two_pow_fix_pairTorus_four (by omega) k hβ hX hD) hX htX hDe

theorem neighbour_standard_pairTorus_of_seitzSetting_four (hset : SeitzSetting G L) {f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (k : Fin 4)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  exact neighbour_standard_pairTorus_four hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_plus hset (by norm_num) hKc e htC ht) hq k e hX htX hDe

end TransportFour

end CFSG.SeitzReduction.OmegaPilot
