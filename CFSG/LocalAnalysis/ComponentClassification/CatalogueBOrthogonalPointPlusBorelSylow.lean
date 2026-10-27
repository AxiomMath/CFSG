module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbitBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalSmallFamilyOrbit
open scoped Pointwise

theorem subgroup_map_conjugate {G : Type*} [Group G] {J : Type*} [Group J]
    (f : G →* J) (B : Subgroup G) (g : G) :
    (B.map (MulAut.conj g).toMonoidHom).map f =
      (B.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    map_inv]

theorem subgroup_map_conjugate_equiv {G : Type*} [Group G] {J : Type*} [Group J]
    (e : G ≃* J) (B : Subgroup G) (g : G) :
    (B.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
      (B.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom :=
  subgroup_map_conjugate e.toMonoidHom B g

variable (n : ℕ) (K : Type) [Field K]

@[expose] def plusProjectiveFlagFamily :
    Set (Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :=
  {J | ∃ F ∈ singularFlags (quadPlus n K) (n - 1),
    J = statedProjectiveFlagStabilizer (StatedQuadPlus n K) F}

theorem plusProjectiveFlagStabilizer_map (hn : 3 ≤ n)
    (F : Fin (n - 1) → Submodule K (Fin n ⊕ Fin n → K)) :
    (statedProjectiveFlagStabilizer (StatedQuadPlus n K) F).map
        (plusProjectiveEquiv n K hn).toMonoidHom =
      (MulAction.stabilizer (orthElementaryGroup (quadPlus n K)) F).map
        (QuotientGroup.mk' (elemScalars n K)) :=
  statedProjectiveFlagStabilizer_map_elementary (coe_quadPlus n K)
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus hn) F

theorem plusProjectiveUnipotent_isSylow [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hn : 3 ≤ n) :
    ∃ S : Sylow p (StatedProj (StatedOmega (StatedQuadPlus n K))),
      (S : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) =
        plusProjectiveUnipotent n K := by
  have : Finite (orthElementaryGroup (quadPlus n K)) := finite_orthElementaryGroup
  obtain ⟨S, hS⟩ := projUnip_isSylow (K := K) p hn
  have hsurj : Function.Surjective (plusProjectiveEquiv n K hn).symm.toMonoidHom :=
    (plusProjectiveEquiv n K hn).symm.surjective
  refine ⟨Sylow.mapSurjective (f := (plusProjectiveEquiv n K hn).symm.toMonoidHom) hsurj S,
    ?_⟩
  rw [Sylow.coe_mapSurjective, hS, ← plusProjectiveUnipotent_map n K hn, Subgroup.map_map]
  have he : (plusProjectiveEquiv n K hn).symm.toMonoidHom.comp
      (plusProjectiveEquiv n K hn).toMonoidHom = MonoidHom.id _ := by
    ext x
    exact (plusProjectiveEquiv n K hn).symm_apply_apply x
  rw [he, Subgroup.map_id]

theorem plusProjectiveUnipotent_normalizer [Finite K] (hn : 3 ≤ n) :
    Subgroup.normalizer (plusProjectiveUnipotent n K :
      Set (StatedProj (StatedOmega (StatedQuadPlus n K)))) = plusProjectiveBorel n K := by
  apply Subgroup.map_injective (f := (plusProjectiveEquiv n K hn).toMonoidHom)
    (plusProjectiveEquiv n K hn).injective
  rw [Subgroup.map_equiv_normalizer_eq, plusProjectiveUnipotent_map,
    normalizer_projUnip hn, plusProjectiveBorel_map]

theorem plusProjectiveFlagStabilizer_is_conjugate (hn : 3 ≤ n)
    (F : Fin (n - 1) → Submodule K (Fin n ⊕ Fin n → K))
    (hF : F ∈ singularFlags (quadPlus n K) (n - 1)) :
    ∃ g : StatedProj (StatedOmega (StatedQuadPlus n K)),
      (plusProjectiveBorel n K).map (MulAut.conj g).toMonoidHom =
        statedProjectiveFlagStabilizer (StatedQuadPlus n K) F := by
  obtain ⟨g, hg⟩ := (conj_projFlagStab_eq_stabilizer (K := K) (by omega : 1 ≤ n)).1 F hF
  refine ⟨(plusProjectiveEquiv n K hn).symm g, ?_⟩
  apply Subgroup.map_injective (f := (plusProjectiveEquiv n K hn).toMonoidHom)
    (plusProjectiveEquiv n K hn).injective
  rw [subgroup_map_conjugate_equiv, MulEquiv.apply_symm_apply, plusProjectiveBorel_map,
    plusProjectiveFlagStabilizer_map]
  exact hg

theorem plusProjectiveBorel_conjugate_is_flagStabilizer (hn : 3 ≤ n)
    (g : StatedProj (StatedOmega (StatedQuadPlus n K))) :
    ∃ F ∈ singularFlags (quadPlus n K) (n - 1),
      (plusProjectiveBorel n K).map (MulAut.conj g).toMonoidHom =
        statedProjectiveFlagStabilizer (StatedQuadPlus n K) F := by
  obtain ⟨F, hF, hg⟩ := (conj_projFlagStab_eq_stabilizer (K := K) (by omega : 1 ≤ n)).2
    (plusProjectiveEquiv n K hn g)
  refine ⟨F, hF, ?_⟩
  apply Subgroup.map_injective (f := (plusProjectiveEquiv n K hn).toMonoidHom)
    (plusProjectiveEquiv n K hn).injective
  rw [subgroup_map_conjugate_equiv, plusProjectiveBorel_map, plusProjectiveFlagStabilizer_map]
  exact hg

theorem plusProjectiveBorel_conjugacyFamily (hn : 3 ≤ n) :
    conjugacyFamily (plusProjectiveBorel n K) = plusProjectiveFlagFamily n K := by
  ext J
  constructor
  · rintro ⟨g, rfl⟩
    exact plusProjectiveBorel_conjugate_is_flagStabilizer n K hn g
  · rintro ⟨F, hF, rfl⟩
    exact plusProjectiveFlagStabilizer_is_conjugate n K hn F hF

theorem plusProjectiveBorel_aut_conjugate [Finite K] (hn : 3 ≤ n)
    (alpha : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))))
    (g : StatedProj (StatedOmega (StatedQuadPlus n K))) :
    ∃ h : StatedProj (StatedOmega (StatedQuadPlus n K)),
      ((plusProjectiveBorel n K).map (MulAut.conj g).toMonoidHom).map alpha.toMonoidHom =
        (plusProjectiveBorel n K).map (MulAut.conj h).toMonoidHom := by
  let beta : MulAut (orthElementaryGroup (quadPlus n K) ⧸ elemScalars n K) :=
    ((plusProjectiveEquiv n K hn).symm.trans alpha).trans (plusProjectiveEquiv n K hn)
  obtain ⟨h, hh⟩ := aut_map_conj_projFlagStab (K := K) hn beta (plusProjectiveEquiv n K hn g)
  refine ⟨(plusProjectiveEquiv n K hn).symm h, ?_⟩
  apply Subgroup.map_injective (f := (plusProjectiveEquiv n K hn).toMonoidHom)
    (plusProjectiveEquiv n K hn).injective
  have hp : (plusProjectiveEquiv n K hn).toMonoidHom.comp alpha.toMonoidHom =
      beta.toMonoidHom.comp (plusProjectiveEquiv n K hn).toMonoidHom := by
    ext x
    change plusProjectiveEquiv n K hn (alpha x) = plusProjectiveEquiv n K hn
      (alpha ((plusProjectiveEquiv n K hn).symm (plusProjectiveEquiv n K hn x)))
    rw [MulEquiv.symm_apply_apply]
  have hL : (((plusProjectiveBorel n K).map (MulAut.conj g).toMonoidHom).map
        alpha.toMonoidHom).map (plusProjectiveEquiv n K hn).toMonoidHom =
      ((((flagStab n K).subgroupOf (orthElementaryGroup (quadPlus n K))).map
        (QuotientGroup.mk' (elemScalars n K))).map
          (MulAut.conj (plusProjectiveEquiv n K hn g)).toMonoidHom).map beta.toMonoidHom := by
    rw [Subgroup.map_map, hp, ← Subgroup.map_map, subgroup_map_conjugate_equiv,
      plusProjectiveBorel_map]
  have hR : ((plusProjectiveBorel n K).map
        (MulAut.conj ((plusProjectiveEquiv n K hn).symm h)).toMonoidHom).map
        (plusProjectiveEquiv n K hn).toMonoidHom =
      (((flagStab n K).subgroupOf (orthElementaryGroup (quadPlus n K))).map
        (QuotientGroup.mk' (elemScalars n K))).map (MulAut.conj h).toMonoidHom := by
    rw [subgroup_map_conjugate_equiv, MulEquiv.apply_symm_apply, plusProjectiveBorel_map]
  rw [hL, hR]
  exact hh

theorem plusProjectiveFlagFamily_aut [Finite K] (hn : 3 ≤ n)
    (alpha : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K)))) :
    (fun J => J.map alpha.toMonoidHom) '' plusProjectiveFlagFamily n K =
      plusProjectiveFlagFamily n K := by
  rw [← plusProjectiveBorel_conjugacyFamily n K hn]
  ext J
  constructor
  · rintro ⟨B, ⟨g, rfl⟩, rfl⟩
    obtain ⟨h, hh⟩ := plusProjectiveBorel_aut_conjugate n K hn alpha g
    exact ⟨h, hh.symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨h, hh⟩ := plusProjectiveBorel_aut_conjugate n K hn alpha.symm g
    refine ⟨(plusProjectiveBorel n K).map (MulAut.conj h).toMonoidHom, ⟨h, rfl⟩, ?_⟩
    change ((plusProjectiveBorel n K).map (MulAut.conj h).toMonoidHom).map
      alpha.toMonoidHom = _
    rw [← hh, Subgroup.map_map]
    have ha : alpha.toMonoidHom.comp alpha.symm.toMonoidHom = MonoidHom.id _ := by
      ext x
      exact alpha.apply_symm_apply x
    rw [ha, Subgroup.map_id]

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
