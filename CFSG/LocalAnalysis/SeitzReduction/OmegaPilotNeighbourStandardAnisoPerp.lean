module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAnisoTorus
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace omegaGroup mem_omegaGroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Extend

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {a a' : ι} {b c : K}
  {Q : QuadraticForm K (ι → K)}

theorem IsAnisoCoord.extendLin_mem_orthogonalGroup (h : IsAnisoCoord Q a a' b c)
    {g : perpSub K a a' ≃ₗ[K] perpSub K a a'}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpSub K a a').subtype)) :
    extendLin h.ne g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have hgu := (g ⟨perpPart a a' v, perpPart_mem h.ne v⟩).2
  have hR := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg
    ⟨perpPart a a' v, perpPart_mem h.ne v⟩
  simp only [QuadraticMap.comp_apply, Submodule.subtype_apply] at hR
  rw [extendLin_apply, add_comm, h.map_add_smul _ _ hgu.1 hgu.2, hR, ← h.apply_eq]

theorem IsAnisoCoord.extendLin_mem_orthDerived (h : IsAnisoCoord Q a a' b c)
    {g : perpSub K a a' ≃ₗ[K] perpSub K a a'}
    (hg : g ∈ orthDerived (Q.comp (perpSub K a a').subtype)) :
    extendLin h.ne g ∈ orthDerived Q := by
  have hle : (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpSub K a a').subtype)).map
      (extendLin h.ne) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g', hg', rfl⟩
    exact h.extendLin_mem_orthogonalGroup hg'
  have hmap : (orthDerived (Q.comp (perpSub K a a').subtype)).map (extendLin h.ne) ≤
      orthDerived Q := by
    rw [orthDerived, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact hmap ⟨g, hg, rfl⟩

theorem IsAnisoCoord.apply_mem_perpSub (h : IsAnisoCoord Q a a' b c) (hb : b ≠ 0)
    {g : (ι → K) ≃ₗ[K] (ι → K)} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g ∈ stabSub a a') {u : ι → K} (hu : u ∈ perpSub K a a') : g u ∈ perpSub K a a' := by
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (Pi.single a 1) u
  have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (Pi.single a' 1) u
  rw [hg.1, h.polar_left, h.polar_left, hu.2, mul_zero] at h1
  rw [hg.2, h.polar_right, h.polar_right, hu.1, mul_zero] at h2
  exact ⟨(mul_eq_zero.mp h2).resolve_left hb, (mul_eq_zero.mp h1).resolve_left hb⟩

@[expose] noncomputable def IsAnisoCoord.resHom (h : IsAnisoCoord Q a a' b c) (hb : b ≠ 0) :
    stabDerived Q a a' →* (perpSub K a a' ≃ₗ[K] perpSub K a a') where
  toFun y := CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv (perpSub K a a')
    (y : orthDerived Q).1
    (fun _ hu => h.apply_mem_perpSub hb (Subgroup.commutator_le_self _ (y : orthDerived Q).2)
      y.2 hu)
    (fun _ hu => h.apply_mem_perpSub hb
      (Subgroup.commutator_le_self _ (y⁻¹ : orthDerived Q).2) (y⁻¹).2 hu)
  map_one' := by
    ext u
    rfl
  map_mul' y y' := by
    ext u
    rfl

theorem IsAnisoCoord.coe_resHom_apply (h : IsAnisoCoord Q a a' b c) (hb : b ≠ 0)
    (y : stabDerived Q a a') (u : perpSub K a a') :
    ((h.resHom hb y u : perpSub K a a') : ι → K) =
      ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) u :=
  rfl

theorem IsAnisoCoord.extendLin_resHom (h : IsAnisoCoord Q a a' b c) (hb : b ≠ 0)
    (y : stabDerived Q a a') :
    extendLin h.ne (h.resHom hb y) = ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) := by
  ext v i
  rw [extendLin_apply, h.coe_resHom_apply]
  have hy : ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) ∈ stabSub a a' := y.2
  conv_rhs => rw [← perpPart_add_planePart (a := a) (b := a') v]
  simp only [map_add, map_smul, hy.1, hy.2]

theorem IsAnisoCoord.resHom_extendLin (h : IsAnisoCoord Q a a' b c) (hb : b ≠ 0)
    (g : perpSub K a a' ≃ₗ[K] perpSub K a a') (hg : extendLin h.ne g ∈ orthDerived Q) :
    h.resHom hb ⟨⟨extendLin h.ne g, hg⟩, extendLin_mem_stabSub h.ne g⟩ = g := by
  refine LinearEquiv.ext fun u => Subtype.ext ?_
  rw [h.coe_resHom_apply]
  exact extendLin_apply_perp h.ne g u

theorem IsAnisoCoord.commSpace_eq_map (h : IsAnisoCoord Q a a' b c) (hb : b ≠ 0)
    (y : stabDerived Q a a') :
    commSpace ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) =
      (commSpace (h.resHom hb y)).map (perpSub K a a').subtype := by
  have hy : ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) ∈ stabSub a a' := y.2
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨h.resHom hb y ⟨perpPart a a' v, perpPart_mem h.ne v⟩ -
      ⟨perpPart a a' v, perpPart_mem h.ne v⟩, mem_commSpace.mpr ⟨_, rfl⟩, ?_⟩
    simp only [Submodule.subtype_apply, Submodule.coe_sub, h.coe_resHom_apply]
    conv_rhs => rw [← perpPart_add_planePart (a := a) (b := a') v]
    simp only [map_add, map_smul, hy.1, hy.2]
    abel
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hz
    exact ⟨u, by simp [h.coe_resHom_apply]⟩

theorem IsAnisoCoord.resHom_mem_orthogonalGroup (h : IsAnisoCoord Q a a' b c) (hb : b ≠ 0)
    (y : stabDerived Q a a') :
    h.resHom hb y ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpSub K a a').subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro u
  simp only [QuadraticMap.comp_apply, Submodule.subtype_apply, h.coe_resHom_apply]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (Subgroup.commutator_le_self _ (y : orthDerived Q).2) u

variable [Fintype ι]

theorem IsAnisoCoord.resHom_mem_orthDerived [Finite K] [CharP K 2] (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a a').subtype)).Nondegenerate)
    (hT : ∃ T : Submodule K (perpSub K a a'), finrank K T = 3 ∧
      ∀ x ∈ T, Q.comp (perpSub K a a').subtype x = 0)
    (y : stabDerived Q a a') :
    h.resHom h.b_ne_zero y ∈ orthDerived (Q.comp (perpSub K a a').subtype) := by
  have hev : Even (finrank K (commSpace ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)))) :=
    (mem_omegaGroup.mp
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ (y : orthDerived Q).2)).2
  apply CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT
  refine mem_omegaGroup.mpr ⟨h.resHom_mem_orthogonalGroup h.b_ne_zero y, ?_⟩
  rw [h.commSpace_eq_map h.b_ne_zero y, Submodule.finrank_map_subtype_eq] at hev
  exact hev

@[expose] noncomputable def IsAnisoCoord.stabDerivedEquiv [Finite K] [CharP K 2]
    (h : IsAnisoCoord Q a a' b c) (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a a').subtype)).Nondegenerate)
    (hT : ∃ T : Submodule K (perpSub K a a'), finrank K T = 3 ∧
      ∀ x ∈ T, Q.comp (perpSub K a a').subtype x = 0) :
    stabDerived Q a a' ≃* orthDerived (Q.comp (perpSub K a a').subtype) where
  toFun y := ⟨h.resHom h.b_ne_zero y, h.resHom_mem_orthDerived hQ hR hT y⟩
  invFun g := ⟨⟨extendLin h.ne (g : perpSub K a a' ≃ₗ[K] perpSub K a a'),
      h.extendLin_mem_orthDerived g.2⟩,
    extendLin_mem_stabSub h.ne (g : perpSub K a a' ≃ₗ[K] perpSub K a a')⟩
  left_inv y := Subtype.ext (Subtype.ext (h.extendLin_resHom h.b_ne_zero y))
  right_inv g := Subtype.ext (h.resHom_extendLin h.b_ne_zero
    (g : perpSub K a a' ≃ₗ[K] perpSub K a a') _)
  map_mul' y y' := Subtype.ext (map_mul (h.resHom h.b_ne_zero) y y')

end Extend

section Proj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {a a' : Fin d} {b c : K}
  {Q : QuadraticForm K (Fin d → K)}

@[expose] noncomputable def IsAnisoCoord.pairPerpOfEquiv (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a a').subtype)).Nondegenerate)
    (hT : ∃ T : Submodule K (perpSub K a a'), finrank K T = 3 ∧
      ∀ x ∈ T, Q.comp (perpSub K a a').subtype x = 0) :
    pairPerpOf Q a a' ≃* orthDerived (Q.comp (perpSub K a a').subtype) :=
  ((stabDerived Q a a').equivMapOfInjective (projHom Q)
    (projHom_injective h.exists_ne_zero)).symm.trans (h.stabDerivedEquiv hQ hR hT)

theorem IsAnisoCoord.isQuasisimple_pairPerpOf (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a a').subtype)).Nondegenerate)
    (hT : ∃ T : Submodule K (perpSub K a a'), finrank K T = 3 ∧
      ∀ x ∈ T, Q.comp (perpSub K a a').subtype x = 0) :
    CFSG.IsQuasisimple (pairPerpOf Q a a') :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (h.pairPerpOfEquiv hQ hR hT).symm
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT)

end Proj

end CFSG.SeitzReduction.OmegaPilot
