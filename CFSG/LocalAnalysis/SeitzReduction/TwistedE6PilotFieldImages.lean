module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldImagesBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalize
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignLevi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (fixAll)

local instance twistedE6PilotFieldImagesNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotFieldImagesNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Conj

variable
  {K : Type} [Field K] {σ : K →+* K}

theorem levelTwist_conj_comm (hσσ : ∀ c, σ (σ c) = c) {S : Set (Fin TwistTag.E6.tag.rank)}
    (hS : ∀ i ∈ S, TwistTag.E6.perm i ∈ S) {x : ModGL TwistTag.E6.tag K}
    (hxΓ : x ∈ twistedFixedGroup TwistTag.E6 K σ)
    (hxN : x ∈ normalizer (subsystemGroup TwistTag.E6.tag K S : Set (ModGL TwistTag.E6.tag K))) :
    (subsystemGroup TwistTag.E6.tag K S).normalizerMonoidHom ⟨x, hxN⟩ * levelTwist hσσ S hS =
      levelTwist hσσ S hS * (subsystemGroup TwistTag.E6.tag K S).normalizerMonoidHom ⟨x, hxN⟩ := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  change x * twistHom TwistTag.E6 K σ g * x⁻¹ = twistHom TwistTag.E6 K σ (x * g * x⁻¹)
  rw [map_mul, map_mul, map_inv, hxΓ.2]
  rfl

end Conj

section Pieces

variable
  {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {σ : K →+* K}

theorem FieldNeighbourIso2E6.map_conj_of_fixRigidComm
    {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ} {t : G} {X : Subgroup G}
    {M D : Subgroup (ModGL TwistTag.E6.tag K)} {β₀ : MulAut M}
    (htL : t ∈ centralizer (L : Set G)) (h : FieldNeighbourIso2E6 e t X M β₀ D)
    (hβ₀ : β₀ * β₀ = 1) (hrig : FixRigidComm (D.subgroupOf M).subtype β₀)
    (x : graphFixedRootGroup TwistTag.E6 K σ)
    (hxN : (x : ModGL TwistTag.E6.tag K) ∈ normalizer (M : Set (ModGL TwistTag.E6.tag K)))
    (hxD : ∀ y ∈ D, (x : ModGL TwistTag.E6.tag K) * y * (x : ModGL TwistTag.E6.tag K)⁻¹ ∈ D ∧
      (x : ModGL TwistTag.E6.tag K)⁻¹ * y * (x : ModGL TwistTag.E6.tag K) ∈ D)
    (hDC : D ≤ graphFixedRootGroup TwistTag.E6 K σ)
    (hxβ : M.normalizerMonoidHom ⟨_, hxN⟩ * β₀ = β₀ * M.normalizerMonoidHom ⟨_, hxN⟩)
    (hdN : ((e.symm x : L) : G) ∈ normalizer (centralizerPerfectCore X : Set G))
    {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) (g : M) :
    ((h.Φ (M.normalizerMonoidHom ⟨_, hxN⟩ g) : centralizerPerfectCore X) : G) =
        ((e.symm x : L) : G) * (h.Φ g : G) * ((e.symm x : L) : G)⁻¹ := by
  set δ := M.normalizerMonoidHom ⟨_, hxN⟩ with hδ
  set c := (centralizerPerfectCore X).normalizerMonoidHom ⟨_, hdN⟩ with hc
  have hδinv : ∀ y : M, ((δ⁻¹ y : M) : ModGL TwistTag.E6.tag K) =
      (x : ModGL TwistTag.E6.tag K)⁻¹ * (y : ModGL TwistTag.E6.tag K) *
        (x : ModGL TwistTag.E6.tag K) := by
    intro y
    rw [hδ, ← map_inv, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp only [Subgroup.coe_inv, inv_inv]
  have hδA : ∀ a : D.subgroupOf M, ∃ a' : D.subgroupOf M,
      δ⁻¹ ((D.subgroupOf M).subtype a) = (D.subgroupOf M).subtype a' := by
    intro a
    have haD : ((a : M) : ModGL TwistTag.E6.tag K) ∈ D := mem_subgroupOf.1 a.2
    refine ⟨⟨δ⁻¹ ((D.subgroupOf M).subtype a), mem_subgroupOf.2 ?_⟩, rfl⟩
    rw [hδinv]
    exact (hxD _ haD).2
  have hfix : ∀ a : D.subgroupOf M, c (h.Φ ((D.subgroupOf M).subtype a)) =
      h.Φ (δ ((D.subgroupOf M).subtype a)) := by
    intro a
    have haD : ((a : M) : ModGL TwistTag.E6.tag K) ∈ D := mem_subgroupOf.1 a.2
    have hδa : ((δ ((D.subgroupOf M).subtype a) : M) : ModGL TwistTag.E6.tag K) =
        (x : ModGL TwistTag.E6.tag K) * ((a : M) : ModGL TwistTag.E6.tag K) *
          (x : ModGL TwistTag.E6.tag K)⁻¹ := by
      rw [hδ, Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    have hδaD : ((δ ((D.subgroupOf M).subtype a) : M) : ModGL TwistTag.E6.tag K) ∈ D := by
      rw [hδa]
      exact (hxD _ haD).1
    have e1 : ((h.Φ (a : M) : centralizerPerfectCore X) : G) =
        ((e.symm ⟨_, hDC haD⟩ : L) : G) := h.fix ⟨_, hDC haD⟩ haD (a : M).2
    have e2 : ((h.Φ (δ ((D.subgroupOf M).subtype a)) : centralizerPerfectCore X) : G) =
        ((e.symm ⟨_, hDC hδaD⟩ : L) : G) :=
      h.fix ⟨_, hDC hδaD⟩ hδaD (δ ((D.subgroupOf M).subtype a)).2
    have hxy : (⟨_, hDC hδaD⟩ : graphFixedRootGroup TwistTag.E6 K σ) =
        x * ⟨_, hDC haD⟩ * x⁻¹ := Subtype.ext hδa
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change ((e.symm x : L) : G) * (h.Φ (a : M) : G) * ((e.symm x : L) : G)⁻¹ =
      (h.Φ (δ ((D.subgroupOf M).subtype a)) : G)
    rw [e1, e2, hxy, map_mul, map_mul, map_inv]
    rfl
  have hcβ : MulAut.congr h.Φ.symm c * β₀ = β₀ * MulAut.congr h.Φ.symm c := by
    have hdt : Commute ((e.symm x : L) : G) t := mem_centralizer_iff.1 htL _ (e.symm x).2
    apply MulEquiv.ext
    intro g
    change h.Φ.symm (c (h.Φ (β₀ g))) = β₀ (h.Φ.symm (c (h.Φ g)))
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, h.twist, h.twist, MulEquiv.apply_symm_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    calc ((e.symm x : L) : G) * (t * (h.Φ g : G) * t⁻¹) * ((e.symm x : L) : G)⁻¹ =
        (((e.symm x : L) : G) * t) * (h.Φ g : G) * (((e.symm x : L) : G) * t)⁻¹ := by group
      _ = (t * ((e.symm x : L) : G)) * (h.Φ g : G) * (t * ((e.symm x : L) : G))⁻¹ := by
        rw [hdt.eq]
      _ = _ := by group
  have hxm' : (x : ModGL TwistTag.E6.tag K) ^ m = 1 := by
    rw [← SubgroupClass.coe_pow, hxm, OneMemClass.coe_one]
  have hdm' : ((e.symm x : L) : G) ^ m = 1 := by
    rw [← SubgroupClass.coe_pow, ← map_pow, hxm, map_one, OneMemClass.coe_one]
  have hδm : δ ^ m = 1 := by
    rw [hδ, ← map_pow]
    have : (⟨_, hxN⟩ : normalizer (M : Set (ModGL TwistTag.E6.tag K))) ^ m = 1 :=
      Subtype.ext (by simpa using hxm')
    rw [this, map_one]
  have hcm : c ^ m = 1 := by
    rw [hc, ← map_pow]
    have : (⟨_, hdN⟩ : normalizer (centralizerPerfectCore X : Set G)) ^ m = 1 :=
      Subtype.ext (by simpa using hdm')
    rw [this, map_one]
  have hN2 := map_apply_eq_of_fixRigidComm_of_odd hβ₀ hrig h.Φ hδA hfix hxβ hcβ hm hδm hcm g
  rw [hN2, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem conj_rootDiagUnit_mem_subsystemGroup' (S : Set (Fin TwistTag.E6.tag.rank))
    (a : Fin TwistTag.E6.tag.rank → Kˣ) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ subsystemGroup TwistTag.E6.tag K S) :
    rootDiagUnit TwistTag.E6.tag a * g * (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈
      subsystemGroup TwistTag.E6.tag K S := by
  have hle : subsystemGroup TwistTag.E6.tag K S ≤ (subsystemGroup TwistTag.E6.tag K S).comap
      (MulAut.conj (rootDiagUnit TwistTag.E6.tag a)).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation TwistTag.E6.tag K a).1 i c]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inl rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation TwistTag.E6.tag K a).2.1 i c]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inr rfl⟩
  exact hle hg

theorem rootDiagUnit_mem_normalizer_subsystemGroup (S : Set (Fin TwistTag.E6.tag.rank))
    (a : Fin TwistTag.E6.tag.rank → Kˣ) :
    rootDiagUnit TwistTag.E6.tag a ∈
      normalizer (subsystemGroup TwistTag.E6.tag K S : Set (ModGL TwistTag.E6.tag K)) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_rootDiagUnit_mem_subsystemGroup' S a, fun hg => ?_⟩
  have h1 := conj_rootDiagUnit_mem_subsystemGroup' S a⁻¹ hg
  rwa [← rootDiagUnit_inv, inv_inv, show (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
    (rootDiagUnit TwistTag.E6.tag a * g * (rootDiagUnit TwistTag.E6.tag a)⁻¹) *
      rootDiagUnit TwistTag.E6.tag a = g by group] at h1

theorem FieldNeighbourIso2E6.pieceCore_eq_map [Finite G] [Finite K] (hσσ : ∀ c, σ (σ c) = c)
    {S : Set (Fin TwistTag.E6.tag.rank)} (hS : ∀ i ∈ S, TwistTag.E6.perm i ∈ S)
    {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ} {t : G} {X : Subgroup G}
    (htL : t ∈ centralizer (L : Set G))
    (h : FieldNeighbourIso2E6 e t X (subsystemGroup TwistTag.E6.tag K S) (levelTwist hσσ S hS)
      (subsystemGroup TwistTag.E6.tag K S ⊓ graphFixedRootGroup TwistTag.E6 K σ))
    (hrig : FixRigidComm ((subsystemGroup TwistTag.E6.tag K S ⊓
      graphFixedRootGroup TwistTag.E6 K σ).subgroupOf (subsystemGroup TwistTag.E6.tag K S)).subtype
        (levelTwist hσσ S hS))
    {A : Subgroup Kˣ} (hAσ : ∀ c ∈ A, Units.map σ.toMonoidHom c = c) {m : ℕ} (hm : Odd m)
    (hAm : ∀ c ∈ A, c ^ m = 1) {I : Finset (Fin Tag.F4.rank)}
    (hXT : X ≤ modelToG e (relLeviTorus K A I)) :
    pieceCore e A I = (((perfectCore (subsystemGroup TwistTag.E6.tag K S ⊓
      centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K)))).subgroupOf
        (subsystemGroup TwistTag.E6.tag K S)).map h.Φ.toMonoidHom).map
          (centralizerPerfectCore X).subtype := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hTC : relLeviTorus K A I ≤ graphFixedRootGroup TwistTag.E6 K σ := relLeviTorus_le_C0 hAσ I
  have hx : ∀ d : modelToG e (relLeviTorus K A I), ∃ x : graphFixedRootGroup TwistTag.E6 K σ,
      (x : ModGL TwistTag.E6.tag K) ∈ relLeviTorus K A I ∧ ((e.symm x : L) : G) = d :=
    fun d => (mem_modelToG e).1 d.2
  choose xd hxdT hxde using hx
  have hxN : ∀ d, (xd d : ModGL TwistTag.E6.tag K) ∈
      normalizer (subsystemGroup TwistTag.E6.tag K S : Set (ModGL TwistTag.E6.tag K)) := by
    intro d
    obtain ⟨B, -, hB⟩ := mem_relLeviTorus.1 (hxdT d)
    rw [← hB]
    exact rootDiagUnit_mem_normalizer_subsystemGroup S _
  have hTcomm : modelToG e (relLeviTorus K A I) ≤
      centralizer (modelToG e (relLeviTorus K A I) : Set G) :=
    modelToG_le_centralizer e (relLeviTorus_le_centralizer_self A I)
  have hdN : ∀ d : modelToG e (relLeviTorus K A I),
      ((e.symm (xd d) : L) : G) ∈ normalizer (centralizerPerfectCore X : Set G) := by
    intro d
    rw [hxde d]
    refine F4Pilot.normalizer_le_normalizer_centralizerPerfectCore X
      (Subgroup.centralizer_le_normalizer _ ?_)
    exact Subgroup.centralizer_le (show (X : Set G) ⊆ modelToG e (relLeviTorus K A I) from hXT)
      (hTcomm d.2)
  have hxm : ∀ d, xd d ^ m = 1 := by
    intro d
    obtain ⟨B, ⟨-, hBA⟩, hB⟩ := mem_relLeviTorus.1 (hxdT d)
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hB, OneMemClass.coe_one]
    change ((rootDiagUnitHom TwistTag.E6.tag K).comp (relTupleHom K)) B ^ m = 1
    rw [← map_pow]
    have hBm : B ^ m = 1 := funext fun a => by
      rw [Pi.pow_apply, hAm _ (hBA a)]
      rfl
    rw [hBm, map_one]
  let α : modelToG e (relLeviTorus K A I) → MulAut (subsystemGroup TwistTag.E6.tag K S) :=
    fun d => (subsystemGroup TwistTag.E6.tag K S).normalizerMonoidHom ⟨_, hxN d⟩
  have hα : ∀ (d : modelToG e (relLeviTorus K A I)) (g : subsystemGroup TwistTag.E6.tag K S),
      ((h.Φ (α d g) : centralizerPerfectCore X) : G) = (d : G) * (h.Φ g : G) * (d : G)⁻¹ := by
    intro d g
    rw [← hxde d]
    have hxC : (xd d : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ := (xd d).2
    have hxD : ∀ y ∈ subsystemGroup TwistTag.E6.tag K S ⊓ graphFixedRootGroup TwistTag.E6 K σ,
        (xd d : ModGL TwistTag.E6.tag K) * y * (xd d : ModGL TwistTag.E6.tag K)⁻¹ ∈
          subsystemGroup TwistTag.E6.tag K S ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
        (xd d : ModGL TwistTag.E6.tag K)⁻¹ * y * (xd d : ModGL TwistTag.E6.tag K) ∈
          subsystemGroup TwistTag.E6.tag K S ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
      intro y hy
      obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.1 hy
      refine ⟨Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hxN d) y).1 hyM,
        mul_mem (mul_mem hxC hyC) (inv_mem hxC)⟩, Subgroup.mem_inf.2 ⟨?_,
        mul_mem (mul_mem (inv_mem hxC) hyC) hxC⟩⟩
      have h1 := (mem_normalizer_iff.1 (inv_mem (hxN d)) y).1 hyM
      rwa [inv_inv] at h1
    exact h.map_conj_of_fixRigidComm htL (levelTwist_mul_self hσσ hS) hrig (xd d) (hxN d) hxD
      inf_le_right (levelTwist_conj_comm hσσ hS
        (graphFixedRootGroup_le TwistTag.E6 K σ hxC) (hxN d)) (hdN d) hm (hxm d) g
  have hfixAll : fixAll α = (subsystemGroup TwistTag.E6.tag K S ⊓
      centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K))).subgroupOf
        (subsystemGroup TwistTag.E6.tag K S) := by
    ext g
    rw [mem_subgroupOf]
    constructor
    · intro hg
      refine Subgroup.mem_inf.2 ⟨g.2, mem_centralizer_iff.2 fun y hy => ?_⟩
      set d : modelToG e (relLeviTorus K A I) :=
        ⟨((e.symm ⟨y, hTC hy⟩ : L) : G), symm_mem_modelToG e hy⟩ with hd
      have hxy : xd d = ⟨y, hTC hy⟩ := by
        apply e.symm.injective
        apply Subtype.ext
        rw [hxde d]
      have h1 := congrArg (fun z : subsystemGroup TwistTag.E6.tag K S =>
        (z : ModGL TwistTag.E6.tag K)) (hg d)
      change (xd d : ModGL TwistTag.E6.tag K) * (g : ModGL TwistTag.E6.tag K) *
        (xd d : ModGL TwistTag.E6.tag K)⁻¹ = g at h1
      rw [hxy] at h1
      change y * (g : ModGL TwistTag.E6.tag K) * y⁻¹ = g at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1
    · intro hg d
      apply Subtype.ext
      change (xd d : ModGL TwistTag.E6.tag K) * (g : ModGL TwistTag.E6.tag K) *
        (xd d : ModGL TwistTag.E6.tag K)⁻¹ = g
      rw [mul_inv_eq_iff_eq_mul]
      exact mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2 _ (hxdT d)
  have hcore : perfectCore (fixAll α) = (perfectCore (subsystemGroup TwistTag.E6.tag K S ⊓
      centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K)))).subgroupOf
        (subsystemGroup TwistTag.E6.tag K S) := by
    rw [hfixAll]
    apply Subgroup.map_injective (subsystemGroup TwistTag.E6.tag K S).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_subgroupOf_eq_of_le inf_le_left,
      Subgroup.map_subgroupOf_eq_of_le ((CFSG.Quasithin.perfectCore_le _).trans inf_le_left)]
  rw [pieceCore_def, centralizerPerfectCore_eq_map_of_mulEquiv hXT h.Φ α hα, hcore]

end Pieces

section Neighbours

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]

theorem FieldNeighbourIso2E6.pieceCore_eq_map_relLevi_Y (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ}
    {t : G} {X : Subgroup G} (htL : t ∈ centralizer (L : Set G))
    (h : FieldNeighbourIso2E6 e t X (subsystemGroup TwistTag.E6.tag K setD)
      (d4LeviTwist (apply_apply_eq hK hσ)) (omegaMinusLevi σ))
    (hrig : FixRigidComm ((omegaMinusLevi σ).subgroupOf
      (subsystemGroup TwistTag.E6.tag K setD)).subtype (d4LeviTwist (apply_apply_eq hK hσ)))
    {A : Subgroup Kˣ} (hA3 : 3 ≤ Nat.card A) (hAσ : ∀ c ∈ A, Units.map σ.toMonoidHom c = c)
    {m : ℕ} (hm : Odd m) (hAm : ∀ c ∈ A, c ^ m = 1) {I : Finset (Fin Tag.F4.rank)}
    (hI : I.card ≤ 2) (hIY : I ⊆ {0, 1, 2}) (hXT : X ≤ modelToG e (relLeviTorus K A I)) :
    pieceCore e A I = (((relLevi K I).subgroupOf (subsystemGroup TwistTag.E6.tag K setD)).map
      h.Φ.toMonoidHom).map (centralizerPerfectCore X).subtype := by
  have := finite_of_card hK
  rw [← perfectCore_inf_centralizer_relLeviTorus_Y hA3 hI hIY]
  exact h.pieceCore_eq_map (apply_apply_eq hK hσ) perm_mem_setD htL hrig hAσ hm hAm hXT

end Neighbours

end CFSG.SeitzReduction.TwistedE6Pilot
