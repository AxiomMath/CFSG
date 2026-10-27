module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.GroupTheory.PerfectLeSupCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Polynomial Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped commutatorElement

universe u

section Supported

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem apply_eq_self_of_supportedUnitary_of_primaryProjection_eq_zero
    (H : UnitaryPrimaryData σ B x) {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ supportedUnitary B x {a}) {v : V}
    (hv : primaryProjection (x : Module.End K V) a v = 0) :
    (g : Module.End K V) v = v := by
  classical
  have hsq := H.squarefree
  have hsum : v = ∑ b ∈ primaryFactors (x : Module.End K V),
      primaryProjection (x : Module.End K V) b v := by
    have h := LinearMap.congr_fun (sum_primaryProjection (x := (x : Module.End K V)) hsq) v
    rw [LinearMap.sum_apply] at h
    simpa using h.symm
  conv_lhs => rw [hsum]
  rw [map_sum]
  conv_rhs => rw [hsum]
  refine Finset.sum_congr rfl fun b hb => ?_
  by_cases hba : b = a
  · rw [hba, hv, map_zero]
  · exact hg.2 b hb (by simp [hba]) _ (primaryProjection_mem hsq hb v)

end Supported

section SelfDual

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

private theorem map_specialBlock_eq_sesqSpecialUnitary_subgroupOf
    {a : primaryFactors (x : Module.End K V)}
    {hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X]))}
    {Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
      primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
        AdjoinRoot (a : K[X])}
    {φ : orbitFactor B x (a : K[X]) ≃* sesqUnitaryGroup Hf}
    (hcompat : ∀ s : orbitFactor B x (a : K[X]),
      ((φ s : sesqUnitaryGroup Hf) : blockGL (x : Module.End K V) (a : K[X])) =
        blockRestrict x (a : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩) :
    ((specialBlock B x (a : K[X])).subgroupOf (orbitFactor B x (a : K[X]))).map
        φ.toMonoidHom =
      (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) := by
  ext u
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
    have hsb := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨horb, hg, hdet⟩ := mem_specialBlock.mp hsb
    have h3 : blockDetHom x (a : K[X])
        ⟨(s : LinearMap.GeneralLinearGroup K V),
          orbitFactor_le_gl_centralizer s.2⟩ = 1 := by
      rw [show (⟨(s : LinearMap.GeneralLinearGroup K V),
          orbitFactor_le_gl_centralizer s.2⟩ : gl_centralizer x) =
          ⟨(s : LinearMap.GeneralLinearGroup K V), hg⟩ from Subtype.ext rfl]
      exact hdet
    have hdetU : blockGLDet (x : Module.End K V) (a : K[X])
        ((φ s : sesqUnitaryGroup Hf) : blockGL (x : Module.End K V) (a : K[X])) = 1 := by
      rw [hcompat s]
      simpa only [blockDetHom, MonoidHom.comp_apply] using h3
    exact ⟨(φ s).2, by simpa [blockGLDet] using congrArg Units.val hdetU⟩
  · intro hu
    refine ⟨φ.symm u, ?_, by simp⟩
    change (φ.symm u : LinearMap.GeneralLinearGroup K V) ∈ specialBlock B x (a : K[X])
    rw [mem_specialBlock]
    refine ⟨(φ.symm u).2, orbitFactor_le_gl_centralizer (φ.symm u).2, ?_⟩
    have h1 : ((φ (φ.symm u) : sesqUnitaryGroup Hf) :
        blockGL (x : Module.End K V) (a : K[X])) =
        blockRestrict x (a : K[X]) ⟨(φ.symm u).1,
          orbitFactor_le_gl_centralizer (φ.symm u).2⟩ := hcompat (φ.symm u)
    rw [φ.apply_symm_apply] at h1
    have hdet : blockGLDet (x : Module.End K V) (a : K[X])
        (blockRestrict x (a : K[X]) ⟨(φ.symm u).1,
          orbitFactor_le_gl_centralizer (φ.symm u).2⟩) = 1 := by
      rw [← h1]
      exact Units.ext (by
        simpa [blockGLDet] using (mem_sesqSpecialUnitaryGroup.mp hu).2)
    simpa only [blockDetHom, MonoidHom.comp_apply] using hdet

theorem exists_selfDual_specialBlock_mulEquiv_sesqSpecialUnitary
    (H : UnitaryPrimaryData hK.bar B x) {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly hK.bar (a : K[X]) = a) (hS : SelfDualPrimaryBlock hK B x a) :
    ∃ (hE : UnitaryFieldData ℓ (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X])))
      (Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
        primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
          AdjoinRoot (a : K[X])),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
      ∃ Φ : ↥(specialBlock B x (a : K[X])) ≃* ↥(sesqSpecialUnitaryGroup Hf),
        (∀ (s : ↥(specialBlock B x (a : K[X]))) (v : V)
          (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
          blockApply (Φ s : blockGL (x : Module.End K V) (a : K[X])) v hv =
            ((s : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) ∧
        (∀ m ∈ unitaryCentralizer B x, ∃ g : ↥(sesqUnitaryGroup Hf),
          ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
            blockApply (g : blockGL (x : Module.End K V) (a : K[X])) v hv =
              (m : Module.End K V) v) := by
  classical
  obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, -⟩ := exists_selfDualFactor hself hS
  have hcompat : ∀ s : orbitFactor B x (a : K[X]),
      ((φ s : sesqUnitaryGroup Hf) : blockGL (x : Module.End K V) (a : K[X])) =
        blockRestrict x (a : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩ :=
    fun s => blockGL_ext fun v hv => hφ s v hv
  have hmap := map_specialBlock_eq_sesqSpecialUnitary_subgroupOf hcompat
  let Φ : ↥(specialBlock B x (a : K[X])) ≃* ↥(sesqSpecialUnitaryGroup Hf) :=
    (Subgroup.subgroupOfEquivOfLe
        (specialBlock_le_orbitFactor (B := B) (x := x) (a := a))).symm.trans
      ((φ.subgroupMap ((specialBlock B x (a : K[X])).subgroupOf
          (orbitFactor B x (a : K[X])))).trans
        ((MulEquiv.subgroupCongr hmap).trans (Subgroup.subgroupOfEquivOfLe
          (sesqSpecialUnitaryGroup_le Hf))))
  have hΦcoe : ∀ s : ↥(specialBlock B x (a : K[X])),
      ((Φ s : ↥(sesqSpecialUnitaryGroup Hf)) : blockGL (x : Module.End K V) (a : K[X])) =
        ((φ ⟨(s : LinearMap.GeneralLinearGroup K V), (mem_specialBlock.mp s.2).1⟩ :
          sesqUnitaryGroup Hf) : blockGL (x : Module.End K V) (a : K[X])) := by
    intro s
    rfl
  refine ⟨hE, Hf, hHf, hHfl, Φ, ?_, ?_⟩
  · intro s v hv
    rw [hΦcoe s]
    exact hφ ⟨(s : LinearMap.GeneralLinearGroup K V), (mem_specialBlock.mp s.2).1⟩ v hv
  ·
    intro m hm
    have hO : ∀ b ∈ primaryFactors (x : Module.End K V), b ∈ ({(a : K[X])} : Set K[X]) →
        dualPoly hK.bar b ∈ ({(a : K[X])} : Set K[X]) := by
      intro b hb hbO
      rw [Set.mem_singleton_iff] at hbO ⊢
      subst hbO
      exact hself
    obtain ⟨gO, hgO, hgOeq⟩ := exists_component H hO hm
    have hsupp : orbitFactor B x (a : K[X]) = supportedUnitary B x {(a : K[X])} := by
      unfold orbitFactor
      rw [hself, Set.pair_eq_singleton]
    have hgO' : gO ∈ orbitFactor B x (a : K[X]) := hsupp.symm ▸ hgO
    refine ⟨φ ⟨gO, hgO'⟩, fun v hv => ?_⟩
    rw [hcompat ⟨gO, hgO'⟩]
    exact (blockApply_blockRestrict x (a : K[X])
      ⟨gO, orbitFactor_le_gl_centralizer hgO'⟩ v hv).trans
      (hgOeq (a : K[X]) a.2 (by simp) v hv)

end SelfDual

section Conj

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem blockApply_conj_specialBlock
    {a : primaryFactors (x : Module.End K V)}
    {G : Subgroup (blockGL (x : Module.End K V) (a : K[X]))}
    {Φ : ↥(specialBlock B x (a : K[X])) ≃* ↥G}
    (hΦ : ∀ (s : ↥(specialBlock B x (a : K[X]))) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply (Φ s : blockGL (x : Module.End K V) (a : K[X])) v hv =
        ((s : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
    {m : LinearMap.GeneralLinearGroup K V} (hm : m ∈ unitaryCentralizer B x)
    {g : blockGL (x : Module.End K V) (a : K[X])}
    (hg : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply g v hv = (m : Module.End K V) v)
    (s : ↥(specialBlock B x (a : K[X]))) :
    ((Φ ⟨m * (s : LinearMap.GeneralLinearGroup K V) * m⁻¹,
        conj_mem_specialBlock hm s.2⟩ : ↥G) :
      blockGL (x : Module.End K V) (a : K[X])) = g * (Φ s) * g⁻¹ := by
  have hg_eq : g = blockRestrict x (a : K[X]) ⟨m, hm.2⟩ :=
    blockGL_ext fun v hv =>
      (hg v hv).trans (blockApply_blockRestrict x a ⟨m, hm.2⟩ v hv).symm
  have hinv : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply g⁻¹ v hv = ((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) v := by
    intro v hv
    rw [hg_eq, ← map_inv, blockApply_blockRestrict]
    rfl
  apply blockGL_ext
  intro v hv
  rw [hΦ ⟨m * (s : LinearMap.GeneralLinearGroup K V) * m⁻¹,
    conj_mem_specialBlock hm s.2⟩ v hv]
  simp only [Units.val_mul, Module.End.mul_apply]
  rw [← hinv v hv]
  have hsv : ((s : LinearMap.GeneralLinearGroup K V) : Module.End K V)
      (blockApply g⁻¹ v hv) = blockApply (Φ s : blockGL (x : Module.End K V) (a : K[X]))
        (blockApply g⁻¹ v hv) (blockApply_mem g⁻¹ v hv) :=
    (hΦ s (blockApply g⁻¹ v hv) (blockApply_mem g⁻¹ v hv)).symm
  rw [hsv]
  rw [← hg _ (blockApply_mem (Φ s : blockGL (x : Module.End K V) (a : K[X]))
    (blockApply g⁻¹ v hv) (blockApply_mem g⁻¹ v hv))]
  rw [show blockApply (g * (Φ s : blockGL (x : Module.End K V) (a : K[X])) * g⁻¹) v hv =
      blockApply g (blockApply (Φ s : blockGL (x : Module.End K V) (a : K[X]))
          (blockApply g⁻¹ v hv) (blockApply_mem g⁻¹ v hv))
        (blockApply_mem (Φ s : blockGL (x : Module.End K V) (a : K[X]))
          (blockApply g⁻¹ v hv) (blockApply_mem g⁻¹ v hv)) by
    rw [blockApply_blockApply, blockApply_blockApply]]

end Conj

section QuasiCommute

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

private theorem mu_ne_zero_of_mul_commute
    {lam μ : K} {m : LinearMap.GeneralLinearGroup K V} {v : V} (hv : v ≠ 0)
    (hx : (x : Module.End K V) v = lam • v) (hlam : lam ≠ 0)
    (hq : (m : Module.End K V) * (x : Module.End K V) =
      μ • ((x : Module.End K V) * (m : Module.End K V))) :
    μ ≠ 0 := by
  intro h0
  apply hv
  have h1 : lam • ((m : Module.End K V) v) = μ •
      ((x : Module.End K V) ((m : Module.End K V) v)) := by
    have h := congrArg (fun T : Module.End K V => T v) hq
    simpa [Module.End.mul_apply, hx] using h
  rw [h0, zero_smul] at h1
  have hmv : (m : Module.End K V) v = 0 := (smul_eq_zero.mp h1).resolve_left hlam
  have h2 : ((m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
      ((m : Module.End K V) v) = 0 := by rw [hmv, map_zero]
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel] at h2
  simpa using h2

private theorem primaryProjection_inv_apply_eq_zero
    (H : UnitaryPrimaryData hK.bar B x) {lam : K}
    (ha : X - C lam ∈ primaryFactors (x : Module.End K V))
    {m : LinearMap.GeneralLinearGroup K V} {μ : K}
    (hq : (m : Module.End K V) * (x : Module.End K V) =
      μ • ((x : Module.End K V) * (m : Module.End K V)))
    (hμ : μ ≠ 1) {v : V} (hv : v ∈ primaryComponent (x : Module.End K V) (X - C lam)) :
    primaryProjection (x : Module.End K V) (X - C lam)
      (((m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) = 0 := by
  classical
  have hsq := H.squarefree
  obtain ⟨v₀, hv₀, hv₀0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq ha)
  have hxlam₀ : (x : Module.End K V) v₀ = lam • v₀ := by
    have h := mem_primaryComponent.mp hv₀
    have h0 : (x : Module.End K V) v₀ - lam • v₀ = 0 := by
      simpa [map_sub, aeval_X, aeval_C, Module.algebraMap_end_apply] using h
    exact sub_eq_zero.mp h0
  have hlam : lam ≠ 0 := by
    intro h0
    apply hv₀0
    apply injective_unit x
    rw [hxlam₀, h0, zero_smul]
    simp
  have hμ0 : μ ≠ 0 := mu_ne_zero_of_mul_commute hv₀0 hxlam₀ hlam hq
  have hμlam : μ * lam ≠ lam := by
    intro h
    exact hμ (mul_right_cancel₀ hlam (by rw [h, one_mul]))
  by_cases hv0 : v = 0
  · rw [hv0, map_zero, map_zero]
  · have hxlam : (x : Module.End K V) v = lam • v := by
      have h := mem_primaryComponent.mp hv
      have h0 : (x : Module.End K V) v - lam • v = 0 := by
        simpa [map_sub, aeval_X, aeval_C, Module.algebraMap_end_apply] using h
      exact sub_eq_zero.mp h0
    have hxinv : (x : Module.End K V) (((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) v) = (μ * lam) • (((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
          Module.End K V) v) := by
      have hm1 : (m : Module.End K V)
          (((m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) = v := by
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
        rfl
      have hm1' : ∀ u : V, ((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
          Module.End K V) ((m : Module.End K V) u) = u := by
        intro u
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
        rfl
      have h1 := congrArg (fun T : Module.End K V =>
        T (((m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)) hq
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1
      rw [hm1, hxlam] at h1
      rw [smul_smul] at h1
      have h2 := congrArg (fun w => ((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
        Module.End K V) w) h1
      rw [map_smul, hm1'] at h2
      exact h2
    set w := ((m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v with hw
    set p := primaryProjection (x : Module.End K V) (X - C lam) with hp
    have hpmem : p w ∈ primaryComponent (x : Module.End K V) (X - C lam) :=
      primaryProjection_mem hsq ha w
    have hxp : (x : Module.End K V) (p w) = lam • (p w) := by
      have h := mem_primaryComponent.mp hpmem
      have h0 : (x : Module.End K V) (p w) - lam • (p w) = 0 := by
        simpa [map_sub, aeval_X, aeval_C, Module.algebraMap_end_apply] using h
      exact sub_eq_zero.mp h0
    have hcomm : Commute (x : Module.End K V) p :=
      commute_aeval (Commute.refl (x : Module.End K V))
        (primaryIdempotent (x : Module.End K V) (X - C lam))
    have hxw : (x : Module.End K V) (p w) = (μ * lam) • (p w) := by
      calc (x : Module.End K V) (p w) = p ((x : Module.End K V) w) := by
            have h := congrArg (fun T : Module.End K V => T w) hcomm.eq
            simpa [Module.End.mul_apply] using h
        _ = p ((μ * lam) • w) := by rw [hxinv]
        _ = (μ * lam) • (p w) := by rw [map_smul]
    rw [hxp] at hxw
    have hzero : (lam - μ * lam) • (p w) = 0 := by
      rw [sub_smul, hxw, sub_self]
    exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (Ne.symm hμlam))
theorem smul_eq_one_of_normalizes_specialBlock
    (H : UnitaryPrimaryData hK.bar B x) {lam : K}
    (ha : X - C lam ∈ primaryFactors (x : Module.End K V))
    (hself : dualPoly hK.bar (X - C lam) = X - C lam)
    {m : LinearMap.GeneralLinearGroup K V} {μ : K}
    (hq : (m : Module.End K V) * (x : Module.End K V) =
      μ • ((x : Module.End K V) * (m : Module.End K V)))
    (hnorm : (specialBlock B x (X - C lam)).map (MulAut.conj m).toMonoidHom =
      specialBlock B x (X - C lam))
    (hne : specialBlock B x (X - C lam) ≠ ⊥) :
    μ = 1 := by
  classical
  by_contra hμ
  have hsq := H.squarefree
  have hproj : ∀ v ∈ primaryComponent (x : Module.End K V) (X - C lam),
      primaryProjection (x : Module.End K V) (X - C lam)
        (((m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) = 0 :=
    fun v hv => primaryProjection_inv_apply_eq_zero H ha hq hμ hv
  have hsupp : specialBlock B x (X - C lam) ≤ supportedUnitary B x {(X - C lam)} := by
    refine (specialBlock_le_orbitFactor).trans ?_
    unfold orbitFactor
    rw [hself, Set.pair_eq_singleton]
  have hbot : specialBlock B x (X - C lam) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    have hfix : ∀ v ∈ primaryComponent (x : Module.End K V) (X - C lam),
        (s : Module.End K V) (((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
          Module.End K V) v) = ((m⁻¹ : LinearMap.GeneralLinearGroup K V) :
            Module.End K V) v :=
      fun v hv =>
        apply_eq_self_of_supportedUnitary_of_primaryProjection_eq_zero H ha (hsupp hs)
          (hproj v hv)
    have hs' : m * s * m⁻¹ ∈ specialBlock B x (X - C lam) := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom hs
      rw [hnorm] at h
      have h' : MulAut.conj m s ∈ specialBlock B x (X - C lam) := h
      rwa [MulAut.conj_apply] at h'
    have h1 : m * s * m⁻¹ = 1 := by
      refine eq_one_of_paired H ha (mem_specialBlock.mp hs').1 ?_
      intro v' hv'
      have h2 : ((m * s * m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v' =
          (m : Module.End K V) ((s : Module.End K V)
            (((m⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v')) := by
        simp only [Units.val_mul, Module.End.mul_apply]
      rw [h2, hfix v' hv', ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
      rfl
    calc s = m⁻¹ * (m * s * m⁻¹) * m := by group
      _ = m⁻¹ * 1 * m := by rw [h1]
      _ = 1 := by group
  exact hne hbot

end QuasiCommute

section Concrete

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData ℓ f K)

noncomputable abbrev unitaryNormOneScalars (n : ℕ) :
    Subgroup ↥(gramSU h (idGram K n)) :=
  normOneScalars h (gramSU h (idGram K n)) n

noncomputable abbrev unitaryPreimageBlock
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)} (a : K[X]) :
    Subgroup ↥(gramSU h (idGram K n)) :=
  (specialBlock (idForm h n) x a).comap (toLinSU h n)

noncomputable abbrev unitaryBlockComponent
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)} (a : K[X]) :
    Subgroup (primeFormP h (idGram K n)) :=
  (unitaryPreimageBlock h (x := x) a).map (QuotientGroup.mk' (unitaryNormOneScalars h n))

theorem map_primeFormConjSU_le_sup_normOneScalars
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    {a : primaryFactors (x : Module.End K (Fin n → K))}
    {X : primeFormUnitary h (idGram K n)}
    (hstab : primeFormConjHom h (idGram K n) X ∈
      CFSG.GroupActions.subgroupStabAut (unitaryBlockComponent h (x := x) a)) :
    (unitaryPreimageBlock h (x := x) a).map
        (primeFormConjSU h (idGram K n) X).toMonoidHom ≤
      unitaryPreimageBlock h (x := x) a ⊔ unitaryNormOneScalars h n := by
  classical
  intro y hy
  obtain ⟨u, hu, rfl⟩ := hy
  have hmemT : QuotientGroup.mk' (unitaryNormOneScalars h n) u ∈
      unitaryBlockComponent h (x := x) a := Subgroup.mem_map_of_mem _ hu
  have h1 : QuotientGroup.mk' (unitaryNormOneScalars h n)
      (primeFormConjSU h (idGram K n) X u) ∈ unitaryBlockComponent h (x := x) a := by
    exact CFSG.GroupActions.apply_mem_of_mem_subgroupStabAut hstab hmemT
  obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.mp h1
  have h2 : QuotientGroup.mk' (unitaryNormOneScalars h n)
      (primeFormConjSU h (idGram K n) X u * v⁻¹) = 1 := by
    rw [map_mul, map_inv, hve, mul_inv_cancel]
  have h3 : primeFormConjSU h (idGram K n) X u * v⁻¹ ∈ unitaryNormOneScalars h n :=
    (QuotientGroup.eq_one_iff _).mp h2
  have h4 : primeFormConjSU h (idGram K n) X u =
      (primeFormConjSU h (idGram K n) X u * v⁻¹) * v := by group
  change primeFormConjSU h (idGram K n) X u ∈
    unitaryPreimageBlock h (x := x) a ⊔ unitaryNormOneScalars h n
  rw [h4]
  have h5 := Subgroup.mul_mem_sup h3 hv
  rwa [sup_comm] at h5

private theorem map_primeFormConjSU_eq_self
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (H : UnitaryPrimaryData h.bar (idForm h n) x)
    {a : primaryFactors (x : Module.End K (Fin n → K))} (hq : 2 ≤ ℓ ^ f)
    (ha : IsGoodBlock h x a) {X : primeFormUnitary h (idGram K n)}
    (hstab : primeFormConjHom h (idGram K n) X ∈
      CFSG.GroupActions.subgroupStabAut (unitaryBlockComponent h (x := x) a)) :
    (unitaryPreimageBlock h (x := x) (a : K[X])).map
        (primeFormConjSU h (idGram K n) X).toMonoidHom =
      unitaryPreimageBlock h (x := x) (a : K[X]) := by
  classical
  have hSBle : specialBlock (idForm h n) x (a : K[X]) ≤ (toLinSU h n).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a ha hg)
  have hFmap : (unitaryPreimageBlock h (x := x) (a : K[X])).map (toLinSU h n) =
      specialBlock (idForm h n) x (a : K[X]) :=
    Subgroup.map_comap_eq_self hSBle
  have hQF : CFSG.IsQuasisimple ↥(unitaryPreimageBlock h (x := x) (a : K[X])) := by
    have e : ↥(unitaryPreimageBlock h (x := x) (a : K[X])) ≃*
        ↥(specialBlock (idForm h n) x (a : K[X])) :=
      (Subgroup.equivMapOfInjective _ (toLinSU h n) toLinSU_injective).trans
        (MulEquiv.subgroupCongr hFmap)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      ((specialBlockFacts_of_good H hq a ha).quasisimple ha.1)
  haveI : Group.IsPerfect ↥(unitaryPreimageBlock h (x := x) (a : K[X])) := hQF.1
  have hFcomm : ⁅unitaryPreimageBlock h (x := x) (a : K[X]),
      unitaryPreimageBlock h (x := x) (a : K[X])⁆ =
      unitaryPreimageBlock h (x := x) (a : K[X]) := Subgroup.commutator_eq_self
  have hZcenter : unitaryNormOneScalars h n ≤
      Subgroup.center ↥(gramSU h (idGram K n)) := normOneScalars_le_center h _ n
  have hkey : ∀ Y : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) Y ∈
        CFSG.GroupActions.subgroupStabAut (unitaryBlockComponent h (x := x) (a : K[X])) →
      (unitaryPreimageBlock h (x := x) (a : K[X])).map
        (primeFormConjSU h (idGram K n) Y).toMonoidHom ≤
        unitaryPreimageBlock h (x := x) (a : K[X]) := by
    intro Y hY
    have hle := map_primeFormConjSU_le_sup_normOneScalars (h := h) (a := a) (X := Y) hY
    let P : Subgroup ↥(gramSU h (idGram K n)) :=
      (unitaryPreimageBlock h (x := x) (a : K[X])).map
        (primeFormConjSU h (idGram K n) Y).toMonoidHom
    have hPcomm : ⁅P, P⁆ = P := by
      change ⁅(unitaryPreimageBlock h (x := x) (a : K[X])).map
            (primeFormConjSU h (idGram K n) Y).toMonoidHom,
          (unitaryPreimageBlock h (x := x) (a : K[X])).map
            (primeFormConjSU h (idGram K n) Y).toMonoidHom⁆ =
        (unitaryPreimageBlock h (x := x) (a : K[X])).map
          (primeFormConjSU h (idGram K n) Y).toMonoidHom
      rw [← Subgroup.map_commutator, hFcomm]
    have hsup : unitaryPreimageBlock h (x := x) (a : K[X]) ⊔ unitaryNormOneScalars h n ≤
        unitaryPreimageBlock h (x := x) (a : K[X]) ⊔
          Subgroup.center ↥(gramSU h (idGram K n)) := by
      refine sup_le le_sup_left ?_
      exact hZcenter.trans le_sup_right
    exact CFSG.le_of_perfect_of_le_sup_center (Y := ↥(gramSU h (idGram K n))) hFcomm hPcomm
      (hle.trans hsup)
  have hstab_inv : primeFormConjHom h (idGram K n) X⁻¹ ∈
      CFSG.GroupActions.subgroupStabAut (unitaryBlockComponent h (x := x) (a : K[X])) := by
    have hc := (CFSG.GroupActions.subgroupStabAut
      (unitaryBlockComponent h (x := x) (a : K[X]))).inv_mem hstab
    rwa [← map_inv] at hc
  have hFX : (unitaryPreimageBlock h (x := x) (a : K[X])).map
      (primeFormConjSU h (idGram K n) X).toMonoidHom ≤
      unitaryPreimageBlock h (x := x) (a : K[X]) := hkey X hstab
  haveI : Finite K := h.finite
  haveI : Finite ↥(unitaryPreimageBlock h (x := x) (a : K[X])) := inferInstance
  have hcard : Nat.card ↥(unitaryPreimageBlock h (x := x) (a : K[X])) ≤
      Nat.card ↥((unitaryPreimageBlock h (x := x) (a : K[X])).map
        (primeFormConjSU h (idGram K n) X).toMonoidHom) :=
    (Nat.card_congr ((primeFormConjSU h (idGram K n) X).subgroupMap
      (unitaryPreimageBlock h (x := x) (a : K[X]))).toEquiv).le
  exact Subgroup.eq_of_le_of_card_ge hFX hcard

theorem toLinSU_primeFormConjSU (X : primeFormUnitary h (idGram K n))
    (u : ↥(gramSU h (idGram K n))) :
    toLinSU h n (primeFormConjSU h (idGram K n) X u) =
      Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K) * toLinSU h n u *
        (Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K))⁻¹ := by
  change Matrix.GeneralLinearGroup.toLin
      (((primeFormConjSU h (idGram K n) X) u : ↥(gramSU h (idGram K n))) : GL (Fin n) K) =
    Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K) *
      Matrix.GeneralLinearGroup.toLin ((u : ↥(gramSU h (idGram K n))) : GL (Fin n) K) *
      (Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K))⁻¹
  rw [show (((primeFormConjSU h (idGram K n) X) u : ↥(gramSU h (idGram K n))) : GL (Fin n) K) =
      (X : GL (Fin n) K) * ((u : ↥(gramSU h (idGram K n))) : GL (Fin n) K) *
        (X : GL (Fin n) K)⁻¹ from rfl,
    map_mul, map_mul, map_inv]

theorem map_conj_specialBlock_eq_self
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (H : UnitaryPrimaryData h.bar (idForm h n) x)
    {a : primaryFactors (x : Module.End K (Fin n → K))} (hq : 2 ≤ ℓ ^ f)
    (ha : IsGoodBlock h x a) {X : primeFormUnitary h (idGram K n)}
    (hstab : primeFormConjHom h (idGram K n) X ∈
      CFSG.GroupActions.subgroupStabAut (unitaryBlockComponent h (x := x) a)) :
    (specialBlock (idForm h n) x (a : K[X])).map
        (MulAut.conj (Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K))).toMonoidHom =
      specialBlock (idForm h n) x (a : K[X]) := by
  classical
  have hSBle : specialBlock (idForm h n) x (a : K[X]) ≤ (toLinSU h n).range := fun g hg =>
    mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a ha hg)
  have hFmap : (unitaryPreimageBlock h (x := x) (a : K[X])).map (toLinSU h n) =
      specialBlock (idForm h n) x (a : K[X]) :=
    Subgroup.map_comap_eq_self hSBle
  have hPeq := map_primeFormConjSU_eq_self h H hq ha hstab

  have hhom : (toLinSU h n).comp (primeFormConjSU h (idGram K n) X).toMonoidHom =
      (MulAut.conj (Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K))).toMonoidHom.comp
        (toLinSU h n) := by
    apply MonoidHom.ext
    intro u
    change Matrix.GeneralLinearGroup.toLin
        (((primeFormConjSU h (idGram K n) X) u : ↥(gramSU h (idGram K n))) : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K) *
        Matrix.GeneralLinearGroup.toLin
          ((u : ↥(gramSU h (idGram K n))) : GL (Fin n) K) *
        (Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K))⁻¹
    have h1 : ((((primeFormConjSU h (idGram K n) X) u : ↥(gramSU h (idGram K n))) :
        GL (Fin n) K)) =
        (X : GL (Fin n) K) * ((u : ↥(gramSU h (idGram K n))) : GL (Fin n) K) *
          (X : GL (Fin n) K)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
  have hpush : ((unitaryPreimageBlock h (x := x) (a : K[X])).map
        (primeFormConjSU h (idGram K n) X).toMonoidHom).map (toLinSU h n) =
      (specialBlock (idForm h n) x (a : K[X])).map
        (MulAut.conj (Matrix.GeneralLinearGroup.toLin (X : GL (Fin n) K))).toMonoidHom := by
    rw [Subgroup.map_map, ← hFmap, Subgroup.map_map, ← hhom]
  rw [← hpush, hPeq, hFmap]

end Concrete

section Commute

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem eq_scalar_commutator_of_commute_primeFormConjHom
    (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 3 ≤ n)
    {A X : primeFormUnitary h (idGram K n)}
    (hcomm : Commute (primeFormConjHom h (idGram K n) A)
      (primeFormConjHom h (idGram K n) X)) :
    ∃ μ : Kˣ, (X : GL (Fin n) K) * (A : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.scalar (Fin n) μ *
        ((A : GL (Fin n) K) * (X : GL (Fin n) K)) := by
  classical
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  have hcomm' : primeFormConjHom h (idGram K n) (X * A * X⁻¹ * A⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm.eq]
    group
  obtain ⟨μ, -, hμ⟩ := eq_scalar_of_primeFormConjHom_eq_one h hC hn hcomm'
  refine ⟨μ, ?_⟩
  have hXA : (X : GL (Fin n) K) * (A : GL (Fin n) K) =
      (((X * A * X⁻¹ * A⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K)) *
        ((A : GL (Fin n) K) * (X : GL (Fin n) K)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv]
    group
  rw [hXA, hμ]

end Commute

section Quotient

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData ℓ f K)

noncomputable def specialBlockEquiv
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (H : UnitaryPrimaryData h.bar (idForm h n) x)
    (a : primaryFactors (x : Module.End K (Fin n → K))) (hq : 2 ≤ ℓ ^ f)
    (ha : IsGoodBlock h x a) :
    ↥(unitaryPreimageBlock h (x := x) (a : K[X])) ≃*
      ↥(specialBlock (idForm h n) x (a : K[X])) :=
  (Subgroup.equivMapOfInjective _ (toLinSU h n) toLinSU_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self fun g hg =>
      mem_range_toLinSU (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a ha hg)))

theorem specialBlockEquiv_apply_coe
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (H : UnitaryPrimaryData h.bar (idForm h n) x)
    (a : primaryFactors (x : Module.End K (Fin n → K))) (hq : 2 ≤ ℓ ^ f)
    (ha : IsGoodBlock h x a)
    (u : ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) :
    ((specialBlockEquiv h H a hq ha u : ↥(specialBlock (idForm h n) x (a : K[X]))) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) = toLinSU h n u := by
  simp only [specialBlockEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
  exact Subgroup.coe_equivMapOfInjective_apply (unitaryPreimageBlock h (x := x) (a : K[X]))
    (toLinSU h n) toLinSU_injective u

theorem subgroupMap_mk'_surjective_ker_le_center
    {x : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (a : primaryFactors (x : Module.End K (Fin n → K))) :
    Function.Surjective (MonoidHom.subgroupMap
        (QuotientGroup.mk' (unitaryNormOneScalars h n))
        (unitaryPreimageBlock h (x := x) (a : K[X]))) ∧
      (MonoidHom.subgroupMap (QuotientGroup.mk' (unitaryNormOneScalars h n))
        (unitaryPreimageBlock h (x := x) (a : K[X]))).ker ≤
        Subgroup.center ↥(unitaryPreimageBlock h (x := x) (a : K[X])) := by
  classical
  constructor
  · exact MonoidHom.subgroupMap_surjective _ _
  · intro u hu
    rw [MonoidHom.mem_ker] at hu
    have h1 : QuotientGroup.mk' (unitaryNormOneScalars h n)
        (u : ↥(gramSU h (idGram K n))) = 1 := congrArg Subtype.val hu
    have h2 : (u : ↥(gramSU h (idGram K n))) ∈ unitaryNormOneScalars h n :=
      (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (u : ↥(gramSU h (idGram K n))) ∈
        Subgroup.center ↥(gramSU h (idGram K n)) :=
      normOneScalars_le_center h _ n h2
    rw [Subgroup.mem_center_iff] at h3 ⊢
    intro w
    exact Subtype.ext (h3 (w : ↥(gramSU h (idGram K n))))

end Quotient

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
