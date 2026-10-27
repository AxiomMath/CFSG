module

public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsHermComm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData sesqUnitaryGroup
  sesqSpecialUnitaryGroup_le)

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type*}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V} (H : UnitaryPrimaryData hK.bar B x)
  {a : primaryFactors (x : Module.End K V)} (hself : dualPoly hK.bar (a : K[X]) = a)

include H hself in
theorem sub_mem_primaryComponent_of_mem_specialBlock {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ specialBlock B x (a : K[X])) (v : V) :
    (g : Module.End K V) v - v ∈ primaryComponent (x : Module.End K V) (a : K[X]) := by
  classical
  have hsq := H.squarefree
  have hO := specialBlock_le_orbitFactor hg
  have hcomm : Commute (g : Module.End K V) (x : Module.End K V) :=
    mem_gl_centralizer.mp (orbitFactor_le_gl_centralizer hO)
  have hv : v = ∑ b ∈ primaryFactors (x : Module.End K V),
      primaryProjection (x : Module.End K V) b v := by
    have h := congrArg (fun T : Module.End K V => T v) (sum_primaryProjection hsq)
    simp only [LinearMap.sum_apply, Module.End.one_apply] at h
    exact h.symm
  rw [hv, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hbv := primaryProjection_mem hsq hb v
  by_cases hba : b = (a : K[X])
  · subst hba
    exact Submodule.sub_mem _ (apply_mem_primaryComponent hcomm hbv) hbv
  · have hbS : b ∉ ({(a : K[X]), dualPoly hK.bar (a : K[X])} : Set K[X]) := by
      rw [hself, Set.pair_eq_singleton, Set.mem_singleton_iff]
      exact hba
    rw [hO.2 b hb hbS _ hbv, sub_self]
    exact Submodule.zero_mem _

private theorem exists_transvection_mem_specialBlock {hE : UnitaryFieldData ℓ
      (f * (a : K[X]).natDegree) (AdjoinRoot (a : K[X]))}
    {Hf : primaryComponent (x : Module.End K V) (a : K[X]) →ₛₗ[hE.bar]
      primaryComponent (x : Module.End K V) (a : K[X]) →ₗ[AdjoinRoot (a : K[X])]
        AdjoinRoot (a : K[X])}
    (hHf : Hf.IsSymm) (φ : orbitFactor B x (a : K[X]) ≃* sesqUnitaryGroup Hf)
    (hφ : ∀ (g : orbitFactor B x (a : K[X])) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
        blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
    {u : primaryComponent (x : Module.End K V) (a : K[X])} (hu : Hf u u = 0)
    {c : AdjoinRoot (a : K[X])} (hc : c + hE.bar c = 0) :
    ∃ g ∈ specialBlock B x (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
      (g : Module.End K V) (v : V) =
        ((v + (c * Hf u v) • u : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
  have hT : CFSG.LinearGroups.hermTransvectionGL Hf hu c ∈ sesqUnitaryGroup Hf :=
    sesqSpecialUnitaryGroup_le Hf
      ((CFSG.LinearGroups.hermitian_unitary_transvection hE hHf hu).2.1 c hc)
  set g := φ.symm ⟨_, hT⟩ with hgdef
  have hφg : φ g = ⟨_, hT⟩ := MulEquiv.apply_symm_apply φ _
  refine ⟨(g : LinearMap.GeneralLinearGroup K V), ?_, fun v => ?_⟩
  · refine mem_specialBlock.mpr ⟨g.2, orbitFactor_le_gl_centralizer g.2, ?_⟩
    have hres : blockRestrict x (a : K[X])
        ⟨(g : LinearMap.GeneralLinearGroup K V), orbitFactor_le_gl_centralizer g.2⟩ =
          (φ g : blockGL (x : Module.End K V) (a : K[X])) :=
      blockGL_ext fun v hv => (hφ g v hv).symm
    change blockGLDet (x : Module.End K V) (a : K[X]) (blockRestrict x (a : K[X]) _) = 1
    rw [hres, hφg]
    apply Units.ext
    exact CFSG.LinearGroups.det_hermTransvection Hf hu c
  · rw [← hφ g v v.2, hφg]
    change ((CFSG.LinearGroups.hermTransvection Hf u c v :
      primaryComponent (x : Module.End K V) (a : K[X])) : V) = _
    rw [CFSG.LinearGroups.hermTransvection_apply]

include H hself in
theorem primaryComponent_le_closure_specialBlock (hℓ : ℓ ≠ 2) (hgood : IsGoodBlock hK x a) :
    (primaryComponent (x : Module.End K V) (a : K[X])).toAddSubgroup ≤
      AddSubgroup.closure {w | ∃ g ∈ specialBlock B x (a : K[X]), ∃ v,
        (g : Module.End K V) v - v = w} := by
  classical
  obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, -⟩ :=
    exists_selfDualFactor hself (CFSG.RankThree.PartOne.selfDualPrimaryBlock H a hself)
  set C := AddSubgroup.closure {w | ∃ g ∈ specialBlock B x (a : K[X]), ∃ v,
    (g : Module.End K V) v - v = w} with hCdef
  have hmult : ∀ u : primaryComponent (x : Module.End K V) (a : K[X]), Hf u u = 0 →
      ∀ e : AdjoinRoot (a : K[X]),
        ((e • u : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ C := by
    intro u hu e
    by_cases hu0 : u = 0
    · rw [hu0, smul_zero, ZeroMemClass.coe_zero]
      exact C.zero_mem
    obtain ⟨c₀, hc₀, hc₀t⟩ := hermComm_exists_traceZero hE
    obtain ⟨v₁, hv₁⟩ : ∃ v₁, Hf u v₁ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu0 (hHfl u hcon)
    set v₀ := ((c₀⁻¹ * e) * (Hf u v₁)⁻¹) • v₁ with hv₀def
    have hv₀ : Hf u v₀ = c₀⁻¹ * e := by
      rw [hv₀def, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hv₁, mul_one]
    obtain ⟨g, hg, hgT⟩ := exists_transvection_mem_specialBlock hHf φ hφ hu hc₀t
    refine AddSubgroup.subset_closure ⟨g, hg, v₀, ?_⟩
    rw [hgT v₀, Submodule.coe_add, add_sub_cancel_left, hv₀, ← mul_assoc,
      mul_inv_cancel₀ hc₀, one_mul]
  have hspan := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.span_isotropic_eq_top hE hHf
    hHfl hgood.1
  have key : ∀ y ∈ Submodule.span (AdjoinRoot (a : K[X]))
      {v : primaryComponent (x : Module.End K V) (a : K[X]) | v ≠ 0 ∧ Hf v v = 0},
      ∀ e : AdjoinRoot (a : K[X]),
        ((e • y : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ C := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hmult y hy.2
    | zero =>
      intro e
      rw [smul_zero, ZeroMemClass.coe_zero]
      exact C.zero_mem
    | add y z _ _ hy hz =>
      intro e
      rw [smul_add, Submodule.coe_add]
      exact C.add_mem (hy e) (hz e)
    | smul c y _ hy =>
      intro e
      rw [smul_smul]
      exact hy (e * c)
  intro w hw
  have hw' : (⟨w, hw⟩ : primaryComponent (x : Module.End K V) (a : K[X])) ∈
      Submodule.span (AdjoinRoot (a : K[X]))
        {v : primaryComponent (x : Module.End K V) (a : K[X]) | v ≠ 0 ∧ Hf v v = 0} := by
    rw [hspan]
    exact Submodule.mem_top
  simpa using key _ hw' 1

include H hself in
theorem specialBlock_selfDual_commutant (hℓ : ℓ ≠ 2) (hgood : IsGoodBlock hK x a) (s : V →+ V)
    (hsinj : Function.Injective s)
    (hs : ∀ g ∈ specialBlock B x (a : K[X]), ∀ v,
      s ((g : Module.End K V) v) = (g : Module.End K V) (s v))
    (hsW : ∀ w ∈ primaryComponent (x : Module.End K V) (a : K[X]),
      s w ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (θ : AdjoinRoot (a : K[X]) →+* AdjoinRoot (a : K[X]))
    (hθ : ∀ (e : AdjoinRoot (a : K[X])) (w : primaryComponent (x : Module.End K V) (a : K[X])),
      s ((e • w : primaryComponent (x : Module.End K V) (a : K[X])) : V) =
        ((θ e • (⟨s w, hsW w w.2⟩ : primaryComponent (x : Module.End K V) (a : K[X])) :
          primaryComponent (x : Module.End K V) (a : K[X])) : V)) :
    (∀ e : AdjoinRoot (a : K[X]), e ^ ((ℓ ^ f) ^ (a : K[X]).natDegree) = e → θ e = e) ∧
      (θ = RingHom.id _ → ∃ c : AdjoinRoot (a : K[X]),
        ∀ w : primaryComponent (x : Module.End K V) (a : K[X]),
          s (w : V) = ((c • w : primaryComponent (x : Module.End K V) (a : K[X])) : V)) := by
  classical
  obtain ⟨hE, Hf, hHf, hHfl, φ, hφ, -⟩ :=
    exists_selfDualFactor hself (CFSG.RankThree.PartOne.selfDualPrimaryBlock H a hself)
  let sW : primaryComponent (x : Module.End K V) (a : K[X]) →+
      primaryComponent (x : Module.End K V) (a : K[X]) :=
    { toFun := fun w => ⟨s (w : V), hsW w w.2⟩
      map_zero' := Subtype.ext (map_zero s)
      map_add' := fun w w' => Subtype.ext (map_add s (w : V) (w' : V)) }
  have hsWinj : Function.Injective sW := fun w w' h =>
    Subtype.ext (hsinj (congrArg Subtype.val h))
  have hsWsmul : ∀ (e : AdjoinRoot (a : K[X])) (w : primaryComponent (x : Module.End K V)
      (a : K[X])), sW (e • w) = θ e • sW w := fun e w => Subtype.ext (hθ e w)
  have hcomm : ∀ u : primaryComponent (x : Module.End K V) (a : K[X]), Hf u u = 0 →
      ∀ c : AdjoinRoot (a : K[X]), c + hE.bar c = 0 →
        ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
          sW (v + (c * Hf u v) • u) = sW v + (c * Hf u (sW v)) • u := by
    intro u hu c hc v
    obtain ⟨g, hg, hgT⟩ := exists_transvection_mem_specialBlock hHf φ hφ hu hc
    apply Subtype.ext
    have h1 := hs g hg v
    rw [hgT v] at h1
    change s ((v + (c * Hf u v) • u : primaryComponent (x : Module.End K V) (a : K[X])) : V) = _
    rw [h1]
    exact hgT (sW v)
  obtain ⟨h1, h2⟩ := hermComm hE hℓ hHf hHfl θ sW hsWsmul hcomm hgood.1 hsWinj
  refine ⟨fun e he => h1 e (by rw [UnitaryFieldData.bar_apply, pow_mul]; exact he),
    fun hθid => ?_⟩
  obtain ⟨c, hc⟩ := h2 hθid
  exact ⟨c, fun w => congrArg Subtype.val (hc w)⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
