module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

section Transvection

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W]

theorem exists_transvection_of_basis {m : ℕ} (b : Module.Basis (Fin m) E W) (hm : 2 ≤ m) :
    ∃ τ : _root_.SpecialLinearGroup E W, ∃ N : W →ₗ[E] W,
      (∀ w, (τ : W ≃ₗ[E] W) w = w + N w) ∧ (∀ w, N (N w) = 0) ∧
        ∀ c : E, ∃ w, (τ : W ≃ₗ[E] W) w ≠ c • w := by
  classical
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := fun he => by simpa [i0, i1] using congrArg Fin.val he
  set N : W →ₗ[E] W := Matrix.toLin b b (Matrix.single i0 i1 1) with hNdef
  set τ := Matrix.SpecialLinearGroup.toLin_equiv b
    (Matrix.SpecialLinearGroup.transvection h01 (1 : E)) with hτdef
  have hτ : ∀ w : W, (τ : W ≃ₗ[E] W) w = w + N w := by
    intro w
    have e1 := LinearMap.congr_fun (Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq b
      (Matrix.SpecialLinearGroup.transvection h01 (1 : E))) w
    rw [Matrix.SpecialLinearGroup.transvection_coe, map_add, Matrix.toLin_one] at e1
    exact e1
  have hNN : ∀ w : W, N (N w) = 0 := by
    intro w
    have e0 : Matrix.single i0 i1 (1 : E) * Matrix.single i0 i1 1 = 0 := by
      ext a d
      rw [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs with h1 h2
      · exact absurd (h2.1.trans h1.2.symm) h01
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [zero_mul]
    have e1 : N.comp N = 0 := by
      rw [hNdef, ← Matrix.toLin_mul, e0, map_zero]
    exact LinearMap.congr_fun e1 w
  have hN1 : N (b i1) = b i0 := by
    rw [hNdef, Matrix.toLin_self, Finset.sum_eq_single i0]
    · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, one_smul]
    · intro l _ hl
      rw [Matrix.single_apply, if_neg (fun hc => hl hc.1.symm), zero_smul]
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  refine ⟨τ, N, hτ, hNN, fun c => ⟨b i1, fun hc => ?_⟩⟩
  rw [hτ, hN1] at hc
  have e1 := congrArg (fun w => b.repr w i0) hc
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, if_neg h01.symm, if_pos rfl, smul_eq_mul, mul_zero, zero_add] at e1
  exact one_ne_zero e1

end Transvection

section Blocks

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem exists_quadratic_specialBlock_paired (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X]))
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) :
    ∃ g ∈ specialBlock B x (a : K[X]),
      (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) - 1) ^ 2 = 0 ∧
      ¬ ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
          ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
  classical
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  set W := primaryComponent (x : Module.End K V) (a : K[X]) with hW
  let bW : Module.Basis (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X])) W := Module.finBasisOfFinrankEq _ _ rfl
  obtain ⟨τ, N, hτ, hNN, hτs⟩ := exists_transvection_of_basis bW hm
  set τGL : blockGL (x : Module.End K V) (a : K[X]) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm (τ : W ≃ₗ[AdjoinRoot (a : K[X])] W)
    with hτGL
  have hτGLapp : ∀ w : W,
      ((τGL : Module.End (AdjoinRoot (a : K[X])) W) w) = (τ : W ≃ₗ[AdjoinRoot (a : K[X])] W) w :=
    fun w => rfl
  set g := (pairedFactorEquiv H a.2 hne).symm τGL with hgdef
  have hga : ∀ v (hv : v ∈ W), ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
      (((τ : W ≃ₗ[AdjoinRoot (a : K[X])] W) ⟨v, hv⟩ : W) : V) := by
    intro v hv
    rw [← blockApply_pairedFactorEquiv H a.2 hne g v hv, hgdef, MulEquiv.apply_symm_apply]
    rfl
  have hgU := (g : supportedUnitary B x {(a : K[X]), dualPoly hK.bar (a : K[X])}).2
  have hgC : Commute ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
      (x : Module.End K V) := (mem_unitaryCentralizer.mp hgU.1).2
  have hgB : ∀ v w, B (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
      (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) w) = B v w :=
    (mem_unitaryCentralizer.mp hgU.1).1
  have hτinv : ∀ w : W, (τ : W ≃ₗ[AdjoinRoot (a : K[X])] W) (w - N w) = w := by
    intro w
    rw [hτ, map_sub, hNN, sub_zero, sub_add_cancel]
  refine ⟨g, ?_, ?_, ?_⟩
  ·
    rw [mem_specialBlock]
    refine ⟨hgU, hgU.1.2, ?_⟩
    apply Units.ext
    change LinearMap.det ((blockRestrict x (a : K[X]) ⟨g, hgU.1.2⟩ :
      blockGL (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X])) W) = 1
    have hres : blockRestrict x (a : K[X]) ⟨g, hgU.1.2⟩ = τGL := by
      apply blockGL_ext
      intro v hv
      rw [blockApply_blockRestrict]
      exact hga v hv
    rw [hres]
    change LinearMap.det ((τ : W ≃ₗ[AdjoinRoot (a : K[X])] W) :
      Module.End (AdjoinRoot (a : K[X])) W) = 1
    rw [← LinearEquiv.coe_det]
    exact congrArg Units.val τ.2
  ·
    refine ext_primaryComponent H.squarefree fun c hc v hv => ?_
    simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply]
    set G := ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) with hG
    by_cases hca : c = a
    · subst hca
      set w : W := ⟨v, hv⟩ with hw
      have e1 : G v - v = ((N w : W) : V) := by
        rw [hga v hv, hτ, Submodule.coe_add]
        exact add_sub_cancel_left _ _
      have e2 : G ((N w : W) : V) - ((N w : W) : V) = 0 := by
        rw [hga _ (N w).2, hτ, hNN, add_zero]
        exact sub_self _
      rw [e1, e2]
    · by_cases hcd : c = dualPoly hK.bar (a : K[X])
      ·
        subst hcd
        have hz : G (G v - v) - (G v - v) ∈
            primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])) := by
          have h1 := apply_mem_primaryComponent hgC hv
          have h2 := Submodule.sub_mem _ h1 hv
          exact Submodule.sub_mem _ (apply_mem_primaryComponent hgC h2) h2
        set z := G (G v - v) - (G v - v) with hzdef
        have hadj : ∀ (u : W) (y : V), B (u : V) (G y) = B (((u - N u : W)) : V) y := by
          intro u y
          have e := hgB ((u - N u : W) : V) y
          rw [hga _ (u - N u).2] at e
          rw [← e]
          congr 2
          exact (congrArg Subtype.val (hτinv u)).symm
        have hNsub : ∀ u : W, N (u - N u) = N u := fun u => by rw [map_sub, hNN, sub_zero]
        have hBz : ∀ u : W, B (u : V) z = 0 := by
          intro u
          have t1 : B (u : V) (G (G v - v)) =
              B ((u - N u : W) : V) (G v) - B ((u - N u : W) : V) v := by
            rw [hadj, map_sub]
          have t2 : B ((u - N u : W) : V) (G v) = B ((u - N u - N u : W) : V) v := by
            rw [hadj, hNsub]
          have t3 : B (u : V) (G v - v) = B ((u - N u : W) : V) v - B (u : V) v := by
            rw [map_sub, hadj]
          rw [hzdef, map_sub, t1, t2, t3]
          simp only [Submodule.coe_sub, map_sub, LinearMap.sub_apply]
          abel
        have hzsup : z ∈ primaryComponent (x : Module.End K V) (a : K[X]) ⊔
            primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])) :=
          Submodule.mem_sup_right hz
        have hsep := separatingLeft_primaryComponent_sup H a.2 hne
        have hz0 : (⟨z, hzsup⟩ : ↥(primaryComponent (x : Module.End K V) (a : K[X]) ⊔
            primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])))) = 0 := by
          refine hsep _ fun y => ?_
          change B z (y : V) = 0
          obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := Submodule.mem_sup.mp y.2
          rw [← hy, map_add]
          have h1 : B z y₁ = 0 := H.symm.eq_iff.1 (hBz ⟨y₁, hy₁⟩)
          have h2 : B z y₂ = 0 := by
            have hb := dualPoly_mem_primaryFactors H a.2
            have hne' : dualPoly hK.bar (a : K[X]) ≠
                dualPoly hK.bar (dualPoly hK.bar (a : K[X])) := by
              rw [dualPoly_dualPoly_of_mem H a.2]
              exact hne.symm
            exact isotropic_primaryComponent H hb hne' hz hy₂
          rw [h1, h2, add_zero]
        exact congrArg Subtype.val hz0
      ·
        have e1 : G v = v := hgU.2 c hc (by
          rintro (h | h)
          · exact hca h
          · exact hcd h) v hv
        rw [e1, sub_self, map_zero, sub_self]
  ·
    rintro ⟨c, hc⟩
    obtain ⟨w, hw⟩ := hτs c
    apply hw
    apply Subtype.ext
    rw [← hga _ w.2]
    exact hc w

theorem exists_quadratic_specialBlock_selfDual (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a)
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) :
    ∃ g ∈ specialBlock B x (a : K[X]),
      (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) - 1) ^ 2 = 0 ∧
      ¬ ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
          ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
  classical
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  obtain ⟨hE, -, -, Hf, hHf, -, -, ⟨e, he⟩, φ, hφ, -⟩ :=
    (selfDualPrimaryBlock H a hself).unitaryForm
  set W := primaryComponent (x : Module.End K V) (a : K[X]) with hW
  let i0 : Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])) := ⟨0, by omega⟩
  let i1 : Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := fun h => by simpa [i0, i1] using congrArg Fin.val h
  obtain ⟨μ, hμ⟩ := OddUnitaryInvolutionSylow.exists_norm_eq_neg_one hE
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul, eq_comm, neg_eq_zero] at hμ
    exact one_ne_zero hμ
  obtain ⟨c₀, hc₀⟩ := hE.exists_bar_ne
  set lam := c₀ - hE.bar c₀ with hlam
  have hlam0 : lam ≠ 0 := sub_ne_zero.2 (Ne.symm hc₀)
  have hlambar : hE.bar lam = -lam := by
    rw [hlam, map_sub, hE.bar_bar]
    ring
  set v₀ : W := e i0 + μ • e i1 with hv₀
  have hv₀0 : Hf v₀ v₀ = 0 := by
    have e1 : μ * hE.bar μ = -1 := hμ
    simp only [hv₀, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, he,
      if_neg h01, if_neg h01.symm, ↓reduceIte, smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]
    linear_combination e1
  set fl : Module.Dual (AdjoinRoot (a : K[X])) W := lam • Hf v₀ with hfl
  have hfv : fl v₀ = 0 := by rw [hfl, LinearMap.smul_apply, hv₀0, smul_zero]
  set τ : W ≃ₗ[AdjoinRoot (a : K[X])] W := LinearEquiv.transvection hfv with hτ
  have hτapp : ∀ w : W, τ w = w + (lam * Hf v₀ w) • v₀ := fun w => by
    rw [hτ, LinearEquiv.transvection.apply, hfl, LinearMap.smul_apply, smul_eq_mul]
  have hNN : ∀ w : W, (lam * Hf v₀ ((lam * Hf v₀ w) • v₀)) • v₀ = 0 := fun w => by
    rw [map_smul, hv₀0, smul_zero, mul_zero, zero_smul]
  have hτU : ∀ v w : W, Hf (τ v) (τ w) = Hf v w := by
    intro v w
    have hs := hHf.eq v₀ v
    rw [hτapp, hτapp]
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
      hv₀0, map_mul, hlambar, hs, mul_zero, add_zero]
    ring
  set τGL : blockGL (x : Module.End K V) (a : K[X]) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm τ with hτGL
  have hτGLU : τGL ∈ sesqUnitaryGroup Hf := mem_sesqUnitaryGroup.2 fun v w => hτU v w
  set g := φ.symm ⟨τGL, hτGLU⟩ with hgdef
  have hga : ∀ v (hv : v ∈ W), ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
      ((τ ⟨v, hv⟩ : W) : V) := by
    intro v hv
    rw [← hφ g v hv, hgdef, MulEquiv.apply_symm_apply]
    rfl
  have hsupp : orbitFactor B x (a : K[X]) = supportedUnitary B x {(a : K[X])} := by
    unfold orbitFactor
    rw [hself, Set.pair_eq_singleton]
  have hgO : (g : LinearMap.GeneralLinearGroup K V) ∈ orbitFactor B x (a : K[X]) := by
    rw [hsupp]
    exact g.2
  refine ⟨g, ?_, ?_, ?_⟩
  ·
    have hgc := supportedUnitary_le_gl_centralizer _ g.2
    rw [mem_specialBlock]
    refine ⟨hgO, hgc, ?_⟩
    apply Units.ext
    change LinearMap.det ((blockRestrict x (a : K[X]) ⟨g, hgc⟩ :
      blockGL (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X])) W) = 1
    have hres : blockRestrict x (a : K[X]) ⟨g, hgc⟩ = τGL := by
      apply blockGL_ext
      intro v hv
      rw [blockApply_blockRestrict]
      exact hga v hv
    rw [hres]
    change LinearMap.det ((τ : W ≃ₗ[AdjoinRoot (a : K[X])] W) :
      Module.End (AdjoinRoot (a : K[X])) W) = 1
    rw [← LinearEquiv.coe_det, hτ, LinearEquiv.transvection.det_eq_one, Units.val_one]
  ·
    refine ext_primaryComponent H.squarefree fun c hc v hv => ?_
    simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply]
    set G := ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) with hG
    by_cases hca : c = a
    · subst hca
      set w : W := ⟨v, hv⟩ with hw
      have e1 : G v - v = (((lam * Hf v₀ w) • v₀ : W) : V) := by
        rw [hga v hv, hτapp, Submodule.coe_add]
        exact add_sub_cancel_left _ _
      have e2 : G (((lam * Hf v₀ w) • v₀ : W) : V) - (((lam * Hf v₀ w) • v₀ : W) : V) = 0 := by
        rw [hga _ ((lam * Hf v₀ w) • v₀).2, hτapp, hNN, add_zero]
        exact sub_self _
      rw [e1, e2]
    · have e1 : G v = v := g.2.2 c hc (fun h => hca (Set.mem_singleton_iff.1 h)) v hv
      rw [e1, sub_self, map_zero, sub_self]
  ·
    rintro ⟨c, hc⟩
    have h1 : τ (e i0) = c • e i0 := by
      apply Subtype.ext
      rw [← hga _ (e i0).2]
      exact hc (e i0)
    have hH0 : Hf v₀ (e i0) = 1 := by
      simp only [hv₀, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, he, ↓reduceIte,
        if_neg h01.symm, smul_eq_mul, mul_zero, add_zero]
    rw [hτapp, hH0, mul_one] at h1
    have e3 := congrArg (fun w => e.repr w i1) h1
    simp only [hv₀, map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, if_neg h01, ↓reduceIte, smul_eq_mul, mul_zero,
      mul_one, zero_add] at e3
    exact mul_ne_zero hlam0 hμ0 e3

theorem exists_quadratic_specialBlock (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V))
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) :
    ∃ g ∈ specialBlock B x (a : K[X]),
      (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) - 1) ^ 2 = 0 ∧
      ¬ ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
          ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · exact exists_quadratic_specialBlock_selfDual H a hself hm
  · exact exists_quadratic_specialBlock_paired H a (Ne.symm hself) hm

end Blocks

end CFSG.LocalAnalysis.GLTheoremA.S2019
