module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

section Blocks

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem l154_pow_pow_eq_of_bar_eq {c : K} (hc : hK.bar c = c) (k : ℕ) : c ^ ((2 ^ f) ^ k) = c := by
  have h1 : c ^ (2 ^ f) = c := by rw [← UnitaryFieldData.bar_apply]; exact hc
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, h1]

theorem l154_selfDual_line (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar (a : K[X]) = a)
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) :
    ∃ N : Module.End K V, N ≠ 0 ∧ ∀ c : K, hK.bar c = c →
      ∃ g ∈ specialBlock B x (a : K[X]),
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1 + c • N := by
  classical
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  obtain ⟨hE, hbarE, -, Hf, hHf, -, -, ⟨e, he⟩, φ, hφ, -⟩ :=
    (selfDualPrimaryBlock H a hself).unitaryForm
  haveI : CharP (AdjoinRoot (a : K[X])) 2 := hE.charP
  set W := primaryComponent (x : Module.End K V) (a : K[X]) with hW
  let i0 : Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])) := ⟨0, by omega⟩
  let i1 : Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := fun h => by simpa [i0, i1] using congrArg Fin.val h
  set v₀ : W := e i0 + e i1 with hv₀
  have hv₀0 : Hf v₀ v₀ = 0 := by
    simp only [hv₀, map_add, LinearMap.add_apply, he, if_neg h01, if_neg h01.symm, ↓reduceIte,
      add_zero, zero_add]
    exact CharTwo.add_self_eq_zero _
  have hsupp : orbitFactor B x (a : K[X]) = supportedUnitary B x {(a : K[X])} := by
    unfold orbitFactor
    rw [hself, Set.pair_eq_singleton]
  have key : ∀ lam : AdjoinRoot (a : K[X]), hE.bar lam = -lam →
      ∃ g ∈ specialBlock B x (a : K[X]),
        (∀ (v : V) (hv : v ∈ W), ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
          v + (((lam * Hf v₀ ⟨v, hv⟩) • v₀ : W) : V)) ∧
        ∀ c ∈ primaryFactors (x : Module.End K V), c ≠ (a : K[X]) → ∀ v ∈ primaryComponent
          (x : Module.End K V) c, ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
    intro lam hlambar
    set fl : Module.Dual (AdjoinRoot (a : K[X])) W := lam • Hf v₀ with hfl
    have hfv : fl v₀ = 0 := by rw [hfl, LinearMap.smul_apply, hv₀0, smul_zero]
    set τ : W ≃ₗ[AdjoinRoot (a : K[X])] W := LinearEquiv.transvection hfv with hτ
    have hτapp : ∀ w : W, τ w = w + (lam * Hf v₀ w) • v₀ := fun w => by
      rw [hτ, LinearEquiv.transvection.apply, hfl, LinearMap.smul_apply, smul_eq_mul]
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
    have hgO : (g : LinearMap.GeneralLinearGroup K V) ∈ orbitFactor B x (a : K[X]) := by
      rw [hsupp]
      exact g.2
    refine ⟨g, ?_, fun v hv => by rw [hga v hv, hτapp, Submodule.coe_add], ?_⟩
    · have hgc := supportedUnitary_le_gl_centralizer _ g.2
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
    · intro c hc hca v hv
      exact g.2.2 c hc (fun h => hca (Set.mem_singleton_iff.1 h)) v hv
  obtain ⟨g₁, hg₁, hg₁a, hg₁o⟩ := key 1 (by rw [map_one, CharTwo.neg_eq])
  refine ⟨((g₁ : LinearMap.GeneralLinearGroup K V) : Module.End K V) - 1, ?_, fun c hc => ?_⟩
  ·
    intro h0
    have h1 : ((g₁ : LinearMap.GeneralLinearGroup K V) : Module.End K V) (e i0 : V) = (e i0 : V) :=
      sub_eq_zero.1 (LinearMap.congr_fun h0 (e i0 : V))
    have hH0 : Hf v₀ (e i0) = 1 := by
      simp only [hv₀, map_add, LinearMap.add_apply, he, ↓reduceIte, if_neg h01.symm, add_zero]
    rw [hg₁a _ (e i0).2, hH0, one_mul] at h1
    have h2 : (((1 : AdjoinRoot (a : K[X])) • v₀ : W) : V) = 0 := by
      have := congrArg (fun y : V => y - (e i0 : V)) h1
      simpa using this
    have h3 : v₀ = 0 := by
      have : (1 : AdjoinRoot (a : K[X])) • v₀ = 0 := Subtype.ext h2
      simpa using this
    have h4 := congrArg (fun w => e.repr w i1) h3
    simp only [hv₀, map_add, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.single_apply,
      if_neg h01, if_neg h01.symm, ↓reduceIte, zero_add, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h4
    exact one_ne_zero h4
  · have hlam : hE.bar (algebraMap K (AdjoinRoot (a : K[X])) c) =
        -(algebraMap K (AdjoinRoot (a : K[X])) c) := by
      rw [hbarE, ← map_pow, l154_pow_pow_eq_of_bar_eq hc, CharTwo.neg_eq]
    obtain ⟨g, hg, hga, hgo⟩ := key _ hlam
    refine ⟨g, hg, ?_⟩
    refine ext_primaryComponent H.squarefree fun b hb v hv => ?_
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, LinearMap.sub_apply]
    by_cases hba : b = (a : K[X])
    · subst hba
      rw [hga v hv, hg₁a v hv]
      have e1 : (((algebraMap K (AdjoinRoot (a : K[X])) c * Hf v₀ ⟨v, hv⟩) • v₀ : W) : V) =
          c • (((Hf v₀ ⟨v, hv⟩) • v₀ : W) : V) := by
        rw [mul_smul, coe_algebraMap_smul_primaryComponent]
      rw [e1, one_mul, add_sub_cancel_left]
    · rw [hgo b hb hba v hv, hg₁o b hb hba v hv]
      simp

theorem l154_paired_line (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X]))
    (hm : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X])) :
    ∃ N : Module.End K V, N ≠ 0 ∧ ∀ c : K, hK.bar c = c →
      ∃ g ∈ specialBlock B x (a : K[X]),
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1 + c • N := by
  classical
  haveI : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  set W := primaryComponent (x : Module.End K V) (a : K[X]) with hW
  let bW : Module.Basis (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X])) W := Module.finBasisOfFinrankEq _ _ rfl
  let i0 : Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])) := ⟨0, by omega⟩
  let i1 : Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := fun h => by simpa [i0, i1] using congrArg Fin.val h
  set NE : W →ₗ[AdjoinRoot (a : K[X])] W := Matrix.toLin bW bW (Matrix.single i0 i1 1) with hNE
  have hNE2 : ∀ w : W, NE (NE w) = 0 := by
    intro w
    have e0 : Matrix.single i0 i1 (1 : AdjoinRoot (a : K[X])) * Matrix.single i0 i1 1 = 0 := by
      ext a' d
      rw [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs with h1 h2
      · exact absurd (h2.1.trans h1.2.symm) h01
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [zero_mul]
    have e1 : NE.comp NE = 0 := by
      rw [hNE, ← Matrix.toLin_mul, e0, map_zero]
    exact LinearMap.congr_fun e1 w
  have hNE1 : NE (bW i1) = bW i0 := by
    rw [hNE, Matrix.toLin_self, Finset.sum_eq_single i0]
    · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, one_smul]
    · intro l _ hl
      rw [Matrix.single_apply, if_neg (fun hc => hl hc.1.symm), zero_smul]
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  have key : ∀ c' : AdjoinRoot (a : K[X]), ∃ g ∈ specialBlock B x (a : K[X]),
      (∀ (v : V) (hv : v ∈ W), ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
        v + (((c' • NE ⟨v, hv⟩ : W)) : V)) ∧
      (∀ c ∈ primaryFactors (x : Module.End K V), c ≠ (a : K[X]) → c ≠ dualPoly hK.bar (a : K[X]) →
        ∀ v ∈ primaryComponent (x : Module.End K V) c,
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v) ∧
      (∀ v ∈ primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])),
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈
          primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X]))) ∧
      (∀ v w : V, B (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
        (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) w) = B v w) := by
    intro c'
    set τ := Matrix.SpecialLinearGroup.toLin_equiv bW
      (Matrix.SpecialLinearGroup.transvection h01 c') with hτdef
    have hτ : ∀ w : W, (τ : W ≃ₗ[AdjoinRoot (a : K[X])] W) w = w + c' • NE w := by
      intro w
      have e1 := LinearMap.congr_fun (Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq bW
        (Matrix.SpecialLinearGroup.transvection h01 c')) w
      have hs : (Matrix.single i0 i1 c' : Matrix (Fin (primaryMultiplicity (x : Module.End K V)
          (a : K[X]))) (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
          (AdjoinRoot (a : K[X]))) = c' • Matrix.single i0 i1 1 := by
        ext a' d
        simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
        split_ifs <;> simp
      rw [Matrix.SpecialLinearGroup.transvection_coe, hs, map_add, Matrix.toLin_one, map_smul] at e1
      exact e1
    set τGL : blockGL (x : Module.End K V) (a : K[X]) :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm (τ : W ≃ₗ[AdjoinRoot (a : K[X])] W)
      with hτGL
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
    refine ⟨g, ?_, fun v hv => by rw [hga v hv, hτ, Submodule.coe_add], ?_, ?_, hgB⟩
    · rw [mem_specialBlock]
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
    · intro c hc hca hcd v hv
      exact hgU.2 c hc (by rintro (h | h) <;> [exact hca h; exact hcd h]) v hv
    · intro v hv
      exact apply_mem_primaryComponent hgC hv
  have adj : ∀ (cc : K), hK.bar cc = cc → ∀ (G : Module.End K V),
      (∀ u w : V, B (G u) (G w) = B u w) →
      (∀ (u : V) (hu : u ∈ W), G u = u + cc • ((NE ⟨u, hu⟩ : W) : V)) →
      ∀ (u : W) (v : V), B (u : V) (G v) = B (u : V) v - cc * B ((NE u : W) : V) v := by
    intro cc hcc G hGB hGW u v
    have hGu : G (u : V) = (u : V) + cc • ((NE u : W) : V) := hGW (u : V) u.2
    have hGu' : G ((NE u : W) : V) = ((NE u : W) : V) := by
      rw [hGW ((NE u : W) : V) (NE u).2]
      have : NE ⟨((NE u : W) : V), (NE u).2⟩ = 0 := by
        have h2 := hNE2 u
        exact h2
      rw [this]
      simp
    have e1 : B ((NE u : W) : V) (G v) = B ((NE u : W) : V) v := by
      rw [← hGB ((NE u : W) : V) v, hGu']
    have e2 := hGB (u : V) v
    rw [hGu, map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, e1, hcc,
      smul_eq_mul] at e2
    linear_combination e2
  obtain ⟨g₁, hg₁, hg₁W, hg₁o, hg₁D, hg₁B⟩ := key 1
  set G₁ : Module.End K V := ((g₁ : LinearMap.GeneralLinearGroup K V) : Module.End K V) with hG₁
  have hG₁W : ∀ (u : V) (hu : u ∈ W), G₁ u = u + (1 : K) • ((NE ⟨u, hu⟩ : W) : V) := by
    intro u hu
    rw [hG₁, hg₁W u hu, one_smul, one_smul]
  have hadj₁ := adj 1 (map_one _) G₁ hg₁B hG₁W
  refine ⟨G₁ - 1, ?_, fun c hc => ?_⟩
  ·
    intro h0
    have h1 := LinearMap.congr_fun h0 ((bW i1 : W) : V)
    rw [LinearMap.sub_apply, Module.End.one_apply, hG₁W _ (bW i1).2, one_smul,
      add_sub_cancel_left] at h1
    have h2 : (NE ⟨((bW i1 : W) : V), (bW i1).2⟩ : W) = 0 := Subtype.ext h1
    have h3 : NE (bW i1) = 0 := h2
    rw [hNE1] at h3
    exact bW.ne_zero i0 h3
  · obtain ⟨g, hg, hgW, hgo, hgD, hgB⟩ := key (algebraMap K (AdjoinRoot (a : K[X])) c)
    set G : Module.End K V := ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) with hG
    have hGW : ∀ (u : V) (hu : u ∈ W), G u = u + c • ((NE ⟨u, hu⟩ : W) : V) := by
      intro u hu
      rw [hG, hgW u hu, coe_algebraMap_smul_primaryComponent]
    have hadj := adj c hc G hgB hGW
    refine ⟨g, hg, ?_⟩
    refine ext_primaryComponent H.squarefree fun b hb v hv => ?_
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, LinearMap.sub_apply]
    by_cases hba : b = (a : K[X])
    · subst hba
      rw [hGW v hv, hG₁W v hv, one_smul, add_sub_cancel_left]
    · by_cases hbd : b = dualPoly hK.bar (a : K[X])
      · subst hbd
        have hbd' := dualPoly_mem_primaryFactors H a.2
        set z : V := G v - v - c • (G₁ v - v) with hz
        have hzmem : z ∈ primaryComponent (x : Module.End K V) (dualPoly hK.bar (a : K[X])) := by
          have h1 := hgD v hv
          have h2 := hg₁D v hv
          exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 hv)
            (Submodule.smul_mem _ _ (Submodule.sub_mem _ h2 hv))
        have hz0 : z = 0 := by
          refine eq_zero_of_perfect_right H a.2 hbd' rfl hzmem fun u hu => ?_
          have e1 := hadj ⟨u, hu⟩ v
          have e2 := hadj₁ ⟨u, hu⟩ v
          simp only at e1 e2
          rw [hz, map_sub, map_sub, map_smul, map_sub, e1, e2, smul_eq_mul]
          ring
        have : G v - v = c • (G₁ v - v) := sub_eq_zero.1 hz0
        rw [← this]
        abel
      · rw [hgo b hb hba hbd v hv, hg₁o b hb hba hbd v hv]
        simp

end Blocks

end CFSG.LocalAnalysis.GLTheoremA.K155X
