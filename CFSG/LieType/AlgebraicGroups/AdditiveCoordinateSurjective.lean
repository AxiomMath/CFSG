module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang

import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma end_apply_eq_sum (A : Module.End k (RootModule τ k)) (v : RootModule τ k)
    (a : Label τ) :
    A v a = ∑ b : Label τ, A (Finsupp.single b 1) a * v b := by
  calc A v a = A (∑ b : Label τ, Finsupp.single b (v b)) a := by
        rw [Finsupp.univ_sum_single]
    _ = (∑ b : Label τ, A (Finsupp.single b (v b))) a := by rw [map_sum]
    _ = ∑ b : Label τ, A (Finsupp.single b (v b)) a := by
        rw [Finsupp.coe_finsetSum, Finset.sum_apply]
    _ = ∑ b : Label τ, A (Finsupp.single b 1) a * v b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [show Finsupp.single b (v b) = v b • Finsupp.single b (1 : k) by
          rw [Finsupp.smul_single', mul_one]]
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        ring

private def coordPoly (v : RootModule τ k) (a : Label τ) : GLCoord k (Label τ) :=
  ∑ b : Label τ, algebraMap k (GLCoord k (Label τ)) (v b) * glEntry k (Label τ) a b -
    algebraMap k (GLCoord k (Label τ)) (v a)

omit [IsAlgClosed k] in
private lemma pt_coordPoly (v : RootModule τ k) (a : Label τ) (u : ModGL τ k) :
    SeminaireExp3.ZariskiGL.pt (modGLZariski τ k u) (coordPoly v a) =
      ((u : Module.End k (RootModule τ k)) v a - v a) := by
  rw [pt_modGLZariski]
  simp only [coordPoly, map_sub, map_sum, map_mul, AlgHom.commutes,
    modGLPoint_apply_glEntry, Algebra.algebraMap_self_apply]
  rw [end_apply_eq_sum (u : Module.End k (RootModule τ k)) v a]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by ring

private def shear (s : k) : SeminaireExp3.ZariskiGL (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, s; 0, 1] (by
    simp [Matrix.det_fin_two])

omit [IsAlgClosed k] in
private lemma toGL_shear (s : k) :
    (SeminaireExp3.ZariskiGL.toGL (shear s) : Matrix (Fin 2) (Fin 2) k) = !![1, s; 0, 1] := by
  change (↑(Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, s; 0, 1] _) :
    Matrix (Fin 2) (Fin 2) k) = !![1, s; 0, 1]
  simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

omit [IsAlgClosed k] in
private lemma shear_zero : shear (0 : k) = 1 := by
  apply (SeminaireExp3.ZariskiGL.toGL).injective
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [toGL_shear, map_one]
  fin_cases i <;> fin_cases j <;> simp

omit [IsAlgClosed k] in
private lemma shear_add (s t : k) : shear (s + t) = shear s * shear t := by
  apply (SeminaireExp3.ZariskiGL.toGL).injective
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [map_mul, Matrix.GeneralLinearGroup.coe_mul, toGL_shear]
  simp only [toGL_shear, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [add_comm]

omit [IsAlgClosed k] in
private lemma shear_injective : Function.Injective (shear (k := k)) := by
  intro s t h
  have h' := congrArg (fun g : SeminaireExp3.ZariskiGL (Fin 2) k =>
    (SeminaireExp3.ZariskiGL.toGL g : Matrix (Fin 2) (Fin 2) k) 0 1) h
  simpa [toGL_shear] using h'

private def shearVars : Fin 2 × Fin 2 ⊕ Unit → Polynomial k
  | Sum.inl (i, j) =>
      if i = 0 then (if j = 0 then 1 else if j = 1 then Polynomial.X else 0)
      else if i = 1 then (if j = 1 then 1 else 0) else 0
  | Sum.inr _ => 1

omit [IsAlgClosed k] in
private lemma shearVars_eval (t : k) (x : Fin 2 × Fin 2 ⊕ Unit) :
    (shearVars x).eval t = SeminaireExp3.ZariskiGL.glVec (shear t) x := by
  rcases x with ⟨i, j⟩ | u
  · fin_cases i <;> fin_cases j <;>
      simp [shearVars, SeminaireExp3.ZariskiGL.glVec, toGL_shear, Matrix.det_fin_two]
  · simp [shearVars, SeminaireExp3.ZariskiGL.glVec, toGL_shear, Matrix.det_fin_two]

omit [IsAlgClosed k] in
private lemma shearVars_aeval_eval (P : MvPolynomial (Fin 2 × Fin 2 ⊕ Unit) k) (t : k) :
    (MvPolynomial.aeval (shearVars (k := k)) P).eval t =
      SeminaireExp3.ZariskiGL.eval (shear t) P := by
  change (Polynomial.aeval (R := k) (A := k) t)
      (MvPolynomial.aeval (R := k) (σ := Fin 2 × Fin 2 ⊕ Unit) (S₁ := Polynomial k)
        (shearVars (k := k)) P) =
    MvPolynomial.aeval (R := k) (σ := Fin 2 × Fin 2 ⊕ Unit) (S₁ := k)
      (SeminaireExp3.ZariskiGL.glVec (shear t)) P
  rw [MvPolynomial.comp_aeval_apply]
  have hfun : (fun x => (Polynomial.aeval (R := k) (A := k) t) (shearVars x)) =
      SeminaireExp3.ZariskiGL.glVec (shear t) := by
    funext x
    exact shearVars_eval t x
  rw [hfun]

theorem surjective_coordinate_of_additive {U : Subgroup (ModGL τ k)}
    (hUc : IsPointClosed k (transportPoints (modGLPoint τ k) (U : Set (ModGL τ k))))
    (hUi : IsPointIrreducible k (transportPoints (modGLPoint τ k) (U : Set (ModGL τ k))))
    (v : RootModule τ k) (a : Label τ)
    (hadd : ∀ u ∈ U, ∀ u' ∈ U,
      ((u * u' : ModGL τ k) : Module.End k (RootModule τ k)) v a - v a =
        ((u : Module.End k (RootModule τ k)) v a - v a) +
          ((u' : Module.End k (RootModule τ k)) v a - v a))
    (hne : ∃ u ∈ U, (u : Module.End k (RootModule τ k)) v a ≠ v a) (t : k) :
    ∃ u ∈ U, (u : Module.End k (RootModule τ k)) v a - v a = t := by
  classical
  let e : ModGL τ k ≃* SeminaireExp3.ZariskiGL (Label τ) k := modGLZariski τ k
  let G : Subgroup (SeminaireExp3.ZariskiGL (Label τ) k) := U.map e.toMonoidHom
  let ψ : ModGL τ k → k := fun u => ((u : Module.End k (RootModule τ k)) v a - v a)
  let F : GLCoord k (Label τ) := coordPoly v a
  have hGcoe : (G : Set (SeminaireExp3.ZariskiGL (Label τ) k)) =
      e '' (U : Set (ModGL τ k)) := by
    rw [Subgroup.coe_map, MulEquiv.coe_toMonoidHom]
  have hψ' : ∀ u : ModGL τ k, SeminaireExp3.ZariskiGL.pt (e u) F = ψ u :=
    fun u => pt_coordPoly v a u
  have hψone : ψ 1 = 0 := by
    simp [ψ]
  have hψmul : ∀ u ∈ U, ∀ u' ∈ U, ψ (u * u') = ψ u + ψ u' := by
    intro u hu u' hu'
    simpa [ψ] using hadd u hu u' hu'
  have hψinv : ∀ u ∈ U, ψ u⁻¹ = -ψ u := by
    intro u hu
    have h := hψmul u hu u⁻¹ (U.inv_mem hu)
    rw [mul_inv_cancel] at h
    rw [hψone] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  let S : AddSubgroup k :=
    { carrier := ψ '' (U : Set (ModGL τ k))
      zero_mem' := ⟨1, U.one_mem, hψone⟩
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', U.mul_mem hu hu', hψmul u hu u' hu'⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, U.inv_mem hu, hψinv u hu⟩ }
  have hU'c : IsClosed (G : Set (SeminaireExp3.ZariskiGL (Label τ) k)) := by
    rw [hGcoe]
    exact (isPointClosed_iff_isClosed_image (τ := τ) (k := k)
      (U : Set (ModGL τ k))).1 hUc
  have hU'i : IsIrreducible (G : Set (SeminaireExp3.ZariskiGL (Label τ) k)) := by
    rw [hGcoe]
    exact (isPointIrreducible_iff_isIrreducible_image (τ := τ) (k := k)
      (U : Set (ModGL τ k))).1 hUi
  have hfib : ∀ s : k, IsClosed {g : SeminaireExp3.ZariskiGL (Label τ) k |
      SeminaireExp3.ZariskiGL.pt g F = s} := by
    intro s
    refine (SeminaireExp3.isClosed_iff_exists (A := GLCoord k (Label τ))
      (e := SeminaireExp3.ZariskiGL.pt) SeminaireExp3.ZariskiGL.isInducing_pt).2
      ⟨{F - algebraMap k (GLCoord k (Label τ)) s}, ?_⟩
    ext g
    simp [sub_eq_zero]
  have hSinf : (S : Set k).Infinite := by
    intro hfin
    have hcover : (G : Set (SeminaireExp3.ZariskiGL (Label τ) k)) ⊆
        ⋃₀ (hfin.toFinset.image fun s =>
          (G : Set (SeminaireExp3.ZariskiGL (Label τ) k)) ∩
            {g | SeminaireExp3.ZariskiGL.pt g F = s}) := by
      intro g hg
      rw [hGcoe] at hg
      obtain ⟨u, hu, rfl⟩ := hg
      exact Set.mem_sUnion.2 ⟨_, Finset.mem_image.2
        ⟨ψ u, hfin.mem_toFinset.2 ⟨u, hu, rfl⟩, rfl⟩, ⟨⟨u, hu, rfl⟩, hψ' u⟩⟩
    have hclosed : ∀ z ∈ hfin.toFinset.image (fun s =>
        (G : Set (SeminaireExp3.ZariskiGL (Label τ) k)) ∩
          {g | SeminaireExp3.ZariskiGL.pt g F = s}), IsClosed z := by
      intro z hz
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hz
      exact hU'c.inter (hfib s)
    obtain ⟨z, hz, hGz⟩ := isIrreducible_iff_sUnion_isClosed.1 hU'i _ hclosed hcover
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hz
    have hs0 : s = 0 := by
      have h1 : SeminaireExp3.ZariskiGL.pt (1 : SeminaireExp3.ZariskiGL (Label τ) k) F = s :=
        (hGz (G.one_mem : (1 : SeminaireExp3.ZariskiGL (Label τ) k) ∈ G)).2
      have hψ1 : SeminaireExp3.ZariskiGL.pt (1 : SeminaireExp3.ZariskiGL (Label τ) k) F = 0 := by
        have h := hψ' 1
        rw [map_one] at h
        simpa [hψone] using h
      exact h1.symm.trans hψ1
    obtain ⟨u, hu, hune⟩ := hne
    have hue : e u ∈ (G : Set (SeminaireExp3.ZariskiGL (Label τ) k)) := by
      rw [hGcoe]
      exact ⟨u, hu, rfl⟩
    have hmem : SeminaireExp3.ZariskiGL.pt (e u) F = s := (hGz hue).2
    have hψu := hψ' u
    apply hune
    have hzero : ψ u = 0 := by
      rw [← hψu, hmem, hs0]
    exact sub_eq_zero.mp hzero
  let f : ↥(G : Set (SeminaireExp3.ZariskiGL (Label τ) k)) →
      SeminaireExp3.ZariskiGL (Fin 2) k :=
    fun x => shear (SeminaireExp3.ZariskiGL.pt x.val F)
  have hrange : Set.range f = shear '' (S : Set k) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨SeminaireExp3.ZariskiGL.pt x.val F, ?_, rfl⟩
      have hx : x.val ∈ e '' (U : Set (ModGL τ k)) := hGcoe ▸ x.2
      obtain ⟨u, hu, hux⟩ := hx
      rw [← hux]
      exact ⟨u, hu, (hψ' u).symm⟩
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hs
      refine ⟨⟨e u, ?_⟩, ?_⟩
      · rw [hGcoe]
        exact ⟨u, hu, rfl⟩
      · show shear (SeminaireExp3.ZariskiGL.pt (e u) F) = shear (ψ u)
        rw [hψ' u]
  have hdom0 : SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' Set.range f) := by
    refine SeminaireExp3.ZariskiGL.isDomainImage_range (A := GLCoord k (Label τ))
      (X := SeminaireExp3.ZariskiGL (Label τ) k) (e := SeminaireExp3.ZariskiGL.pt)
      SeminaireExp3.ZariskiGL.isInducing_pt hU'c hU'i f !![1, F; 0, 1] ?_
    intro x
    rw [toGL_shear]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  let φ : Multiplicative S →* SeminaireExp3.ZariskiGL (Fin 2) k :=
    { toFun := fun x => shear (x.toAdd : k)
      map_one' := by
        have h : (((1 : Multiplicative S).toAdd : S) : k) = 0 := by simp
        rw [h, shear_zero]
      map_mul' := by
        intro x y
        have h : ((((x * y).toAdd : S) : k)) = (x.toAdd : k) + (y.toAdd : k) := by simp
        rw [h, shear_add] }
  let H : Subgroup (SeminaireExp3.ZariskiGL (Fin 2) k) := φ.range
  have hHcarrier : (H : Set (SeminaireExp3.ZariskiGL (Fin 2) k)) = shear '' (S : Set k) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x.toAdd : k), x.toAdd.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Multiplicative.ofAdd ⟨s, hs⟩, rfl⟩
  have hHrange : (H : Set (SeminaireExp3.ZariskiGL (Fin 2) k)) = Set.range f :=
    hHcarrier.trans hrange.symm
  have hdom : SeminaireExp3.IsDomainImage k (SeminaireExp3.ZariskiGL.pt '' (H : Set
      (SeminaireExp3.ZariskiGL (Fin 2) k))) := by
    rw [hHrange]
    exact hdom0
  have hHclosed : IsClosed (H : Set (SeminaireExp3.ZariskiGL (Fin 2) k)) :=
    SeminaireExp3.ZariskiGL.isClosed_of_isDomainImage (H := H) hdom
  obtain ⟨Fam, hFam⟩ := SeminaireExp3.ZariskiGL.isClosed_iff.1 hHclosed
  have hqzero : ∀ P ∈ Fam,
      MvPolynomial.aeval (shearVars (k := k)) P = 0 := by
    intro P hP
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine hSinf.mono ?_
    intro s hs
    have hsinH : shear s ∈ (H : Set (SeminaireExp3.ZariskiGL (Fin 2) k)) := by
      rw [hHcarrier]
      exact ⟨s, hs, rfl⟩
    rw [hFam] at hsinH
    have h0 : SeminaireExp3.ZariskiGL.eval (shear s) P = 0 := hsinH P hP
    show (MvPolynomial.aeval (shearVars (k := k)) P).eval s = 0
    rw [shearVars_aeval_eval P s]
    exact h0
  have htS : ∀ t : k, t ∈ S := by
    intro t
    have hsinH : shear t ∈ (H : Set (SeminaireExp3.ZariskiGL (Fin 2) k)) := by
      rw [hFam]
      intro P hP
      rw [← shearVars_aeval_eval P t, hqzero P hP]
      simp
    rw [hHcarrier] at hsinH
    obtain ⟨s, hs, hst⟩ := hsinH
    have hst' : s = t := shear_injective hst
    rwa [← hst']
  obtain ⟨u, hu, hψu⟩ := htS t
  exact ⟨u, hu, hψu⟩

end CFSG.LieType.AlgebraicGroups

