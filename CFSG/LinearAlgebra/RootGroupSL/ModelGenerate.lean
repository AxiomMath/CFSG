module

public import CFSG.LinearAlgebra.RootGroupSL.ModelBasic
public import CFSG.LinearAlgebra.RootGroupSL.TransvecSL
public import CFSG.LinearAlgebra.RootGroupSL.SLTransitive
import CFSG.RankThree.Classical.SteinbergBJBlockMixingGeneration
import TauCeti.RingTheory.Trace.Dual

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open scoped commutatorElement BigOperators

private lemma transvecSL_zero_vec {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (f : Module.Dual k V) : transvecSL (0 : V) f = 1 := by
  apply SpecialLinearGroup.ext
  intro x
  rw [transvecSL_apply (by simp : f (0 : V) = 0)]
  simp

private lemma transvecSL_zero_form {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (w : V) : transvecSL w (0 : Module.Dual k V) = 1 := by
  apply SpecialLinearGroup.ext
  intro x
  rw [transvecSL_apply (by simp : (0 : Module.Dual k V) w = 0)]
  simp

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀] [Finite k] [Finite E] [CharP k 2]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

private lemma trace_comp_restrictSL_inv (B : SpecialLinearGroup E VJ) (l₀ l : VJ →ₗ[E] E)
    (h : ∀ v, l (B v) = l₀ v) :
    (Algebra.trace k E).comp (l₀.restrictScalars k) ∘ₗ
        (SpecialLinearGroup.toLinearEquiv
          ((restrictSL (E := E) (VJ := VJ) k B)⁻¹)).toLinearMap =
      (Algebra.trace k E).comp (l.restrictScalars k) := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars]
  have hx : (SpecialLinearGroup.toLinearEquiv
        ((restrictSL (E := E) (VJ := VJ) k B)⁻¹)).toLinearMap x =
      (B⁻¹ : SpecialLinearGroup E VJ) x := by
    rw [map_inv]
    rfl
  rw [hx]
  have hx' : (B : VJ ≃ₗ[E] VJ) ((B⁻¹ : SpecialLinearGroup E VJ) x) = x := by
    rw [SpecialLinearGroup.coe_inv]
    exact LinearEquiv.apply_symm_apply _ x
  have h' := h ((B⁻¹ : SpecialLinearGroup E VJ) x)
  dsimp only at h'
  rw [hx'] at h'
  dsimp only
  rw [← h']

private lemma transvec_mem_of_incident (hm : 3 ≤ Module.finrank E VJ)
    (H : Subgroup (SpecialLinearGroup k (VJ × V₀))) (hJ : modelJ k E VJ V₀ ≤ H) {w₀ : VJ}
    {l₀ : VJ →ₗ[E] E} (hw₀ : w₀ ≠ 0) (hl₀ : l₀ ≠ 0) (h0 : l₀ w₀ = 0)
    (hbase : blockSLk k V₀
      (transvecSL w₀ ((Algebra.trace k E).comp (l₀.restrictScalars k))) ∈ H)
    (w : VJ) (l : VJ →ₗ[E] E) (hlw : l w = 0) :
    blockSLk k V₀ (transvecSL w ((Algebra.trace k E).comp (l.restrictScalars k))) ∈ H := by
  by_cases hw : w = 0
  · subst hw
    rw [transvecSL_zero_vec, map_one]
    exact H.one_mem
  by_cases hl : l = 0
  · subst hl
    have hzero : (Algebra.trace k E).comp ((0 : VJ →ₗ[E] E).restrictScalars k) = 0 := by
      ext x
      simp
    rw [hzero, transvecSL_zero_form, map_one]
    exact H.one_mem
  · obtain ⟨B, hBw, hBl⟩ :=
      exists_specialLinear_apply_eq_of_incident hm hw₀ hw hl₀ hl h0 hlw
    have hcond : ((Algebra.trace k E).comp (l₀.restrictScalars k)) w₀ = 0 := by
      simp [h0]
    have hconj : blockSLk k V₀ (restrictSL (E := E) (VJ := VJ) k B) *
        blockSLk k V₀
          (transvecSL w₀ ((Algebra.trace k E).comp (l₀.restrictScalars k))) *
        (blockSLk k V₀ (restrictSL (E := E) (VJ := VJ) k B))⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hJ ⟨B, rfl⟩) hbase) (H.inv_mem (hJ ⟨B, rfl⟩))
    have hgw : (restrictSL (E := E) (VJ := VJ) k B) w₀ = w := by
      change (B : VJ ≃ₗ[E] VJ) w₀ = w
      exact hBw
    have hform := trace_comp_restrictSL_inv (k := k) B l₀ l hBl
    have hconj_eq : blockSLk k V₀ (restrictSL (E := E) (VJ := VJ) k B) *
        blockSLk k V₀
          (transvecSL w₀ ((Algebra.trace k E).comp (l₀.restrictScalars k))) *
        (blockSLk k V₀ (restrictSL (E := E) (VJ := VJ) k B))⁻¹ =
        blockSLk k V₀ (transvecSL w ((Algebra.trace k E).comp (l.restrictScalars k))) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      rw [transvecSL_conj (restrictSL (E := E) (VJ := VJ) k B) hcond, hgw, hform]
    rw [hconj_eq] at hconj
    exact hconj

private lemma transvec_mem_all (hm : 3 ≤ Module.finrank E VJ)
    (H : Subgroup (SpecialLinearGroup k (VJ × V₀))) (hJ : modelJ k E VJ V₀ ≤ H) {w₀ : VJ}
    {l₀ : VJ →ₗ[E] E} (hw₀ : w₀ ≠ 0) (hl₀ : l₀ ≠ 0) (h0 : l₀ w₀ = 0)
    (hbase : blockSLk k V₀
      (transvecSL w₀ ((Algebra.trace k E).comp (l₀.restrictScalars k))) ∈ H)
    (w : VJ) (f : Module.Dual k VJ) (hfw : f w = 0) :
    blockSLk k V₀ (transvecSL w f) ∈ H := by
  by_cases hf : f = 0
  · subst hf
    rw [transvecSL_zero_form, map_one]
    exact H.one_mem
  by_cases hw : w = 0
  · subst hw
    rw [transvecSL_zero_vec, map_one]
    exact H.one_mem
  · let l : VJ →ₗ[E] E := (Module.Dual.traceCompEquiv k E VJ).symm f
    have hlf : (Module.Dual.traceCompEquiv k E VJ) l = f :=
      LinearEquiv.apply_symm_apply _ f
    have hfl (v : VJ) : f v = Algebra.trace k E (l v) := by
      rw [← congrArg (fun g : Module.Dual k VJ => g v) hlf]
      exact Module.Dual.traceCompEquiv_apply l v
    have hl : l ≠ 0 := by
      intro h0l
      apply hf
      rw [← hlf, h0l, map_zero]
    have hnotle : ¬ LinearMap.ker l ≤ Submodule.span E ({w} : Set VJ) := by
      intro hle
      have h1 : Module.finrank E (LinearMap.ker l) ≤
          Module.finrank E (Submodule.span E ({w} : Set VJ)) :=
        Submodule.finrank_mono hle
      have hspan1 : Module.finrank E (Submodule.span E ({w} : Set VJ)) = 1 :=
        finrank_span_singleton hw
      have hrange : Module.finrank E (LinearMap.range l) = 1 := by
        rw [Module.Dual.range_eq_top_of_ne_zero hl, finrank_top E E,
          CommSemiring.finrank_self E]
      have hker : Module.finrank E (LinearMap.ker l) = Module.finrank E VJ - 1 := by
        have hsum := LinearMap.finrank_range_add_finrank_ker l
        rw [hrange] at hsum
        omega
      omega
    obtain ⟨v, hvker, hvnotmem⟩ := SetLike.not_le_iff_exists.mp hnotle
    have hlv : l v = 0 := LinearMap.mem_ker.mp hvker
    obtain ⟨f₀, hf₀v, hf₀w⟩ :=
      (Submodule.span E ({w} : Set VJ)).exists_dual_map_eq_bot_of_notMem hvnotmem
        (inferInstance : Module.Projective E (VJ ⧸ Submodule.span E ({w} : Set VJ)))
    have hf₀w0 : f₀ w = 0 := by
      have hmem : f₀ w ∈ (Submodule.span E ({w} : Set VJ)).map f₀ :=
        ⟨w, Submodule.subset_span (by simp), rfl⟩
      rw [hf₀w] at hmem
      exact hmem
    let mu : VJ →ₗ[E] E := (f₀ v)⁻¹ • f₀
    have hmuw : mu w = 0 := by simp [mu, hf₀w0]
    have hmuv : mu v = 1 := by simp [mu, hf₀v]
    obtain ⟨c, hc⟩ := Algebra.trace_surjective k E (1 : k)
    let l' : VJ →ₗ[E] E := c • mu
    have hl'w : l' w = 0 := by simp [l', hmuw]
    have hf'w : ((Algebra.trace k E).comp (l'.restrictScalars k)) w = 0 := by
      rw [LinearMap.comp_apply, LinearMap.coe_restrictScalars, hl'w, map_zero]
    have hf'v : ((Algebra.trace k E).comp (l'.restrictScalars k)) v = 1 := by
      rw [LinearMap.comp_apply, LinearMap.coe_restrictScalars]
      have hl'v : l' v = c := by simp [l', hmuv]
      rw [hl'v, hc]
    have hfv : f v = 0 := by rw [hfl v, hlv, map_zero]
    have hA' : blockSLk k V₀
        (transvecSL w ((Algebra.trace k E).comp (l'.restrictScalars k))) ∈ H :=
      transvec_mem_of_incident hm H hJ hw₀ hl₀ h0 hbase w l' hl'w
    have hA : blockSLk k V₀
        (transvecSL v ((Algebra.trace k E).comp (l.restrictScalars k))) ∈ H :=
      transvec_mem_of_incident hm H hJ hw₀ hl₀ h0 hbase v l hlv
    have hl_eq : (Algebra.trace k E).comp (l.restrictScalars k) = f := by
      ext x
      exact (hfl x).symm
    rw [hl_eq] at hA
    have hcomm := commutator_transvecSL (w := w) (v := v) (f := f)
      (f' := (Algebra.trace k E).comp (l'.restrictScalars k)) hf'w hfv hfw hf'v
    have hmem : blockSLk k V₀
        (⁅transvecSL w ((Algebra.trace k E).comp (l'.restrictScalars k)),
          transvecSL v f⁆) ∈ H := by
      rw [map_commutatorElement, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hA' hA) (H.inv_mem hA')) (H.inv_mem hA)
    rw [hcomm] at hmem
    exact hmem

private lemma modelA1Elt_zero : modelA1Elt (0 : V₀ →ₗ[k] VJ) = 1 := by
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  rw [modelA1Elt_apply]
  simp

private lemma modelA2Elt_zero : modelA2Elt (0 : VJ →ₗ[k] V₀) = 1 := by
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  rw [modelA2Elt_apply]
  simp

private lemma modelA1Elt_finset_sum_mem (H : Subgroup (SpecialLinearGroup k (VJ × V₀)))
    {ι : Type} (s : Finset ι) (g : ι → V₀ →ₗ[k] VJ)
    (h : ∀ i, modelA1Elt (g i) ∈ H) :
    modelA1Elt (s.sum g) ∈ H := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, modelA1Elt_zero]
    exact H.one_mem
  · intro i s hi ih
    rw [Finset.sum_insert hi, modelA1Elt_add]
    exact H.mul_mem (h i) ih

private lemma modelA2Elt_finset_sum_mem (H : Subgroup (SpecialLinearGroup k (VJ × V₀)))
    {ι : Type} (s : Finset ι) (g : ι → VJ →ₗ[k] V₀)
    (h : ∀ i, modelA2Elt (g i) ∈ H) :
    modelA2Elt (s.sum g) ∈ H := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, modelA2Elt_zero]
    exact H.one_mem
  · intro i s hi ih
    rw [Finset.sum_insert hi, modelA2Elt_add]
    exact H.mul_mem (h i) ih

private lemma modelA1_smulRight_mem (hm : 2 ≤ Module.finrank E VJ)
    (H : Subgroup (SpecialLinearGroup k (VJ × V₀))) (hJ : modelJ k E VJ V₀ ≤ H) {e₀ : VJ}
    (he : e₀ ≠ 0) (hbase : ∀ f : V₀ →ₗ[k] k, modelA1Elt (f.smulRight e₀) ∈ H)
    (e : VJ) (f : V₀ →ₗ[k] k) : modelA1Elt (f.smulRight e) ∈ H := by
  rcases eq_or_ne e 0 with rfl | he'
  · rw [LinearMap.smulRight_zero, modelA1Elt_zero]
    exact H.one_mem
  · obtain ⟨B, hB⟩ := exists_specialLinear_apply_eq hm he he'
    have hconj : blockSLk k V₀ (restrictSL (E := E) (VJ := VJ) k B) *
        modelA1Elt (f.smulRight e₀) *
        (blockSLk k V₀ (restrictSL (E := E) (VJ := VJ) k B))⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hJ ⟨B, rfl⟩) (hbase f)) (H.inv_mem (hJ ⟨B, rfl⟩))
    have hge : (SpecialLinearGroup.toLinearEquiv
        (restrictSL (E := E) (VJ := VJ) k B)).toLinearMap e₀ = e := by
      change (B : VJ ≃ₗ[E] VJ) e₀ = e
      exact hB
    have hform : (SpecialLinearGroup.toLinearEquiv
          (restrictSL (E := E) (VJ := VJ) k B)).toLinearMap ∘ₗ (f.smulRight e₀) =
        f.smulRight e := by
      ext w
      simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul, hge]
    rw [blockSLk_mul_modelA1Elt_mul_inv, hform] at hconj
    exact hconj

private lemma modelA2_smulRight_mem (hm : 2 ≤ Module.finrank E VJ)
    (H : Subgroup (SpecialLinearGroup k (VJ × V₀))) (hJ : modelJ k E VJ V₀ ≤ H)
    {l₀ : VJ →ₗ[E] E} (hl : l₀ ≠ 0)
    (hbase : ∀ w : V₀,
      modelA2Elt (((Algebra.trace k E).comp (l₀.restrictScalars k)).smulRight w) ∈ H)
    (w : V₀) (f : VJ →ₗ[k] k) : modelA2Elt (f.smulRight w) ∈ H := by
  let l : VJ →ₗ[E] E := (Module.Dual.traceCompEquiv k E VJ).symm f
  have hlf : (Module.Dual.traceCompEquiv k E VJ) l = f :=
    LinearEquiv.apply_symm_apply _ f
  have hfl (v : VJ) : f v = Algebra.trace k E (l v) := by
    rw [← congrArg (fun g : Module.Dual k VJ => g v) hlf]
    exact Module.Dual.traceCompEquiv_apply l v
  have hl_eq : (Algebra.trace k E).comp (l.restrictScalars k) = f := by
    ext x
    exact (hfl x).symm
  by_cases hl0 : l = 0
  · have hf0 : f = 0 := by
      rw [← hl_eq, hl0]
      ext x
      simp
    rw [hf0, LinearMap.zero_smulRight, modelA2Elt_zero]
    exact H.one_mem
  · obtain ⟨B, hB⟩ := exists_specialLinear_comp_eq hm hl hl0
    have hconj : blockSLk k V₀ (restrictSL (E := E) (VJ := VJ) k B) *
        modelA2Elt (((Algebra.trace k E).comp (l₀.restrictScalars k)).smulRight w) *
        (blockSLk k V₀ (restrictSL (E := E) (VJ := VJ) k B))⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hJ ⟨B, rfl⟩) (hbase w)) (H.inv_mem (hJ ⟨B, rfl⟩))
    have hform := trace_comp_restrictSL_inv (k := k) B l₀ l hB
    have hcomp : (((Algebra.trace k E).comp (l₀.restrictScalars k)).smulRight w) ∘ₗ
        (SpecialLinearGroup.toLinearEquiv
          ((restrictSL (E := E) (VJ := VJ) k B)⁻¹)).toLinearMap =
        (((Algebra.trace k E).comp (l₀.restrictScalars k)) ∘ₗ
          (SpecialLinearGroup.toLinearEquiv
            ((restrictSL (E := E) (VJ := VJ) k B)⁻¹)).toLinearMap).smulRight w := by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.smulRight_apply]
    rw [blockSLk_mul_modelA2Elt_mul_inv, hcomp, hform, hl_eq] at hconj
    exact hconj

theorem modelK1_le_of_transvec (hm : 3 ≤ Module.finrank E VJ)
    (H : Subgroup (SpecialLinearGroup k (VJ × V₀))) (hJ : modelJ k E VJ V₀ ≤ H) {w₀ : VJ}
    {l₀ : VJ →ₗ[E] E} (hw₀ : w₀ ≠ 0) (hl₀ : l₀ ≠ 0) (h0 : l₀ w₀ = 0)
    (hbase : blockSLk k V₀
      (transvecSL w₀ ((Algebra.trace k E).comp (l₀.restrictScalars k))) ∈ H) :
    modelK1 k VJ V₀ ≤ H := by
  have htop : H.comap (blockSLk (VJ := VJ) k V₀) = ⊤ := by
    apply eq_top_of_transvecSL_mem
    intro w f hfw
    exact transvec_mem_all hm H hJ hw₀ hl₀ h0 hbase w f hfw
  have hrange : (blockSLk (VJ := VJ) k V₀).range ≤ H := by
    rintro g ⟨B, rfl⟩
    have hB : B ∈ H.comap (blockSLk (VJ := VJ) k V₀) := by
      rw [htop]
      exact Subgroup.mem_top B
    exact hB
  rw [modelK1_eq_range]
  exact hrange

theorem modelA1_le_of_mem (hm : 2 ≤ Module.finrank E VJ)
    (H : Subgroup (SpecialLinearGroup k (VJ × V₀))) (hJ : modelJ k E VJ V₀ ≤ H) {e₀ : VJ}
    (he : e₀ ≠ 0) (hbase : ∀ f : V₀ →ₗ[k] k, modelA1Elt (f.smulRight e₀) ∈ H) :
    modelA1 k VJ V₀ ≤ H := by
  intro g hg
  obtain ⟨φ, rfl⟩ := (mem_modelA1_iff g).mp hg
  let b : Module.Basis (Fin (Module.finrank k V₀)) k V₀ := Module.finBasis k V₀
  have hdecomp : φ = ∑ i, (b.coord i).smulRight (φ (b i)) := by
    ext w
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply, Module.Basis.coord_apply]
    have h : φ (∑ i, b.repr w i • b i) = ∑ i, b.repr w i • φ (b i) := by
      rw [map_sum]
      simp only [map_smul]
    rw [← h, Module.Basis.sum_repr]
  rw [hdecomp]
  refine modelA1Elt_finset_sum_mem H Finset.univ _ ?_
  intro i
  exact modelA1_smulRight_mem hm H hJ he hbase (φ (b i)) (b.coord i)

theorem modelA2_le_of_mem (hm : 2 ≤ Module.finrank E VJ)
    (H : Subgroup (SpecialLinearGroup k (VJ × V₀))) (hJ : modelJ k E VJ V₀ ≤ H)
    {l₀ : VJ →ₗ[E] E} (hl : l₀ ≠ 0)
    (hbase : ∀ w : V₀,
      modelA2Elt (((Algebra.trace k E).comp (l₀.restrictScalars k)).smulRight w) ∈ H) :
    modelA2 k VJ V₀ ≤ H := by
  intro g hg
  obtain ⟨ψ, rfl⟩ := (mem_modelA2_iff g).mp hg
  let b : Module.Basis (Fin (Module.finrank k V₀)) k V₀ := Module.finBasis k V₀
  have hdecomp : ψ = ∑ j, (b.coord j ∘ₗ ψ).smulRight (b j) := by
    ext v
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply, LinearMap.comp_apply, Module.Basis.coord_apply]
    exact (Module.Basis.sum_repr b (ψ v)).symm
  rw [hdecomp]
  refine modelA2Elt_finset_sum_mem H Finset.univ _ ?_
  intro j
  exact modelA2_smulRight_mem hm H hJ hl hbase (b j) (b.coord j ∘ₗ ψ)

end CFSG.LinearAlgebra.RootGroupSL

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open CFSG.RankThree.Classical

variable {k E : Type} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

theorem eq_top_of_blockSLk_and_restrictSL (hE : 2 ≤ Module.finrank k E)
    (H : Subgroup (SpecialLinearGroup k (E × E)))
    (hLeft : (blockSLk (VJ := E) k E).range ≤ H)
    (hRight : ((blockSLk (VJ := E) k E).range.map
      (SpecialLinearGroup.congr_linearEquiv (LinearEquiv.prodComm k E E)).toMonoidHom) ≤ H)
    (hExtension : (restrictSL (E := E) (VJ := E × E) k).range ≤ H) : H = ⊤ := by
  classical
  let H' : Subgroup ((E × E) ≃ₗ[k] (E × E)) :=
    H.map SpecialLinearGroup.toLinearEquiv
  have hSL : ∀ h ∈ H', LinearMap.det (h : (E × E) →ₗ[k] (E × E)) = 1 := by
    rintro h ⟨g, _, rfl⟩
    exact SpecialLinearGroup.det_eq_one g
  have hSLU : ∀ g : E ≃ₗ[k] E, LinearMap.det (g : E →ₗ[k] E) = 1 →
      g.prodCongr (LinearEquiv.refl k E) ∈ H' := by
    intro g hg
    let g' : SpecialLinearGroup k E := ⟨g, by
      apply Units.ext
      rw [LinearEquiv.coe_det, hg, Units.val_one]⟩
    refine Subgroup.mem_map.mpr ⟨blockSLk (VJ := E) k E g', hLeft ⟨g', rfl⟩, ?_⟩
    ext p <;> obtain ⟨v, w⟩ := p <;> simp [g', blockSLk_apply]
  have hSLV : ∀ g : E ≃ₗ[k] E, LinearMap.det (g : E →ₗ[k] E) = 1 →
      (LinearEquiv.refl k E).prodCongr g ∈ H' := by
    intro g hg
    let g' : SpecialLinearGroup k E := ⟨g, by
      apply Units.ext
      rw [LinearEquiv.coe_det, hg, Units.val_one]⟩
    let τ : (E × E) ≃ₗ[k] (E × E) := LinearEquiv.prodComm k E E
    let B : SpecialLinearGroup k (E × E) :=
      SpecialLinearGroup.congr_linearEquiv τ (blockSLk (VJ := E) k E g')
    refine Subgroup.mem_map.mpr ⟨B, ?_, ?_⟩
    · exact hRight ⟨blockSLk (VJ := E) k E g', ⟨g', rfl⟩, rfl⟩
    · ext x <;> obtain ⟨v, w⟩ := x <;>
        simp [B, τ, g', SpecialLinearGroup.congr_linearEquiv_coe_apply,
          LinearEquiv.prodComm_apply, blockSLk_apply]
  have hA1 : modelA1Elt (LinearMap.id : E →ₗ[k] E) ∈ H := by
    have h := hExtension ⟨modelA1Elt (LinearMap.id : E →ₗ[E] E), rfl⟩
    have hrestrict : restrictSL (E := E) (VJ := E × E) k
        (modelA1Elt (LinearMap.id : E →ₗ[E] E)) =
        modelA1Elt (LinearMap.id : E →ₗ[k] E) := by
      apply SpecialLinearGroup.ext
      intro p
      rfl
    rwa [hrestrict] at h
  have hA2 : modelA2Elt (LinearMap.id : E →ₗ[k] E) ∈ H := by
    have h := hExtension ⟨modelA2Elt (LinearMap.id : E →ₗ[E] E), rfl⟩
    have hrestrict : restrictSL (E := E) (VJ := E × E) k
        (modelA2Elt (LinearMap.id : E →ₗ[E] E)) =
        modelA2Elt (LinearMap.id : E →ₗ[k] E) := by
      apply SpecialLinearGroup.ext
      intro p
      rfl
    rwa [hrestrict] at h
  have huB : blockUpper (LinearMap.id : E →ₗ[k] E) ∈ H' := by
    refine Subgroup.mem_map.mpr ⟨modelA1Elt (LinearMap.id : E →ₗ[k] E), hA1, ?_⟩
    ext p <;> obtain ⟨v, w⟩ := p <;> simp [blockUpper_apply, modelA1Elt_apply]
  have hlC : blockLower (LinearMap.id : E →ₗ[k] E) ∈ H' := by
    refine Subgroup.mem_map.mpr ⟨modelA2Elt (LinearMap.id : E →ₗ[k] E), hA2, ?_⟩
    ext p <;> obtain ⟨v, w⟩ := p <;> simp [blockLower_apply, modelA2Elt_apply]
  have hid : (LinearMap.id : E →ₗ[k] E) ≠ 0 := by
    intro h
    have h1 : (1 : E) = 0 := by
      simpa using congrArg (fun f : E →ₗ[k] E => f 1) h
    exact one_ne_zero h1
  have hgen : ∀ g : (E × E) ≃ₗ[k] (E × E),
      g ∈ H' ↔ LinearMap.det (g : (E × E) →ₗ[k] (E × E)) = 1 :=
    special_linear_two_block_mixing_unipotents_generate (K := k) (U := E) (V := E)
      hE hE H' hSL hSLU hSLV (B := LinearMap.id) hid huB (C := LinearMap.id) hid hlC
  refine eq_top_iff.mpr ?_
  intro x _
  obtain ⟨y, hyH, hyx⟩ :=
    Subgroup.mem_map.mp ((hgen (SpecialLinearGroup.toLinearEquiv x)).mpr
      (SpecialLinearGroup.det_eq_one x))
  have hy : y = x := SpecialLinearGroup.toLinearEquiv_injective hyx
  simpa [hy] using hyH

end CFSG.LinearAlgebra.RootGroupSL
