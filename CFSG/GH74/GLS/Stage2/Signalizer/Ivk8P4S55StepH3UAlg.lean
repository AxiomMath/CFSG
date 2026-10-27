module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3SpAlg
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUElem

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3Sp

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem stdHermForm_eq_dotProduct (x y : Fin n → K) :
    stdHermForm h n x y = (fun i => h.bar (x i)) ⬝ᵥ y := by
  rw [stdHermForm_apply]
  rfl

theorem stdHermForm_uU {A : GL (Fin n) K} (hA : A ∈ uU h n) (x y : Fin n → K) :
    stdHermForm h n ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      stdHermForm h n x y := by
  have hAu := (mem_uU h).1 hA
  have hbarmv : (fun i => h.bar (((A : Matrix (Fin n) (Fin n) K) *ᵥ x) i)) =
      ((A : Matrix (Fin n) (Fin n) K).map h.bar) *ᵥ (fun i => h.bar (x i)) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [stdHermForm_eq_dotProduct, stdHermForm_eq_dotProduct, hbarmv, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hAu, Matrix.vecMul_one]

theorem stdHermForm_smul_left (c : K) (x y : Fin n → K) :
    stdHermForm h n (c • x) y = h.bar c * stdHermForm h n x y := by
  rw [stdHermForm_apply, stdHermForm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem stdHermForm_smul_right (c : K) (x y : Fin n → K) :
    stdHermForm h n x (c • y) = c * stdHermForm h n x y := by
  rw [stdHermForm_apply, stdHermForm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem bar_stdHermForm (x y : Fin n → K) :
    h.bar (stdHermForm h n x y) = stdHermForm h n y x := by
  rw [stdHermForm_apply, stdHermForm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, UnitaryFieldData.bar_bar]
  ring

@[expose] noncomputable def utvMat (w : Fin n → K) (b : K) : Matrix (Fin n) (Fin n) K :=
  1 + b • vecMulVec w (fun i => h.bar (w i))

theorem utvMat_mulVec (w : Fin n → K) (b : K) (x : Fin n → K) :
    utvMat h w b *ᵥ x = x + (b * stdHermForm h n w x) • w := by
  rw [utvMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul, stdHermForm_eq_dotProduct]

theorem utvMat_sub_one_mulVec (w : Fin n → K) (b : K) (x : Fin n → K) :
    (utvMat h w b - 1) *ᵥ x = (b * stdHermForm h n w x) • w := by
  rw [Matrix.sub_mulVec, utvMat_mulVec, Matrix.one_mulVec, add_sub_cancel_left]

theorem utvMat_adj (w : Fin n → K) (b : K) :
    ((utvMat h w b).map h.bar)ᵀ = utvMat h w (h.bar b) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [utvMat, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
      Matrix.one_apply_eq, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, map_add, map_mul,
      map_one, UnitaryFieldData.bar_bar]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp only [utvMat, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
      Matrix.one_apply_ne hij, Matrix.one_apply_ne hji, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, map_add, map_mul, map_zero, UnitaryFieldData.bar_bar]
    ring

theorem utvMat_unitary {w : Fin n → K} (hw : stdHermForm h n w w = 0) {b : K}
    (hb : h.bar b = -b) : ((utvMat h w b).map h.bar)ᵀ * utvMat h w b = 1 := by
  rw [utvMat_adj, hb]
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, utvMat_mulVec,
    utvMat_mulVec, Matrix.one_mulVec]
  rw [map_add, map_smul, hw, smul_eq_mul, mul_zero, add_zero, add_assoc, ← add_smul]
  ring_nf
  simp

theorem utvMat_det {w : Fin n → K} (hw : stdHermForm h n w w = 0) (b : K) :
    (utvMat h w b).det = 1 := by
  have e : utvMat h w b = 1 + vecMulVec w (b • fun i => h.bar (w i)) := by
    rw [utvMat]
    congr 1
    ext i j
    simp [vecMulVec_apply, mul_left_comm]
  rw [e, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, smul_dotProduct,
    smul_eq_mul, ← stdHermForm_eq_dotProduct, hw, mul_zero, add_zero]

@[expose] noncomputable def utvSU {w : Fin n → K} (hw : stdHermForm h n w w = 0) {b : K}
    (hb : h.bar b = -b) : StatedSU n (p ^ f) K :=
  ⟨uGL h (utvMat h w b) (utvMat_unitary h hw hb), (mem_unitarySU_iff h).2
    ⟨utvMat_det h hw b, utvMat_unitary h hw hb⟩⟩

@[expose] def uElatImage (W : Submodule K (Fin n → K)) :
    Subgroup (StatedProj (StatedSU n (p ^ f) K)) :=
  ((glElat W).comap (StatedSU n (p ^ f) K).subtype).map (projH _)

theorem isPGroup_uElatImage {r : ℕ} [CharP K r] (W : Submodule K (Fin n → K)) :
    IsPGroup r ↥(uElatImage (p := p) (f := f) W) :=
  ((isPGroup_glElat W).comap_of_injective _ Subtype.coe_injective).map _

theorem uConjAut_mem_uElatImage (hn : 1 ≤ n) {W : Submodule K (Fin n → K)} (A : uU h n)
    (hA : ∀ w ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (hA' : ∀ w ∈ W,
      (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    {x : StatedProj (StatedSU n (p ^ f) K)} (hx : x ∈ uElatImage W) :
    uConjAut h hn A x ∈ uElatImage W := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [uConjAut_proj]
  refine Subgroup.mem_map_of_mem _ ?_
  rw [Subgroup.mem_comap, Subgroup.coe_subtype]
  exact conj_mem_glElat hA hA' hg

theorem uFieldAut_mem_uElatImage (hn : 1 ≤ n) {w : Fin n → K} (φ : K ≃+* K)
    (hφw : ∀ i, φ (w i) = w i) {x : StatedProj (StatedSU n (p ^ f) K)}
    (hx : x ∈ uElatImage (Submodule.span K {w})) :
    uFieldAut h hn φ x ∈ uElatImage (Submodule.span K {w}) := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [uFieldAut_proj]
  refine Subgroup.mem_map_of_mem _ ?_
  rw [Subgroup.mem_comap, Subgroup.coe_subtype]
  have hg' : ((g : StatedSU n (p ^ f) K) : GL (Fin n) K) ∈ glElat (Submodule.span K {w}) := hg
  obtain ⟨hg1, hg2⟩ := hg'
  set G : Matrix (Fin n) (Fin n) K :=
    (((g : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hG
  have hsub : (((glAut φ ((g : StatedSU n (p ^ f) K) : GL (Fin n) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) - 1) = (G - 1).map φ := by
    rw [coe_glAut, Matrix.map_sub φ (map_sub φ), Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hmap : ∀ v, (((glAut φ ((g : StatedSU n (p ^ f) K) : GL (Fin n) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) - 1) *ᵥ v =
        fun i => φ (((G - 1) *ᵥ (fun j => φ.symm (v j))) i) := by
    intro v
    funext i
    rw [hsub]
    have e := RingHom.map_mulVec (φ : K →+* K) (G - 1) (fun j => φ.symm (v j)) i
    simp only [RingEquiv.coe_toRingHom, Function.comp_def, RingEquiv.apply_symm_apply] at e
    exact e.symm
  have hspan : ∀ u ∈ Submodule.span K {w}, (fun i => φ (u i)) ∈ Submodule.span K {w} := by
    intro u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    refine Submodule.mem_span_singleton.mpr ⟨φ a, ?_⟩
    funext i
    simp [hφw]
  have hspan' : ∀ u ∈ Submodule.span K {w}, (fun i => φ.symm (u i)) ∈ Submodule.span K {w} := by
    intro u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    refine Submodule.mem_span_singleton.mpr ⟨φ.symm a, ?_⟩
    funext i
    have hwi : φ.symm (w i) = w i := by
      rw [RingEquiv.symm_apply_eq]
      exact (hφw i).symm
    simp [hwi]
  refine ⟨fun v => ?_, fun u hu => ?_⟩
  · rw [hmap]
    exact hspan _ (hg1 _)
  · rw [hmap]
    have h0 := hg2 _ (hspan' u hu)
    funext i
    rw [show (G - 1) *ᵥ (fun j => φ.symm (u j)) = 0 from h0]
    simp

theorem proj_utvSU_mem_uElatImage {W : Submodule K (Fin n → K)} {w : Fin n → K}
    (hwW : w ∈ W) (horth : ∀ y ∈ W, stdHermForm h n w y = 0)
    (hw : stdHermForm h n w w = 0) {b : K} (hb : h.bar b = -b) :
    projH _ (utvSU h hw hb) ∈ uElatImage (p := p) (f := f) W := by
  refine Subgroup.mem_map_of_mem _ ?_
  rw [Subgroup.mem_comap, Subgroup.coe_subtype]
  refine ⟨fun v => ?_, fun y hy => ?_⟩
  · change (utvMat h w b - 1) *ᵥ v ∈ W
    rw [utvMat_sub_one_mulVec]
    exact W.smul_mem _ hwW
  · change (utvMat h w b - 1) *ᵥ y = 0
    rw [utvMat_sub_one_mulVec, horth y hy, mul_zero, zero_smul]

theorem proj_utvSU_ne_one {w : Fin n → K} (hw0 : w ≠ 0) (hw : stdHermForm h n w w = 0)
    {b : K} (hb0 : b ≠ 0) (hb : h.bar b = -b) :
    projH (StatedSU n (p ^ f) K) (utvSU h hw hb) ≠ 1 := by
  intro h1
  have hmem := (QuotientGroup.eq_one_iff _).mp h1
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  have hcM : Matrix.scalar (Fin n) (c : K) = utvMat h w b :=
    congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
  have hTw : utvMat h w b *ᵥ w = w := by
    rw [utvMat_mulVec, hw, mul_zero, zero_smul, add_zero]
  have hc1 : (c : K) = 1 := by
    rw [← hcM, scalar_apply] at hTw
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw0 (funext hall)
    have h3 := congrFun hTw i
    rw [mulVec_diagonal] at h3
    exact mul_right_cancel₀ hi (by rw [h3, one_mul])
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hw0 (funext hall)
  have h4 : utvMat h w b *ᵥ (Pi.single i 1) = Pi.single i 1 := by
    rw [← hcM, hc1, map_one, Matrix.one_mulVec]
  rw [utvMat_mulVec, add_eq_left] at h4
  have h5 := congrFun h4 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h5
  have hform : stdHermForm h n w (Pi.single i 1) = h.bar (w i) := by
    rw [stdHermForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  rw [hform] at h5
  have hbw : h.bar (w i) ≠ 0 := by
    intro h0
    apply hi
    have := congrArg h.bar h0
    rwa [UnitaryFieldData.bar_bar, map_zero] at this
  exact (mul_ne_zero (mul_ne_zero hb0 hbw) hi) h5

theorem exists_bar_eq_neg : ∃ b : K, b ≠ 0 ∧ h.bar b = -b := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  refine ⟨c - h.bar c, sub_ne_zero.mpr (Ne.symm hc), ?_⟩
  rw [map_sub, UnitaryFieldData.bar_bar, neg_sub]

theorem exists_isotropic_prime (hn : 3 ≤ n) :
    ∃ w : Fin n → K, w ≠ 0 ∧ stdHermForm h n w w = 0 ∧ ∀ φ : K ≃+* K, ∀ i, φ (w i) = w i := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  obtain ⟨a, c, hac⟩ := ZMod.sq_add_sq p (-1)
  set ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K with hι
  have hfix : ∀ (ψ : K →+* K) (x : ZMod p), ψ (ι x) = ι x := fun ψ x =>
    RingHom.congr_fun (RingHom.ext_zmod (ψ.comp ι) ι) x
  set w' : Fin (m + 3) → ZMod p := Fin.cons 1 (Fin.cons a (Fin.cons c 0)) with hw'
  set w : Fin (m + 3) → K := fun i => ι (w' i) with hw
  refine ⟨w, ?_, ?_, fun φ i => hfix (φ : K →+* K) (w' i)⟩
  · intro h0
    have h1 := congrFun h0 0
    simp [hw, hw'] at h1
  · rw [stdHermForm_apply]
    have hbar : ∀ i, h.bar (w i) = w i := fun i => hfix h.bar (w' i)
    have hK : ι a * ι a + ι c * ι c = -1 := by
      have e := congrArg ι hac
      have e1 : ι (-1) = -1 := by
        have e2 := RingHom.map_neg ι 1
        rw [map_one] at e2
        exact e2
      rw [map_add, map_pow, map_pow, e1] at e
      rw [← e]
      ring
    simp only [hbar]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [hw, hw', Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, map_zero, mul_zero,
      Finset.sum_const_zero, add_zero, map_one, mul_one]
    rw [← add_assoc, add_assoc 1, hK]
    ring

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U
