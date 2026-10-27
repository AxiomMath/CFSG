module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.LieType.SeitzGeneration.SpF2

open Matrix CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def tripleSpan (e f r₀ : Fin r ⊕ Fin r → K) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  Submodule.span K {e, f, r₀}

structure Frame (e f r₀ : Fin r ⊕ Fin r → K) : Prop where
  ef : spForm r K e f = 1
  er : spForm r K e r₀ = 0
  fr : spForm r K f r₀ = 0

variable {e f r₀ : Fin r ⊕ Fin r → K}

private theorem Frame.fe (h : Frame e f r₀) : spForm r K f e = -1 := by
  rw [← spForm_isAlt.neg_eq, h.ef]

private theorem Frame.rf (h : Frame e f r₀) : spForm r K r₀ f = 0 := by
  rw [← spForm_isAlt.neg_eq, h.fr, neg_zero]

private theorem Frame.re (h : Frame e f r₀) : spForm r K r₀ e = 0 := by
  rw [← spForm_isAlt.neg_eq, h.er, neg_zero]

private theorem Frame.comb_f (h : Frame e f r₀) (α β ρ : K) :
    spForm r K (α • e + β • f + ρ • r₀) f = α := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h.ef,
    spForm_isAlt.self_eq_zero, h.rf, mul_one, mul_zero, add_zero]

private theorem Frame.e_comb (h : Frame e f r₀) (α β ρ : K) :
    spForm r K e (α • e + β • f + ρ • r₀) = β := by
  simp only [map_add, map_smul, smul_eq_mul, spForm_isAlt.self_eq_zero, h.ef, h.er, mul_one,
    mul_zero, zero_add, add_zero]

private theorem Frame.f_comb (h : Frame e f r₀) (α β ρ : K) :
    spForm r K f (α • e + β • f + ρ • r₀) = -α := by
  simp only [map_add, map_smul, smul_eq_mul, h.fe, spForm_isAlt.self_eq_zero, h.fr, mul_neg,
    mul_one, mul_zero, add_zero]

private theorem Frame.comb_comb (h : Frame e f r₀) (x y c x' y' c' : K) :
    spForm r K (x • e + y • f + c • r₀) (x' • e + y' • f + c' • r₀) = x * y' - y * x' := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    spForm_isAlt.self_eq_zero, h.ef, h.er, h.fr, h.fe, h.re, h.rf]
  ring

theorem Frame.decomp (h : Frame e f r₀) {z : Fin r ⊕ Fin r → K} (hz : z ∈ tripleSpan e f r₀) :
    ∃ c : K, z = spForm r K z f • e + spForm r K e z • f + c • r₀ := by
  obtain ⟨α, β, ρ, rfl⟩ := Submodule.mem_span_triple.mp hz
  exact ⟨ρ, by rw [h.comb_f, h.e_comb]⟩

private theorem spEnd_inv_apply_spEnd (g : StatedSp r K) (y : Fin r ⊕ Fin r → K) :
    spEnd g⁻¹ (spEnd g y) = y := by
  rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply]

@[expose] noncomputable def tripleStab (e f r₀ : Fin r ⊕ Fin r → K) : Subgroup (StatedSp r K) where
  carrier := {g | spEnd g r₀ = r₀ ∧ (tripleSpan e f r₀).map (spEnd g) = tripleSpan e f r₀}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [spEnd_mul, Module.End.mul_apply, hb, ha], by
      rw [spEnd_mul, Module.End.mul_eq_comp, Submodule.map_comp, hb', ha']⟩
  one_mem' := by
    exact ⟨by rw [spEnd_one, Module.End.one_apply], by
      rw [spEnd_one, Module.End.one_eq_id, Submodule.map_id]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(congrArg (spEnd a⁻¹) ha).symm.trans (spEnd_inv_apply_spEnd a r₀), ?_⟩
    calc (tripleSpan e f r₀).map (spEnd a⁻¹)
        = ((tripleSpan e f r₀).map (spEnd a)).map (spEnd a⁻¹) := by rw [ha']
      _ = (tripleSpan e f r₀).map (spEnd a⁻¹ * spEnd a) := by
        rw [Module.End.mul_eq_comp, Submodule.map_comp]
      _ = tripleSpan e f r₀ := by
        rw [← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_eq_id, Submodule.map_id]

@[expose] noncomputable def quotMat (e f : Fin r ⊕ Fin r → K) (g : StatedSp r K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![spForm r K (spEnd g e) f, spForm r K (spEnd g f) f;
    spForm r K e (spEnd g e), spForm r K e (spEnd g f)]

private theorem left_mem_tripleSpan : e ∈ tripleSpan e f r₀ :=
  Submodule.subset_span (Set.mem_insert _ _)

private theorem mid_mem_tripleSpan : f ∈ tripleSpan e f r₀ :=
  Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

private theorem spEnd_mem_tripleSpan {g : StatedSp r K} (hg : g ∈ tripleStab e f r₀)
    {x : Fin r ⊕ Fin r → K} (hx : x ∈ tripleSpan e f r₀) : spEnd g x ∈ tripleSpan e f r₀ := by
  rw [← hg.2]
  exact Submodule.mem_map_of_mem hx

private theorem Frame.exists_spEnd_eq (h : Frame e f r₀) {g : StatedSp r K}
    (hg : g ∈ tripleStab e f r₀) {x : Fin r ⊕ Fin r → K} (hx : x ∈ tripleSpan e f r₀) :
    ∃ c : K, spEnd g x = spForm r K x f • spEnd g e + spForm r K e x • spEnd g f + c • r₀ := by
  obtain ⟨c, hc⟩ := h.decomp hx
  refine ⟨c, ?_⟩
  conv_lhs => rw [hc]
  rw [map_add, map_add, map_smul, map_smul, map_smul, hg.1]

private theorem Frame.spForm_spEnd_f (h : Frame e f r₀) {g : StatedSp r K}
    (hg : g ∈ tripleStab e f r₀) {x : Fin r ⊕ Fin r → K} (hx : x ∈ tripleSpan e f r₀) :
    spForm r K (spEnd g x) f =
      spForm r K (spEnd g e) f * spForm r K x f + spForm r K (spEnd g f) f * spForm r K e x := by
  obtain ⟨c, hc⟩ := h.exists_spEnd_eq hg hx
  rw [hc]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h.rf,
    mul_zero, add_zero]
  ring

private theorem Frame.spForm_e_spEnd (h : Frame e f r₀) {g : StatedSp r K}
    (hg : g ∈ tripleStab e f r₀) {x : Fin r ⊕ Fin r → K} (hx : x ∈ tripleSpan e f r₀) :
    spForm r K e (spEnd g x) =
      spForm r K e (spEnd g e) * spForm r K x f + spForm r K e (spEnd g f) * spForm r K e x := by
  obtain ⟨c, hc⟩ := h.exists_spEnd_eq hg hx
  rw [hc]
  simp only [map_add, map_smul, smul_eq_mul, h.er, mul_zero, add_zero]
  ring

private theorem det_quotMat (h : Frame e f r₀) {g : StatedSp r K} (hg : g ∈ tripleStab e f r₀) :
    (quotMat e f g).det = 1 := by
  obtain ⟨c, hc⟩ := h.decomp (spEnd_mem_tripleSpan hg left_mem_tripleSpan)
  obtain ⟨c', hc'⟩ := h.decomp (spEnd_mem_tripleSpan hg mid_mem_tripleSpan)
  have key := h.comb_comb (spForm r K (spEnd g e) f) (spForm r K e (spEnd g e)) c
    (spForm r K (spEnd g f) f) (spForm r K e (spEnd g f)) c'
  rw [← hc, ← hc', spEnd_isometry, h.ef] at key
  rw [quotMat, Matrix.det_fin_two_of]
  linear_combination -key

private theorem quotMat_one (h : Frame e f r₀) : quotMat e f 1 = 1 := by
  rw [quotMat, spEnd_one, Module.End.one_apply, Module.End.one_apply, h.ef,
    spForm_isAlt.self_eq_zero, spForm_isAlt.self_eq_zero, Matrix.one_fin_two]

private theorem quotMat_mul (h : Frame e f r₀) {g g' : StatedSp r K}
    (hg : g ∈ tripleStab e f r₀) (hg' : g' ∈ tripleStab e f r₀) :
    quotMat e f (g * g') = quotMat e f g * quotMat e f g' := by
  have he := spEnd_mem_tripleSpan hg' left_mem_tripleSpan
  have hf := spEnd_mem_tripleSpan hg' mid_mem_tripleSpan
  simp only [quotMat, spEnd_mul, Module.End.mul_apply]
  rw [Matrix.mul_fin_two, h.spForm_spEnd_f hg he, h.spForm_spEnd_f hg hf, h.spForm_e_spEnd hg he,
    h.spForm_e_spEnd hg hf]

@[expose] noncomputable def quotHom (h : Frame e f r₀) :
    tripleStab e f r₀ →* SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨quotMat e f g, by exact det_quotMat h g.2⟩
  map_one' := by exact Subtype.ext (quotMat_one h)
  map_mul' g g' := by exact Subtype.ext (quotMat_mul h g.2 g'.2)

theorem quotHom_coe (h : Frame e f r₀) (g : tripleStab e f r₀) :
    (quotHom h g : Matrix (Fin 2) (Fin 2) K) = quotMat e f g := rfl

theorem spTransvection_mem_tripleStab {v : Fin r ⊕ Fin r → K} (hv : v ∈ tripleSpan e f r₀)
    (hvr : spForm r K v r₀ = 0) (t : K) : spTransvection v t ∈ tripleStab e f r₀ := by
  have hle : ∀ s : K,
      (tripleSpan e f r₀).map (spEnd (spTransvection v s)) ≤ tripleSpan e f r₀ := by
    rintro s _ ⟨x, hx, rfl⟩
    rw [spEnd_spTransvection]
    exact add_mem hx (Submodule.smul_mem _ _ hv)
  refine ⟨?_, le_antisymm (hle t) fun x hx => ?_⟩
  · rw [spEnd_spTransvection, ← spForm_isAlt.neg_eq, hvr, neg_zero, mul_zero, zero_smul,
      add_zero]
  · refine ⟨spEnd (spTransvection v t)⁻¹ x, ?_, spEnd_spEnd_inv _ x⟩
    rw [spTransvection_inv]
    exact hle (-t) ⟨x, hx, rfl⟩

theorem quotMat_spTransvection (h : Frame e f r₀) (α β ρ t : K) :
    quotMat e f (spTransvection (α • e + β • f + ρ • r₀) t) =
      !![1 + t * α * β, -(t * α ^ 2); t * β ^ 2, 1 - t * α * β] := by
  have h₁ : spForm r K (spEnd (spTransvection (α • e + β • f + ρ • r₀) t) e) f =
      1 + t * α * β := by
    rw [spEnd_spTransvection, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, h.e_comb, h.comb_f, h.ef]
    ring
  have h₂ : spForm r K (spEnd (spTransvection (α • e + β • f + ρ • r₀) t) f) f =
      -(t * α ^ 2) := by
    rw [spEnd_spTransvection, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, h.f_comb, h.comb_f, spForm_isAlt.self_eq_zero]
    ring
  have h₃ : spForm r K e (spEnd (spTransvection (α • e + β • f + ρ • r₀) t) e) = t * β ^ 2 := by
    rw [spEnd_spTransvection, map_add, map_smul, smul_eq_mul, h.e_comb,
      spForm_isAlt.self_eq_zero]
    ring
  have h₄ : spForm r K e (spEnd (spTransvection (α • e + β • f + ρ • r₀) t) f) =
      1 - t * α * β := by
    rw [spEnd_spTransvection, map_add, map_smul, smul_eq_mul, h.f_comb, h.e_comb, h.ef]
    ring
  rw [quotMat, h₁, h₂, h₃, h₄]

end CFSG.LieType.SeitzGeneration.SpF2
