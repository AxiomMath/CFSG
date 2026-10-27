module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix

namespace SpChain

variable {K : Type} [Field K]

variable (K) in
abbrev wedgeSpace : Type := ⋀[K]^2 (Fin 4 → K)

abbrev stdVec (i : Fin 4) : Fin 4 → K := Pi.single i 1

abbrev wedge (v w : Fin 4 → K) : wedgeSpace K := exteriorPower.ιMulti K 2 ![v, w]

theorem wedge_add_left (v₁ v₂ w : Fin 4 → K) : wedge (v₁ + v₂) w = wedge v₁ w + wedge v₂ w :=
  (exteriorPower.ιMulti K 2).map_vecCons_add ![w] v₁ v₂

theorem wedge_smul_left (c : K) (v w : Fin 4 → K) : wedge (c • v) w = c • wedge v w :=
  (exteriorPower.ιMulti K 2).map_vecCons_smul ![w] c v

theorem wedge_add_right (v w₁ w₂ : Fin 4 → K) : wedge v (w₁ + w₂) = wedge v w₁ + wedge v w₂ :=
  ((exteriorPower.ιMulti K 2).curryLeft v).map_vecCons_add ![] w₁ w₂

theorem wedge_smul_right (c : K) (v w : Fin 4 → K) : wedge v (c • w) = c • wedge v w :=
  ((exteriorPower.ιMulti K 2).curryLeft v).map_vecCons_smul ![] c w

theorem wedge_self (v : Fin 4 → K) : wedge v v = 0 :=
  (exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)

theorem wedge_swap (v w : Fin 4 → K) : wedge w v = -wedge v w := by
  have h := (exteriorPower.ιMulti K 2).map_swap ![v, w] (i := 0) (j := 1) (by decide)
  rw [← h]
  congr 1

variable (K) in
@[expose] def wedgeBil : (Fin 4 → K) →ₗ[K] (Fin 4 → K) →ₗ[K] wedgeSpace K :=
  LinearMap.mk₂ K wedge wedge_add_left wedge_smul_left wedge_add_right wedge_smul_right

theorem wedgeBil_apply (v w : Fin 4 → K) : wedgeBil K v w = wedge v w := rfl

theorem eq_sum_stdVec (v : Fin 4 → K) : v = ∑ i, v i • stdVec i := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem wedge_expand (v w : Fin 4 → K) : wedge v w =
    (v 0 * w 1 - v 1 * w 0) • wedge (stdVec 0) (stdVec 1) +
    (v 0 * w 2 - v 2 * w 0) • wedge (stdVec 0) (stdVec 2) +
    (v 0 * w 3 - v 3 * w 0) • wedge (stdVec 0) (stdVec 3) +
    (v 1 * w 2 - v 2 * w 1) • wedge (stdVec 1) (stdVec 2) +
    (v 1 * w 3 - v 3 * w 1) • wedge (stdVec 1) (stdVec 3) +
    (v 2 * w 3 - v 3 * w 2) • wedge (stdVec 2) (stdVec 3) := by
  have h : wedge v w = wedgeBil K (∑ i, v i • stdVec i) (∑ j, w j • stdVec j) := by
    rw [← eq_sum_stdVec, ← eq_sum_stdVec]
    rfl
  rw [h]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [Fin.sum_univ_four]
  simp only [wedgeBil_apply, wedge_self, wedge_swap (stdVec (K := K) 0) (stdVec 1),
    wedge_swap (stdVec (K := K) 0) (stdVec 2), wedge_swap (stdVec (K := K) 0) (stdVec 3),
    wedge_swap (stdVec (K := K) 1) (stdVec 2), wedge_swap (stdVec (K := K) 1) (stdVec 3),
    wedge_swap (stdVec (K := K) 2) (stdVec 3)]
  module

@[expose] def plk (i j : Fin 4) : wedgeSpace K →ₗ[K] K :=
  exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating.compLinearMap (LinearMap.pi ![LinearMap.proj i, LinearMap.proj j]))

theorem plk_ιMulti (i j : Fin 4) (m : Fin 2 → Fin 4 → K) :
    plk i j (exteriorPower.ιMulti K 2 m) = m 0 i * m 1 j - m 0 j * m 1 i := by
  rw [plk, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact det_fin_two _

theorem plk_wedge (i j : Fin 4) (v w : Fin 4 → K) :
    plk i j (wedge v w) = v i * w j - v j * w i :=
  plk_ιMulti i j _

theorem linearMap_ext_wedge {M : Type*} [AddCommGroup M] [Module K M]
    {f g : wedgeSpace K →ₗ[K] M} (h : ∀ v w, f (wedge v w) = g (wedge v w)) : f = g :=
  LinearMap.ext_on_range (exteriorPower.ιMulti_span K 2 (Fin 4 → K)) fun m => by
    rw [show m = ![m 0, m 1] from funext fun i => by fin_cases i <;> rfl]
    exact h (m 0) (m 1)

theorem eq_sum_plk (x : wedgeSpace K) : x =
    plk 0 1 x • wedge (stdVec 0) (stdVec 1) + plk 0 2 x • wedge (stdVec 0) (stdVec 2) +
    plk 0 3 x • wedge (stdVec 0) (stdVec 3) + plk 1 2 x • wedge (stdVec 1) (stdVec 2) +
    plk 1 3 x • wedge (stdVec 1) (stdVec 3) + plk 2 3 x • wedge (stdVec 2) (stdVec 3) := by
  have key : (LinearMap.id : wedgeSpace K →ₗ[K] wedgeSpace K) =
      (plk 0 1).smulRight (wedge (stdVec 0) (stdVec 1)) +
      (plk 0 2).smulRight (wedge (stdVec 0) (stdVec 2)) +
      (plk 0 3).smulRight (wedge (stdVec 0) (stdVec 3)) +
      (plk 1 2).smulRight (wedge (stdVec 1) (stdVec 2)) +
      (plk 1 3).smulRight (wedge (stdVec 1) (stdVec 3)) +
      (plk 2 3).smulRight (wedge (stdVec 2) (stdVec 3)) :=
    linearMap_ext_wedge fun v w => by
      simp only [LinearMap.id_apply, LinearMap.add_apply, LinearMap.smulRight_apply, plk_wedge]
      exact wedge_expand v w
  exact LinearMap.congr_fun key x

theorem ext_plk {x y : wedgeSpace K} (h01 : plk 0 1 x = plk 0 1 y) (h02 : plk 0 2 x = plk 0 2 y)
    (h03 : plk 0 3 x = plk 0 3 y) (h12 : plk 1 2 x = plk 1 2 y) (h13 : plk 1 3 x = plk 1 3 y)
    (h23 : plk 2 3 x = plk 2 3 y) : x = y := by
  rw [eq_sum_plk x, eq_sum_plk y, h01, h02, h03, h12, h13, h23]

theorem plk_stdVec (i j k l : Fin 4) :
    plk i j (wedge (stdVec (K := K) k) (stdVec l)) =
      (if i = k then 1 else 0) * (if j = l then 1 else 0) -
        (if j = k then 1 else 0) * (if i = l then 1 else 0) := by
  rw [plk_wedge]
  simp only [Pi.single_apply]

variable (K) in
@[expose] def wedgeForm : wedgeSpace K →ₗ[K] K := plk 0 3 + plk 1 2

theorem wedgeForm_wedge [CharP K 2] (v w : Fin 4 → K) :
    wedgeForm K (wedge v w) = minorForm K v w := by
  rw [wedgeForm, LinearMap.add_apply, plk_wedge, plk_wedge, minorForm_apply]
  linear_combination (-(v 3 * w 0 + v 2 * w 1)) * (CharTwo.two_eq_zero : (2 : K) = 0)

variable (K) in
@[expose] def wedgeZ : wedgeSpace K :=
  wedge (stdVec 0) (stdVec 3) + wedge (stdVec 1) (stdVec 2)

theorem wedgeForm_wedgeZ [CharP K 2] : wedgeForm K (wedgeZ K) = 0 := by
  rw [wedgeZ, map_add, wedgeForm_wedge, wedgeForm_wedge, minorForm_apply, minorForm_apply]
  simp
  exact CharTwo.add_self_eq_zero 1

@[expose] def wedgeAct (g : Matrix (Fin 4) (Fin 4) K) : wedgeSpace K →ₗ[K] wedgeSpace K :=
  exteriorPower.map 2 (Matrix.toLin' g)

theorem wedgeAct_wedge (g : Matrix (Fin 4) (Fin 4) K) (v w : Fin 4 → K) :
    wedgeAct g (wedge v w) = wedge (g *ᵥ v) (g *ᵥ w) := by
  rw [wedgeAct, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem mulVec_stdVec (g : Matrix (Fin 4) (Fin 4) K) (k i : Fin 4) :
    (g *ᵥ stdVec k) i = g i k := by
  simp [stdVec, Matrix.mulVec_single]

theorem minorForm_mulVec_of_mem {g : GL (Fin 4) K} (hg : g ∈ antiSp K) (v w : Fin 4 → K) :
    minorForm K (glMat g *ᵥ v) (glMat g *ᵥ w) = minorForm K v w := by
  have h := CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mp
    ((mem_antiSp_iff_toLin g).mp hg) v w
  simpa only [GeneralLinearGroup.coe_toLin, mulVecLin_apply] using h

theorem wedgeForm_wedgeAct [CharP K 2] {g : GL (Fin 4) K} (hg : g ∈ antiSp K)
    (x : wedgeSpace K) : wedgeForm K (wedgeAct (glMat g) x) = wedgeForm K x := by
  have key : wedgeForm K ∘ₗ wedgeAct (glMat g) = wedgeForm K :=
    linearMap_ext_wedge fun v w => by
      rw [LinearMap.comp_apply, wedgeAct_wedge, wedgeForm_wedge, wedgeForm_wedge,
        minorForm_mulVec_of_mem hg]
  exact LinearMap.congr_fun key x

theorem wedgeAct_wedgeZ [CharP K 2] {g : GL (Fin 4) K} (hg : g ∈ antiSp K) :
    wedgeAct (glMat g) (wedgeZ K) = wedgeZ K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hJ := mul_minorJ_mul_transpose_of_mem hg
  have hJ' : ∀ i j : Fin 4, glMat g i 0 * glMat g j 3 + glMat g i 1 * glMat g j 2 +
      glMat g i 2 * glMat g j 1 + glMat g i 3 * glMat g j 0 = minorJ K i j := fun i j => by
    rw [← mul_minorJ_mul_transpose_apply, hJ]
  have key : ∀ i j : Fin 4, plk i j (wedgeAct (glMat g) (wedgeZ K)) =
      glMat g i 0 * glMat g j 3 + glMat g i 1 * glMat g j 2 +
        glMat g i 2 * glMat g j 1 + glMat g i 3 * glMat g j 0 := fun i j => by
    rw [wedgeZ, map_add, map_add, wedgeAct_wedge, wedgeAct_wedge, plk_wedge, plk_wedge,
      mulVec_stdVec, mulVec_stdVec, mulVec_stdVec, mulVec_stdVec, mulVec_stdVec, mulVec_stdVec,
      mulVec_stdVec, mulVec_stdVec]
    linear_combination (-(glMat g j 0 * glMat g i 3 + glMat g j 1 * glMat g i 2)) * h2
  refine ext_plk ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · rw [key, hJ', wedgeZ, map_add, plk_stdVec, plk_stdVec, minorJ_apply]
      simp

variable (K) in
abbrev wedgeLine : Submodule K (wedgeSpace K) := K ∙ wedgeZ K

variable (K) in
abbrev wedgeQuot : Submodule K (wedgeSpace K ⧸ wedgeLine K) :=
  (LinearMap.ker (wedgeForm K)).map (wedgeLine K).mkQ

abbrev wedgeVec (A : Fin 4) : wedgeSpace K :=
  wedge (stdVec (minorIdx A).1) (stdVec (minorIdx A).2)

theorem wedgeVec_mem (A : Fin 4) : wedgeVec (K := K) A ∈ LinearMap.ker (wedgeForm K) := by
  rw [LinearMap.mem_ker, wedgeForm, LinearMap.add_apply, plk_stdVec, plk_stdVec]
  fin_cases A <;> simp [minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three]

@[expose] def quotOf {x : wedgeSpace K} (hx : x ∈ LinearMap.ker (wedgeForm K)) :
    wedgeQuot K :=
  ⟨Submodule.Quotient.mk x, x, hx, rfl⟩

@[expose] def quotVec (A : Fin 4) : wedgeQuot K := quotOf (wedgeVec_mem A)

theorem quotOf_eq_sum [CharP K 2] {x : wedgeSpace K} (hx : x ∈ LinearMap.ker (wedgeForm K)) :
    quotOf hx = ∑ A, plk (minorIdx A).1 (minorIdx A).2 x • quotVec A := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine Subtype.ext ?_
  simp only [quotOf, quotVec, Submodule.coe_sum, Submodule.coe_smul]
  rw [← sub_eq_zero]
  have e : Submodule.Quotient.mk x - ∑ A, plk (minorIdx A).1 (minorIdx A).2 x •
      (Submodule.Quotient.mk (wedgeVec A) : wedgeSpace K ⧸ wedgeLine K) =
      (wedgeLine K).mkQ (x - ∑ A, plk (minorIdx A).1 (minorIdx A).2 x • wedgeVec A) := by
    simp only [map_sub, map_sum, map_smul, Submodule.mkQ_apply]
  rw [e, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
  refine ⟨plk 0 3 x, ?_⟩
  have hsum := eq_sum_plk x
  have hκ : plk 0 3 x + plk 1 2 x = 0 := hx
  have h12 : plk 1 2 x = plk 0 3 x := by linear_combination hκ - plk 0 3 x * h2
  rw [h12] at hsum
  simp only [Fin.sum_univ_four, wedgeVec, minorIdx_zero, minorIdx_one, minorIdx_two,
    minorIdx_three, wedgeZ]
  linear_combination (norm := module) -hsum

theorem quotVec_linearIndependent [CharP K 2] : LinearIndependent K (quotVec (K := K)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc' : (wedgeLine K).mkQ (∑ A, c A • wedgeVec A) = 0 := by
    have h := congrArg Subtype.val hc
    simpa only [map_sum, map_smul, Submodule.mkQ_apply, Submodule.coe_sum, Submodule.coe_smul,
      quotVec, quotOf, ZeroMemClass.coe_zero] using h
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton] at hc'
  obtain ⟨t, ht⟩ := hc'
  simp only [Fin.sum_univ_four, wedgeVec, minorIdx_zero, minorIdx_one, minorIdx_two,
    minorIdx_three, wedgeZ] at ht
  intro A
  have h := congrArg (plk (minorIdx A).1 (minorIdx A).2) ht
  fin_cases A <;>
    simpa [minorIdx_zero, minorIdx_one, minorIdx_two, minorIdx_three, plk_stdVec] using h.symm

theorem quotVec_span [CharP K 2] : ⊤ ≤ Submodule.span K (Set.range (quotVec (K := K))) := by
  rintro ⟨q, x, hx, rfl⟩ -
  rw [show (⟨(wedgeLine K).mkQ x, x, hx, rfl⟩ : wedgeQuot K) = quotOf hx from rfl,
    quotOf_eq_sum]
  exact Submodule.sum_mem _ fun A _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨A, rfl⟩)

variable (K) in
@[expose] def wedgeQuotBasis [CharP K 2] : Module.Basis (Fin 4) K (wedgeQuot K) :=
  Module.Basis.mk quotVec_linearIndependent quotVec_span

theorem wedgeQuotBasis_apply [CharP K 2] (A : Fin 4) : wedgeQuotBasis K A = quotVec A :=
  Module.Basis.mk_apply _ _ A

theorem wedgeQuotBasis_repr_quotOf [CharP K 2] {x : wedgeSpace K}
    (hx : x ∈ LinearMap.ker (wedgeForm K)) (A : Fin 4) :
    (wedgeQuotBasis K).repr (quotOf hx) A = plk (minorIdx A).1 (minorIdx A).2 x := by
  have h : quotOf hx = ∑ B, plk (minorIdx B).1 (minorIdx B).2 x • wedgeQuotBasis K B := by
    simp only [wedgeQuotBasis_apply, quotOf_eq_sum]
  rw [h, Module.Basis.repr_sum_self]

theorem wedgeAct_mem_ker [CharP K 2] {g : GL (Fin 4) K} (hg : g ∈ antiSp K)
    {x : wedgeSpace K} (hx : x ∈ LinearMap.ker (wedgeForm K)) :
    wedgeAct (glMat g) x ∈ LinearMap.ker (wedgeForm K) := by
  rw [LinearMap.mem_ker, wedgeForm_wedgeAct hg]
  exact hx

theorem wedgeAct_mem_wedgeLine [CharP K 2] {g : GL (Fin 4) K} (hg : g ∈ antiSp K)
    {x : wedgeSpace K} (hx : x ∈ wedgeLine K) : wedgeAct (glMat g) x ∈ wedgeLine K := by
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, wedgeAct_wedgeZ hg]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

@[expose] def wedgeLineAct [CharP K 2] (g : antiSp K) :
    (wedgeSpace K ⧸ wedgeLine K) →ₗ[K] wedgeSpace K ⧸ wedgeLine K :=
  Submodule.mapQ (wedgeLine K) (wedgeLine K) (wedgeAct (glMat (g : GL (Fin 4) K)))
    fun _ hx => wedgeAct_mem_wedgeLine g.2 hx

theorem wedgeLineAct_mk [CharP K 2] (g : antiSp K) (x : wedgeSpace K) :
    wedgeLineAct g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (wedgeAct (glMat (g : GL (Fin 4) K)) x) :=
  Submodule.mapQ_apply _ _ _ x

variable (K) in
@[expose] def wedgeQuotAct [CharP K 2] (g : antiSp K) : wedgeQuot K →ₗ[K] wedgeQuot K :=
  (wedgeLineAct g).restrict fun _ ⟨x, hx, hxq⟩ => ⟨_, wedgeAct_mem_ker g.2 hx, by
    rw [← hxq, Submodule.mkQ_apply, Submodule.mkQ_apply, wedgeLineAct_mk]⟩

theorem wedgeQuotAct_apply [CharP K 2] (g : antiSp K) (q : wedgeQuot K) (x : wedgeSpace K)
    (hq : (q : wedgeSpace K ⧸ wedgeLine K) = Submodule.Quotient.mk x) :
    (wedgeQuotAct K g q : wedgeSpace K ⧸ wedgeLine K) =
      Submodule.Quotient.mk (wedgeAct (glMat (g : GL (Fin 4) K)) x) := by
  rw [wedgeQuotAct, LinearMap.coe_restrict_apply, hq, wedgeLineAct_mk]

theorem wedgeQuotAct_quotOf [CharP K 2] (g : antiSp K) {x : wedgeSpace K}
    (hx : x ∈ LinearMap.ker (wedgeForm K)) :
    wedgeQuotAct K g (quotOf hx) = quotOf (wedgeAct_mem_ker g.2 hx) :=
  Subtype.ext (wedgeQuotAct_apply g _ x rfl)

theorem toMatrix_wedgeQuotAct [CharP K 2] (g : antiSp K) :
    LinearMap.toMatrix (wedgeQuotBasis K) (wedgeQuotBasis K) (wedgeQuotAct K g) =
      minorMap (glMat (g : GL (Fin 4) K)) := by
  ext A B
  rw [LinearMap.toMatrix_apply, wedgeQuotBasis_apply, quotVec, wedgeQuotAct_quotOf,
    wedgeQuotBasis_repr_quotOf, wedgeAct_wedge, plk_wedge, mulVec_stdVec, mulVec_stdVec,
    mulVec_stdVec, mulVec_stdVec, minorMap_apply]
  ring

end SpChain

open SpChain

theorem characteristic_two_exterior_square_minor_homomorphism {K : Type} [Field K] [CharP K 2] :
    (∃ φ : antiSp K →* antiSp K,
      ∀ g, glMat (φ g : GL (Fin 4) K) = minorMap (glMat (g : GL (Fin 4) K))) ∧
    (∀ v w : Fin 4 → K, wedgeForm K (exteriorPower.ιMulti K 2 ![v, w]) = v ⬝ᵥ (minorJ K *ᵥ w)) ∧
    (∀ κ : ⋀[K]^2 (Fin 4 → K) →ₗ[K] K,
      (∀ v w : Fin 4 → K, κ (exteriorPower.ιMulti K 2 ![v, w]) = v ⬝ᵥ (minorJ K *ᵥ w)) →
        κ = wedgeForm K) ∧
    wedgeZ K = exteriorPower.ιMulti K 2 ![Pi.single 0 1, Pi.single 3 1] +
      exteriorPower.ιMulti K 2 ![Pi.single 1 1, Pi.single 2 1] ∧
    wedgeZ K ∈ LinearMap.ker (wedgeForm K) ∧
    (∀ g : Matrix (Fin 4) (Fin 4) K, wedgeAct g = exteriorPower.map 2 (Matrix.toLin' g)) ∧
    (∀ g ∈ antiSp K, wedgeForm K ∘ₗ wedgeAct (glMat g) = wedgeForm K) ∧
    (∀ g ∈ antiSp K, wedgeAct (glMat g) (wedgeZ K) = wedgeZ K) ∧
    (∀ g ∈ antiSp K, ∀ x ∈ LinearMap.ker (wedgeForm K),
      wedgeAct (glMat g) x ∈ LinearMap.ker (wedgeForm K)) ∧
    (∀ g ∈ antiSp K, ∀ x ∈ K ∙ wedgeZ K, wedgeAct (glMat g) x ∈ K ∙ wedgeZ K) ∧
    wedgeQuot K = (LinearMap.ker (wedgeForm K)).map (K ∙ wedgeZ K).mkQ ∧
    (∀ A : Fin 4, ((wedgeQuotBasis K A : wedgeQuot K) : wedgeSpace K ⧸ K ∙ wedgeZ K) =
      Submodule.Quotient.mk
        (exteriorPower.ιMulti K 2 ![Pi.single (minorIdx A).1 1, Pi.single (minorIdx A).2 1])) ∧
    (∀ (g : antiSp K) (q : wedgeQuot K) (x : wedgeSpace K),
      (q : wedgeSpace K ⧸ K ∙ wedgeZ K) = Submodule.Quotient.mk x →
        (wedgeQuotAct K g q : wedgeSpace K ⧸ K ∙ wedgeZ K) =
          Submodule.Quotient.mk (wedgeAct (glMat (g : GL (Fin 4) K)) x)) ∧
    ∀ g : antiSp K, LinearMap.toMatrix (wedgeQuotBasis K) (wedgeQuotBasis K) (wedgeQuotAct K g) =
      minorMap (glMat (g : GL (Fin 4) K)) := by
  have hκ : ∀ v w : Fin 4 → K, minorForm K v w = v ⬝ᵥ (minorJ K *ᵥ w) := fun v w =>
    Matrix.toBilin'_apply' _ _ _
  refine ⟨⟨minorHom K, glMat_minorHom⟩, fun v w => (wedgeForm_wedge v w).trans (hκ v w),
    fun κ hκ' => linearMap_ext_wedge fun v w => by rw [hκ', wedgeForm_wedge, hκ], rfl,
    wedgeForm_wedgeZ, fun g => rfl,
    fun g hg => LinearMap.ext (wedgeForm_wedgeAct hg), fun g hg => wedgeAct_wedgeZ hg,
    fun g hg x hx => wedgeAct_mem_ker hg hx, fun g hg x hx => wedgeAct_mem_wedgeLine hg hx, rfl,
    fun A => by rw [wedgeQuotBasis_apply]; rfl, fun g q x hq => wedgeQuotAct_apply g q x hq,
    toMatrix_wedgeQuotAct⟩

end CFSG.ComponentClassification.UnbalancedCatalog
