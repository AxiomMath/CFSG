module

public import CFSG.FeitThompson.Representations.PrimeTILocalTransporterTISet
public import CFSG.FeitThompson.Representations.TIRectangleCoefficientExchange
import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference
import CFSG.FeitThompson.Representations.InductionIntegerIsometryTISupport
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
public import CFSG.FeitThompson.Representations.DadeIntegerIsometry
import CFSG.FeitThompson.Representations.NormalInducedSupportBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}

theorem mem_right_of_notMem_primeTIset {x : L} (hx : x ∈ W₁ ⊔ W₂)
    (hxB : x ∉ primeTIset W₁ W₂) : x ∈ W₂ := by
  by_contra hc
  exact hxB (mem_primeTIset.2 ⟨hx, hc⟩)

theorem cyclicTIDiff_sup_eq_cyclicTIset :
    cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ = cyclicTIset W₁ W₂ := by
  ext x; simp

theorem IsTIWithNormalizer.indClassFun_apply_of_mem [Fintype L] {A : Set L} {M : Subgroup L}
    (hTI : IsTIWithNormalizer A M) {f : ↥M → ℂ} (hf : f ∈ classFun ↥M)
    (hf0 : ∀ x : ↥M, (x : L) ∉ A → f x = 0) {x : ↥M} (hx : (x : L) ∈ A) :
    indClassFun M f (x : L) = f x := by
  rw [← tiDadeMap_eq_indClassFun hTI (isClassFun_of_mem_classFun hf) hf0]
  exact tiDadeMap_apply_mem hTI (isClassFun_of_mem_classFun hf) x hx

theorem IsPrimeCyclicTIHyp.natCard_sup_eq_mul (h : IsPrimeCyclicTIHyp K W₁ W₂) :
    Nat.card ↥(W₁ ⊔ W₂) = Nat.card ↥W₁ * Nat.card ↥W₂ := by
  rw [← Nat.card_congr (mulEquivProdOfCoeEqMul h.coe_sup_eq_mul h.inf_left_right_eq_bot
    (fun x hx y hy => h.commute_left_right x hx y hy)).toEquiv, Nat.card_prod]

theorem IsPrimeCyclicTIHyp.isCyclicTIPair (h : IsPrimeCyclicTIHyp K W₁ W₂) :
    IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ where
  left_ne_bot := h.left_ne_bot
  right_ne_bot := h.right_ne_bot
  mul_eq := h.coe_sup_eq_mul.symm
  inf_eq_bot := h.inf_left_right_eq_bot
  commute := fun x hx y hy => (h.commute_left_right x hx y hy).eq
  isCyclic := h.isCyclic_sup
  odd_natCard := by rw [h.natCard_sup_eq_mul]; exact h.odd_natCard
  setOf_conj_eq_self := by
    rw [cyclicTIDiff_sup_eq_cyclicTIset]; exact h.setOf_conj_image_cyclicTIset_eq_self
  inter_eq_empty := by
    intro g hg
    rw [cyclicTIDiff_sup_eq_cyclicTIset]
    exact h.conj_image_cyclicTIset_inter_eq_empty hg

namespace IsPrimeCyclicTIHyp

variable (h : IsPrimeCyclicTIHyp K W₁ W₂)

noncomputable def prodCharDiff (z : Irr ↥W₁ × Irr ↥W₂) : classFun ↥(W₁ ⊔ W₂) :=
  h.isCyclicTIPair.basisProdIrr z -
    h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, z.2)

theorem coe_prodCharDiff (z : Irr ↥W₁ × Irr ↥W₂) :
    (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) =
      h.isCyclicTIPair.prodChar (z.1 : ↥W₁ → ℂ) (z.2 : ↥W₂ → ℂ) -
        h.isCyclicTIPair.prodChar 1 (z.2 : ↥W₂ → ℂ) := by
  simp [prodCharDiff, IsCyclicTIPair.coe_basisProdIrr_apply]

theorem prodCharDiff_eq_zero {z : Irr ↥W₁ × Irr ↥W₂} (hz : z.1 = principalIrr ↥W₁) :
    h.prodCharDiff z = 0 := by
  rw [prodCharDiff, show z = (principalIrr ↥W₁, z.2) from Prod.ext hz rfl, sub_self]

theorem prodCharDiff_apply_eq_zero_of_notMem {z : Irr ↥W₁ × Irr ↥W₂} {x : ↥(W₁ ⊔ W₂)}
    (hx : (x : L) ∉ primeTIset W₁ W₂) : (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) x = 0 := by
  have hW := h.isCyclicTIPair
  have := hW.isMulCommutative_left
  have hx2 : (x : L) ∈ W₂ := mem_right_of_notMem_primeTIset x.2 hx
  have hxe : x = ⟨((⟨(x : L), hx2⟩ : ↥W₂) : L), hW.right_le hx2⟩ := Subtype.ext rfl
  rw [h.coe_prodCharDiff]
  simp only [Pi.sub_apply]
  rw [hxe, hW.prodChar_apply_coe_right, hW.prodChar_apply_coe_right,
    apply_one_eq_one_of_mem_Irr z.1.2]
  simp

theorem prodCharDiff_mem_virtualChars (z : Irr ↥W₁ × Irr ↥W₂) :
    (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) ∈ virtualChars ↥(W₁ ⊔ W₂) := by
  have hW := h.isCyclicTIPair
  rw [h.coe_prodCharDiff]
  exact sub_mem (Irr_subset_virtualChars (hW.prodChar_mem_Irr z.1.2 z.2.2))
    (Irr_subset_virtualChars (hW.prodChar_mem_Irr one_mem_Irr z.2.2))

theorem prodCharDiff_mem_dadeZDomain (z : Irr ↥W₁ × Irr ↥W₂) :
    (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) ∈ dadeZDomain (W₁ ⊔ W₂) (primeTIset W₁ W₂) :=
  mem_dadeZDomain.2 ⟨h.prodCharDiff_mem_virtualChars z,
    fun _ hx => h.prodCharDiff_apply_eq_zero_of_notMem hx⟩

theorem prodCharDiff_mem_dadeDomain (z : Irr ↥W₁ × Irr ↥W₂) :
    (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) ∈ dadeDomain (W₁ ⊔ W₂) (primeTIset W₁ W₂) :=
  mem_dadeDomain_of_mem_dadeZDomain (h.prodCharDiff_mem_dadeZDomain z)

theorem cfInner_self_prodCharDiff [Fintype ↥(W₁ ⊔ W₂)] {z : Irr ↥W₁ × Irr ↥W₂}
    (hz : z.1 ≠ principalIrr ↥W₁) :
    cfInner (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) = 2 := by
  classical
  have hW := h.isCyclicTIPair
  rw [h.coe_prodCharDiff, cfInner_sub_left, cfInner_sub_right, cfInner_sub_right]
  have e1 := hW.cfInner_prodChar z.1 z.1 z.2 z.2
  have e2 := hW.cfInner_prodChar z.1 (principalIrr ↥W₁) z.2 z.2
  have e3 := hW.cfInner_prodChar (principalIrr ↥W₁) z.1 z.2 z.2
  have e4 := hW.cfInner_prodChar (principalIrr ↥W₁) (principalIrr ↥W₁) z.2 z.2
  rw [coe_principalIrr] at e2 e3 e4
  rw [if_pos rfl] at e1
  rw [if_neg (by simp [Prod.ext_iff, hz])] at e2
  rw [if_neg (by simp [Prod.ext_iff, Ne.symm hz])] at e3
  rw [if_pos rfl] at e4
  rw [e1, e2, e3, e4]
  ring

theorem eq_sum_smul_prodCharDiff [Fintype (Irr ↥W₁)] [Fintype (Irr ↥W₂)]
    (f : classFun ↥(W₁ ⊔ W₂))
    (hf0 : ∀ x : ↥(W₁ ⊔ W₂), (x : L) ∉ primeTIset W₁ W₂ → (f : ↥(W₁ ⊔ W₂) → ℂ) x = 0) :
    f = ∑ z : Irr ↥W₁ × Irr ↥W₂,
      h.isCyclicTIPair.basisProdIrr.repr f z • h.prodCharDiff z := by
  classical
  have hW := h.isCyclicTIPair
  have hbase : ∀ x : ↥(W₁ ⊔ W₂), (f : ↥(W₁ ⊔ W₂) → ℂ) x
      = ∑ z : Irr ↥W₁ × Irr ↥W₂,
        hW.basisProdIrr.repr f z * hW.prodChar (z.1 : ↥W₁ → ℂ) (z.2 : ↥W₂ → ℂ) x := by
    intro x
    have h1 : ((∑ z : Irr ↥W₁ × Irr ↥W₂,
          hW.basisProdIrr.repr f z • hW.basisProdIrr z : classFun ↥(W₁ ⊔ W₂)) :
          ↥(W₁ ⊔ W₂) → ℂ) x
        = ∑ z : Irr ↥W₁ × Irr ↥W₂,
          hW.basisProdIrr.repr f z * hW.prodChar (z.1 : ↥W₁ → ℂ) (z.2 : ↥W₂ → ℂ) x := by
      rw [Submodule.coe_sum]
      simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
        IsCyclicTIPair.coe_basisProdIrr_apply]
    rw [← h1, hW.basisProdIrr.sum_repr f]
  refine Subtype.ext (funext fun x => ?_)
  set b : ↥W₂ := (hW.mulEquivProd.symm x).2 with hb
  set y : ↥(W₁ ⊔ W₂) := ⟨((b : L)), hW.right_le b.2⟩ with hy
  have hstep : ∀ mu : ↥W₂ → ℂ, hW.prodChar 1 mu x = hW.prodChar 1 mu y := by
    intro mu
    rw [hW.prodChar_apply, hy, hW.prodChar_apply_coe_right]
    simp [hb]
  have hyB : (y : L) ∉ primeTIset W₁ W₂ := by
    simp [hy, mem_primeTIset, b.2]
  have hzeroy : ∀ z : Irr ↥W₁ × Irr ↥W₂,
      hW.prodChar (z.1 : ↥W₁ → ℂ) (z.2 : ↥W₂ → ℂ) y = hW.prodChar 1 (z.2 : ↥W₂ → ℂ) y := by
    intro z
    have hz := h.prodCharDiff_apply_eq_zero_of_notMem (z := z) (x := y) hyB
    rw [h.coe_prodCharDiff] at hz
    simp only [Pi.sub_apply, sub_eq_zero] at hz
    exact hz
  have hu : ∑ z : Irr ↥W₁ × Irr ↥W₂,
      hW.basisProdIrr.repr f z * hW.prodChar 1 (z.2 : ↥W₂ → ℂ) x = 0 := by
    calc ∑ z : Irr ↥W₁ × Irr ↥W₂,
          hW.basisProdIrr.repr f z * hW.prodChar 1 (z.2 : ↥W₂ → ℂ) x
        = ∑ z : Irr ↥W₁ × Irr ↥W₂,
            hW.basisProdIrr.repr f z * hW.prodChar 1 (z.2 : ↥W₂ → ℂ) y :=
          Finset.sum_congr rfl fun z _ => by rw [hstep]
      _ = ∑ z : Irr ↥W₁ × Irr ↥W₂,
            hW.basisProdIrr.repr f z * hW.prodChar (z.1 : ↥W₁ → ℂ) (z.2 : ↥W₂ → ℂ) y :=
          Finset.sum_congr rfl fun z _ => by rw [hzeroy]
      _ = (f : ↥(W₁ ⊔ W₂) → ℂ) y := (hbase y).symm
      _ = 0 := hf0 y hyB
  have hsum : ((∑ z : Irr ↥W₁ × Irr ↥W₂,
        hW.basisProdIrr.repr f z • h.prodCharDiff z : classFun ↥(W₁ ⊔ W₂)) :
        ↥(W₁ ⊔ W₂) → ℂ) x
      = ∑ z : Irr ↥W₁ × Irr ↥W₂,
        hW.basisProdIrr.repr f z * (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) x := by
    rw [Submodule.coe_sum]
    simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
  rw [hsum, hbase x]
  have hterm : ∀ z : Irr ↥W₁ × Irr ↥W₂,
      hW.basisProdIrr.repr f z * (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) x
        = hW.basisProdIrr.repr f z * hW.prodChar (z.1 : ↥W₁ → ℂ) (z.2 : ↥W₂ → ℂ) x
          - hW.basisProdIrr.repr f z * hW.prodChar 1 (z.2 : ↥W₂ → ℂ) x := by
    intro z
    rw [h.coe_prodCharDiff]
    simp [mul_sub]
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_sub_distrib, hu, sub_zero]

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

theorem coe_apply_prodCharDiff (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (z : Irr ↥W₁ × Irr ↥W₂) :
    (σ (h.prodCharDiff z) : L → ℂ)
      = indClassFun (W₁ ⊔ W₂) (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) := by
  classical
  have hW := h.isCyclicTIPair
  have hfin1 : Finite ↥W₁ := hW.finite_left
  have hfin2 : Finite ↥W₂ := hW.finite_right
  by_cases hz : z.1 = principalIrr ↥W₁
  · rw [h.prodCharDiff_eq_zero hz]
    simp [indClassFun_zero]
  · set hTI := h.isTIWithNormalizer_primeTIset with hTIdef
    set F : L → ℂ := indClassFun (W₁ ⊔ W₂) (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) with hF
    have hFmem : F ∈ Submodule.span ℤ (Irr L) :=
      virtualChars_le_span_Irr
        (hTI.indClassFun_mem_virtualChars (h.prodCharDiff_mem_dadeZDomain z))
    have hFnorm : cfInner F F = 2 := by
      rw [hF, hTI.cfInner_self_indClassFun (h.prodCharDiff_mem_dadeDomain z)]
      exact h.cfInner_self_prodCharDiff hz
    have hV : ∀ v : ↥(W₁ ⊔ W₂), (v : L) ∈ cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ →
        F (v : L) = (1 : ℂ) * (hW.prodChar (z.1 : ↥W₁ → ℂ) (z.2 : ↥W₂ → ℂ) v
          - hW.prodChar ((principalIrr ↥W₁ : Irr ↥W₁) : ↥W₁ → ℂ) (z.2 : ↥W₂ → ℂ) v) := by
      intro v hv
      rw [cyclicTIDiff_sup_eq_cyclicTIset] at hv
      have hvB : (v : L) ∈ primeTIset W₁ W₂ := cyclicTIset_subset_primeTIset hv
      have hval : F (v : L) = (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) v := by
        rw [hF]
        exact hTI.indClassFun_apply_of_mem (h.prodCharDiff z).2
          (fun _ hx => h.prodCharDiff_apply_eq_zero_of_notMem hx) hvB
      rw [hval, h.coe_prodCharDiff, coe_principalIrr]
      simp
    have hkey := hW.eq_signed_sub_prodCharEta hσ
      (i := z.1) (j := z.2) (k := principalIrr ↥W₁) (l := z.2)
      (by simp [Prod.ext_iff, hz]) (Or.inl rfl) hFmem hFnorm hV
    rw [hkey, one_smul, prodCharDiff, map_sub]
    funext x
    simp [IsCyclicTIPair.prodCharEta_eq_coe_apply]

include h in
theorem coe_apply_eq_indClassFun (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (f : classFun ↥(W₁ ⊔ W₂))
    (hf0 : ∀ x : ↥(W₁ ⊔ W₂), (x : L) ∉ primeTIset W₁ W₂ → (f : ↥(W₁ ⊔ W₂) → ℂ) x = 0) :
    (σ f : L → ℂ) = indClassFun (W₁ ⊔ W₂) (f : ↥(W₁ ⊔ W₂) → ℂ) := by
  classical
  have hW := h.isCyclicTIPair
  have hfin1 : Finite ↥W₁ := hW.finite_left
  have hfin2 : Finite ↥W₂ := hW.finite_right
  have hFI : Fintype (Irr ↥W₁) := Fintype.ofFinite _
  have hFJ : Fintype (Irr ↥W₂) := Fintype.ofFinite _
  set c := hW.basisProdIrr.repr f with hc
  have hexp := h.eq_sum_smul_prodCharDiff f hf0
  have hcoe : (f : ↥(W₁ ⊔ W₂) → ℂ)
      = ∑ z : Irr ↥W₁ × Irr ↥W₂, c z • (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ) := by
    rw [hexp, Submodule.coe_sum]
    rfl
  calc (σ f : L → ℂ)
      = ∑ z : Irr ↥W₁ × Irr ↥W₂, c z • (σ (h.prodCharDiff z) : L → ℂ) := by
        rw [hexp, map_sum, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [map_smul]
        rfl
    _ = ∑ z : Irr ↥W₁ × Irr ↥W₂,
          indClassFun (W₁ ⊔ W₂) (c z • (h.prodCharDiff z : ↥(W₁ ⊔ W₂) → ℂ)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [indClassFun_smul, h.coe_apply_prodCharDiff hσ z]
    _ = indClassFun (W₁ ⊔ W₂) (f : ↥(W₁ ⊔ W₂) → ℂ) := by
        rw [hcoe, NormalInducedSupportBasis.indClassFun_sum]

include h in
theorem apply_eq_of_mem_primeTIset (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (f : classFun ↥(W₁ ⊔ W₂)) {v : ↥(W₁ ⊔ W₂)} (hv : (v : L) ∈ primeTIset W₁ W₂) :
    (σ f : L → ℂ) (v : L) = (f : ↥(W₁ ⊔ W₂) → ℂ) v := by
  classical
  have hW := h.isCyclicTIPair
  have hcomm := hW.isMulCommutative_coe
  set p : ↥(W₁ ⊔ W₂) → ℂ := Pi.single v 1 with hp
  set pcf : classFun ↥(W₁ ⊔ W₂) := ⟨p, single_mem_classFun v 1⟩ with hpcf
  have hσp : (σ pcf : L → ℂ) = indClassFun (W₁ ⊔ W₂) p := by
    refine h.coe_apply_eq_indClassFun hσ pcf fun x hx => ?_
    change p x = 0
    rw [hp, Pi.single_eq_of_ne']
    intro hxv
    exact hx (hxv ▸ hv)
  have h1 : cfInner (σ f : L → ℂ) (indClassFun (W₁ ⊔ W₂) p)
      = cfInner (f : ↥(W₁ ⊔ W₂) → ℂ) p := by
    rw [← hσp]
    exact hσ.inner_eq f pcf
  have h2 : cfInner (indClassFun (W₁ ⊔ W₂) p) (σ f : L → ℂ)
      = cfInner p (resClassFun (W₁ ⊔ W₂) (σ f : L → ℂ)) :=
    cfInner_indClassFun (W₁ ⊔ W₂) p (σ f).2
  have h3 : cfInner (resClassFun (W₁ ⊔ W₂) (σ f : L → ℂ)) p
      = cfInner (f : ↥(W₁ ⊔ W₂) → ℂ) p := by
    rw [← h1, ← conj_cfInner, ← h2]
    exact conj_cfInner _ _
  rw [hp, cfInner_single, cfInner_single, resClassFun_apply] at h3
  have hne : (Nat.card ↥(W₁ ⊔ W₂) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact mul_left_cancel₀ (inv_ne_zero hne) h3

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
