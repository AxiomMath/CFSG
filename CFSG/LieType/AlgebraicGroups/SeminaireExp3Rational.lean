module

public import CFSG.LieType.AlgebraicGroups.SeminaireExp3Image
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Nullstellensatz

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups.SeminaireExp3

open MvPolynomial TensorProduct Pointwise

section Coefficients

variable {k : Type} [Field k] (k₀ : Subfield k) {σ τ : Type}

@[expose] def CoeffsIn (P : MvPolynomial σ k) : Prop :=
  ∀ m, P.coeff m ∈ k₀

theorem coeffsIn_iff_mem_range {P : MvPolynomial σ k} :
    CoeffsIn k₀ P ↔ P ∈ (MvPolynomial.map k₀.subtype).range := by
  rw [RingHom.mem_range, ← Set.mem_range, mem_range_map_iff_coeffs_subset]
  constructor
  · intro h c hc
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
    exact ⟨⟨_, h m⟩, rfl⟩
  · intro h m
    by_cases hm : P.coeff m = 0
    · rw [hm]
      exact k₀.zero_mem
    · obtain ⟨c, hc⟩ := h (coeff_mem_coeffs m hm)
      rw [← hc]
      exact c.2

variable {k₀}

@[expose] def coeffMap (l : k →ₗ[k₀] k₀) : MvPolynomial σ k →+ MvPolynomial σ k where
  toFun P := AddMonoidAlgebra.map (k₀.subtype.toAddMonoidHom.comp l.toAddMonoidHom) P
  map_zero' := by
    ext m
    simp
  map_add' P Q := by
    ext m
    simp

@[simp] theorem coeff_coeffMap (l : k →ₗ[k₀] k₀) (P : MvPolynomial σ k) (m : σ →₀ ℕ) :
    (coeffMap l P).coeff m = l (P.coeff m) :=
  rfl

theorem coeffsIn_coeffMap (l : k →ₗ[k₀] k₀) (P : MvPolynomial σ k) :
    CoeffsIn k₀ (coeffMap l P) :=
  fun m => (l (P.coeff m)).2

theorem coeffMap_C_mul (l : k →ₗ[k₀] k₀) (c : k) {R : MvPolynomial σ k} (hR : CoeffsIn k₀ R) :
    coeffMap l (C c * R) = C (l c : k) * R := by
  ext m
  rw [coeff_coeffMap, coeff_C_mul, coeff_C_mul]
  have h : c * R.coeff m = (⟨R.coeff m, hR m⟩ : k₀) • c := by
    rw [mul_comm]
    rfl
  rw [h, map_smul, smul_eq_mul, Subfield.coe_mul, mul_comm]

theorem coeffMap_mul (l : k →ₗ[k₀] k₀) (P : MvPolynomial σ k) {R : MvPolynomial σ k}
    (hR : CoeffsIn k₀ R) : coeffMap l (P * R) = coeffMap l P * R := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hm : CoeffsIn k₀ (monomial u (1 : k)) := by
      rw [coeffsIn_iff_mem_range]
      exact ⟨monomial u 1, by simp⟩
    have h1 : CoeffsIn k₀ (monomial u (1 : k) * R) := by
      rw [coeffsIn_iff_mem_range] at hR hm ⊢
      exact Subring.mul_mem _ hm hR
    have ha : monomial u a = C a * monomial u (1 : k) := by rw [C_mul_monomial, mul_one]
    rw [ha, mul_assoc, coeffMap_C_mul l a h1, coeffMap_C_mul l a hm, mul_assoc]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_mul]

theorem coeffMap_bind₁ (l : k →ₗ[k₀] k₀) {Ψ : τ → MvPolynomial σ k}
    (hΨ : ∀ i, CoeffsIn k₀ (Ψ i)) (Q : MvPolynomial τ k) :
    coeffMap l (bind₁ Ψ Q) = bind₁ Ψ (coeffMap l Q) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    have hprod : CoeffsIn k₀ (∏ i ∈ u.support, Ψ i ^ u i) := by
      rw [coeffsIn_iff_mem_range]
      exact Subring.prod_mem _ fun i _ =>
        Subring.pow_mem _ ((coeffsIn_iff_mem_range k₀).1 (hΨ i)) _
    have hmono : coeffMap l (monomial u a) = monomial u (l a : k) := by
      ext m
      rw [coeff_coeffMap, coeff_monomial, coeff_monomial]
      split_ifs <;> simp
    rw [bind₁_monomial, coeffMap_C_mul l a hprod, hmono, bind₁_monomial]
  | add p q hp hq => simp only [map_add, hp, hq]

variable (k₀) in
@[expose] def IsGeneratedOver (I : Ideal (MvPolynomial σ k)) : Prop :=
  ∃ S : Set (MvPolynomial σ k), (∀ P ∈ S, ∀ m, P.coeff m ∈ k₀) ∧ Ideal.span S = I

theorem IsGeneratedOver.coeffMap_mem {I : Ideal (MvPolynomial σ k)} (hI : IsGeneratedOver k₀ I)
    (l : k →ₗ[k₀] k₀) {Q : MvPolynomial σ k} (hQ : Q ∈ I) : coeffMap l Q ∈ I := by
  obtain ⟨S, hS, rfl⟩ := hI
  have key : ∀ a : MvPolynomial σ k, coeffMap l (a * Q) ∈ Ideal.span S := by
    induction hQ using Submodule.span_induction with
    | mem x hx =>
      intro a
      rw [coeffMap_mul l a (hS x hx)]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span hx)
    | zero =>
      intro a
      rw [mul_zero, map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro a
      rw [mul_add, map_add]
      exact add_mem (hx a) (hy a)
    | smul b x _ hx =>
      intro a
      rw [smul_eq_mul, ← mul_assoc]
      exact hx (a * b)
  simpa using key 1

theorem isGeneratedOver_of_coeffMap_mem {I : Ideal (MvPolynomial σ k)}
    (h : ∀ (l : k →ₗ[k₀] k₀), ∀ Q ∈ I, coeffMap l Q ∈ I) : IsGeneratedOver k₀ I := by
  classical
  refine ⟨{P | P ∈ I ∧ CoeffsIn k₀ P}, fun P hP => hP.2,
    le_antisymm (Ideal.span_le.2 fun P hP => hP.1) fun Q hQ => ?_⟩
  let b := Module.Basis.ofVectorSpace k₀ k
  let F := Q.support.biUnion fun m => (b.repr (Q.coeff m)).support
  have hsum : Q = ∑ i ∈ F, C (b i) * coeffMap (b.coord i) Q := by
    ext m
    rw [coeff_sum]
    simp only [coeff_C_mul, coeff_coeffMap, Module.Basis.coord_apply]
    have hsupp : (b.repr (Q.coeff m)).support ⊆ F := by
      by_cases hm : m ∈ Q.support
      · exact Finset.subset_biUnion_of_mem (fun m => (b.repr (Q.coeff m)).support) hm
      · rw [notMem_support_iff.1 hm, map_zero, Finsupp.support_zero]
        exact Finset.empty_subset _
    conv_lhs => rw [← b.linearCombination_repr (Q.coeff m), Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset (b.repr (Q.coeff m)) hsupp (fun i a => a • b i)
        fun i _ => zero_smul _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    rfl
  rw [hsum]
  exact sum_mem fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨h _ Q hQ, coeffsIn_coeffMap _ _⟩)

theorem IsGeneratedOver.comap_bind₁ {J : Ideal (MvPolynomial σ k)} (hJ : IsGeneratedOver k₀ J)
    {Ψ : τ → MvPolynomial σ k} (hΨ : ∀ i, CoeffsIn k₀ (Ψ i)) :
    IsGeneratedOver k₀ (Ideal.comap (bind₁ Ψ) J) :=
  isGeneratedOver_of_coeffMap_mem fun l Q hQ => by
    rw [Ideal.mem_comap] at hQ ⊢
    rw [← coeffMap_bind₁ l hΨ]
    exact hJ.coeffMap_mem l hQ

theorem IsGeneratedOver.sup {I J : Ideal (MvPolynomial σ k)} (hI : IsGeneratedOver k₀ I)
    (hJ : IsGeneratedOver k₀ J) : IsGeneratedOver k₀ (I ⊔ J) := by
  obtain ⟨S, hS, rfl⟩ := hI
  obtain ⟨T, hT, rfl⟩ := hJ
  exact ⟨S ∪ T, fun P hP => hP.elim (hS P) (hT P), Ideal.span_union S T⟩

theorem IsGeneratedOver.map_rename (f : σ → τ) {I : Ideal (MvPolynomial σ k)}
    (hI : IsGeneratedOver k₀ I) : IsGeneratedOver k₀ (Ideal.map (rename f) I) := by
  obtain ⟨S, hS, rfl⟩ := hI
  refine ⟨rename f '' S, ?_, (Ideal.map_span (rename f) S).symm⟩
  rintro _ ⟨P, hP, rfl⟩
  have hP' : P ∈ (MvPolynomial.map k₀.subtype).range := (coeffsIn_iff_mem_range k₀).1 (hS P hP)
  obtain ⟨P₀, hP₀⟩ := hP'
  intro m
  rw [← hP₀, ← MvPolynomial.map_rename, coeff_map]
  exact SetLike.coe_mem _

theorem isGeneratedOver_bot : IsGeneratedOver k₀ (⊥ : Ideal (MvPolynomial σ k)) :=
  ⟨∅, by simp, Ideal.span_empty⟩

end Coefficients

section Product

variable {k : Type} [Field k] {σ₁ σ₂ : Type}

theorem isRadical_vanishingIdeal {σ : Type} (S : Set (σ → k)) :
    (vanishingIdeal k S).IsRadical := by
  rintro P ⟨n, hn⟩ x hx
  have h := hn x hx
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

theorem aeval_aeval_sumElim_X_C (x : σ₁ → k) (w : σ₂ → k) (Q : MvPolynomial (σ₁ ⊕ σ₂) k) :
    aeval x (aeval (Sum.elim X fun t => C (w t)) Q) = aeval (Sum.elim x w) Q := by
  have : (aeval x).comp (aeval (Sum.elim (X : σ₁ → MvPolynomial σ₁ k) fun t => C (w t))) =
      aeval (Sum.elim x w) :=
    MvPolynomial.algHom_ext fun v => by rcases v with s | t <;> simp
  exact congrArg (fun f : MvPolynomial (σ₁ ⊕ σ₂) k →ₐ[k] k => f Q) this

theorem aeval_aeval_sumElim_C_X (w : σ₁ → k) (y : σ₂ → k) (Q : MvPolynomial (σ₁ ⊕ σ₂) k) :
    aeval y (aeval (Sum.elim (fun s => C (w s)) X) Q) = aeval (Sum.elim w y) Q := by
  have : (aeval y).comp (aeval (Sum.elim (fun s => C (w s)) (X : σ₂ → MvPolynomial σ₂ k))) =
      aeval (Sum.elim w y) :=
    MvPolynomial.algHom_ext fun v => by rcases v with s | t <;> simp
  exact congrArg (fun f : MvPolynomial (σ₁ ⊕ σ₂) k →ₐ[k] k => f Q) this

variable [IsAlgClosed k] [Finite σ₁] [Finite σ₂]

theorem vanishingIdeal_image2_sumElim (S₁ : Set (σ₁ → k)) (S₂ : Set (σ₂ → k)) :
    vanishingIdeal k (Set.image2 (fun x y => Sum.elim x y) S₁ S₂) =
      Ideal.map (rename Sum.inl) (vanishingIdeal k S₁) ⊔
        Ideal.map (rename Sum.inr) (vanishingIdeal k S₂) := by
  set I₁ := vanishingIdeal k S₁
  set I₂ := vanishingIdeal k S₂
  refine le_antisymm (fun Q hQ => ?_) (sup_le ?_ ?_)
  · have : IsReduced (MvPolynomial σ₁ k ⧸ I₁) :=
      (Ideal.isRadical_iff_quotient_reduced I₁).1 (isRadical_vanishingIdeal S₁)
    have : IsReduced (MvPolynomial σ₂ k ⧸ I₂) :=
      (Ideal.isRadical_iff_quotient_reduced I₂).1 (isRadical_vanishingIdeal S₂)
    let e := MvPolynomial.tensorEquivSum k σ₁ σ₂ k
    let Φ := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I₁) (Ideal.Quotient.mkₐ k I₂)
    have hA : ∀ w₂ ∈ S₂, ∀ w₁ : σ₁ → k, (∀ p ∈ I₁, aeval w₁ p = 0) →
        aeval (Sum.elim w₁ w₂) Q = 0 := by
      intro w₂ hw₂ w₁ hw₁
      have hmem : aeval (Sum.elim X fun t => C (w₂ t)) Q ∈ I₁ := by
        rw [mem_vanishingIdeal_iff]
        intro x hx
        rw [aeval_aeval_sumElim_X_C]
        exact hQ _ ⟨x, hx, w₂, hw₂, rfl⟩
      have h := hw₁ _ hmem
      rwa [aeval_aeval_sumElim_X_C] at h
    have hB : ∀ w₁ : σ₁ → k, (∀ p ∈ I₁, aeval w₁ p = 0) → ∀ w₂ : σ₂ → k,
        (∀ p ∈ I₂, aeval w₂ p = 0) → aeval (Sum.elim w₁ w₂) Q = 0 := by
      intro w₁ hw₁ w₂ hw₂
      have hmem : aeval (Sum.elim (fun s => C (w₁ s)) X) Q ∈ I₂ := by
        rw [mem_vanishingIdeal_iff]
        intro y hy
        rw [aeval_aeval_sumElim_C_X]
        exact hA y hy w₁ hw₁
      have h := hw₂ _ hmem
      rwa [aeval_aeval_sumElim_C_X] at h
    have hΦ : Φ (e.symm Q) = 0 := by
      refine tensor_eq_zero_of_forall_algHom k _ _ _ fun x y => ?_
      set w₁ : σ₁ → k := fun s => x (Ideal.Quotient.mk I₁ (X s))
      set w₂ : σ₂ → k := fun s => y (Ideal.Quotient.mk I₂ (X s))
      have hx : x.comp (Ideal.Quotient.mkₐ k I₁) = aeval w₁ :=
        MvPolynomial.algHom_ext fun s => by simp [w₁]
      have hy : y.comp (Ideal.Quotient.mkₐ k I₂) = aeval w₂ :=
        MvPolynomial.algHom_ext fun s => by simp [w₂]
      have hcomp : ((Algebra.TensorProduct.productMap x y).comp Φ).comp
          (e.symm : MvPolynomial (σ₁ ⊕ σ₂) k →ₐ[k] _) = aeval (Sum.elim w₁ w₂) := by
        refine MvPolynomial.algHom_ext fun v => ?_
        rcases v with s | s
        · have : e.symm (X (Sum.inl s)) = X s ⊗ₜ 1 := by
            rw [AlgEquiv.symm_apply_eq]
            exact (MvPolynomial.tensorEquivSum_X_tmul_one s).symm
          simp [this, Φ, w₁]
        · have : e.symm (X (Sum.inr s)) = 1 ⊗ₜ X s := by
            rw [AlgEquiv.symm_apply_eq]
            exact (MvPolynomial.tensorEquivSum_one_tmul_X s).symm
          simp [this, Φ, w₂]
      have h := congrArg (fun f : MvPolynomial (σ₁ ⊕ σ₂) k →ₐ[k] k => f Q) hcomp
      simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at h
      rw [h]
      refine hB w₁ (fun p hp => ?_) w₂ fun p hp => ?_
      · rw [← hx, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
      · rw [← hy, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    have hker : ∀ {σ : Type} (I : Ideal (MvPolynomial σ k)),
        RingHom.ker (Ideal.Quotient.mkₐ k I) = I := fun I => by
      ext p
      rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    have hmem : e.symm Q ∈ RingHom.ker Φ := hΦ
    rw [Algebra.TensorProduct.map_ker _ _ (Ideal.Quotient.mkₐ_surjective k I₁)
      (Ideal.Quotient.mkₐ_surjective k I₂), hker, hker] at hmem
    have hL : ∀ p : MvPolynomial σ₁ k, e ((Algebra.TensorProduct.includeLeft :
        MvPolynomial σ₁ k →ₐ[k] MvPolynomial σ₁ k ⊗[k] MvPolynomial σ₂ k) p) =
          rename Sum.inl p := by
      have : e.toAlgHom.comp (Algebra.TensorProduct.includeLeft :
          MvPolynomial σ₁ k →ₐ[k] MvPolynomial σ₁ k ⊗[k] MvPolynomial σ₂ k) = rename Sum.inl :=
        MvPolynomial.algHom_ext fun s => by simp [e]
      exact fun p => congrArg (fun f : MvPolynomial σ₁ k →ₐ[k] _ => f p) this
    have hR : ∀ p : MvPolynomial σ₂ k, e ((Algebra.TensorProduct.includeRight :
        MvPolynomial σ₂ k →ₐ[k] MvPolynomial σ₁ k ⊗[k] MvPolynomial σ₂ k) p) =
          rename Sum.inr p := by
      have : e.toAlgHom.comp (Algebra.TensorProduct.includeRight :
          MvPolynomial σ₂ k →ₐ[k] MvPolynomial σ₁ k ⊗[k] MvPolynomial σ₂ k) = rename Sum.inr :=
        MvPolynomial.algHom_ext fun s => by simp [e]
      exact fun p => congrArg (fun f : MvPolynomial σ₂ k →ₐ[k] _ => f p) this
    have hle : Ideal.map (Algebra.TensorProduct.includeLeft : MvPolynomial σ₁ k →ₐ[k] _) I₁ ⊔
        Ideal.map (Algebra.TensorProduct.includeRight : MvPolynomial σ₂ k →ₐ[k] _) I₂ ≤
        Ideal.comap e (Ideal.map (rename Sum.inl) I₁ ⊔ Ideal.map (rename Sum.inr) I₂) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro p hp
        rw [Ideal.mem_comap, Ideal.mem_comap, hL]
        exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)
      · rw [Ideal.map_le_iff_le_comap]
        intro p hp
        rw [Ideal.mem_comap, Ideal.mem_comap, hR]
        exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hp)
    have := hle hmem
    rwa [Ideal.mem_comap, AlgEquiv.apply_symm_apply] at this
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    rw [Ideal.mem_comap, mem_vanishingIdeal_iff]
    rintro _ ⟨x, hx, y, -, rfl⟩
    rw [aeval_rename]
    exact hP x hx
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    rw [Ideal.mem_comap, mem_vanishingIdeal_iff]
    rintro _ ⟨x, -, y, hy, rfl⟩
    rw [aeval_rename]
    exact hP y hy

end Product

namespace ZariskiGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : Type} [Field k] (k₀ : Subfield k)

theorem eval_eq_aeval (g : ZariskiGL ι k) (P : MvPolynomial (ι × ι ⊕ Unit) k) :
    eval g P = aeval (glVec g) P :=
  rfl

@[expose] def IsDefinedOver (S : Set (ZariskiGL ι k)) : Prop :=
  IsGeneratedOver k₀ (vanishingIdeal S)

variable {κ : Type} [Fintype κ] [DecidableEq κ]

@[expose] def IsMorphismOver {G : Subgroup (ZariskiGL ι k)} {H : Subgroup (ZariskiGL κ k)}
    (φ : G →* H) : Prop :=
  ∀ a b : κ, ∃ P : MvPolynomial (ι × ι ⊕ Unit) k, (∀ m, P.coeff m ∈ k₀) ∧ ∀ g : G,
    (toGL (φ g : ZariskiGL κ k) : Matrix κ κ k) a b = eval (g : ZariskiGL ι k) P

variable {k₀}

theorem IsMorphismOver.isMorphism {G : Subgroup (ZariskiGL ι k)} {H : Subgroup (ZariskiGL κ k)}
    {φ : G →* H} (hφ : IsMorphismOver k₀ φ) : IsMorphism φ := fun a b => by
  obtain ⟨P, -, hP⟩ := hφ a b
  exact ⟨P, hP⟩

variable (ι k) in
@[expose] def genMatrix : Matrix ι ι (MvPolynomial (ι × ι ⊕ Unit) k) :=
  Matrix.of fun i j => X (Sum.inl (i, j))

omit [Fintype ι] [DecidableEq ι] in
theorem map_genMatrix :
    (genMatrix ι k₀).map (MvPolynomial.map k₀.subtype) = genMatrix ι k := by
  ext i j
  simp [genMatrix]

theorem map_eval_genMatrix (g : ZariskiGL ι k) :
    (genMatrix ι k).map (eval g) = (toGL g : Matrix ι ι k) := by
  ext i j
  simp [genMatrix]

variable (ι k) in
@[expose] def invSubst : ι × ι ⊕ Unit → MvPolynomial (ι × ι ⊕ Unit) k :=
  Sum.elim (fun p => X (Sum.inr ()) * (genMatrix ι k).adjugate p.1 p.2) fun _ =>
    (genMatrix ι k).det

theorem coeffsIn_invSubst (v : ι × ι ⊕ Unit) : CoeffsIn k₀ (invSubst ι k v) := by
  rw [coeffsIn_iff_mem_range]
  rcases v with ⟨i, j⟩ | ⟨⟩
  · refine ⟨X (Sum.inr ()) * (genMatrix ι k₀).adjugate i j, ?_⟩
    have h := congrArg (fun M => M i j)
      (RingHom.map_adjugate (MvPolynomial.map k₀.subtype) (genMatrix ι k₀))
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h
    rw [map_mul, map_X, h, map_genMatrix]
    rfl
  · refine ⟨(genMatrix ι k₀).det, ?_⟩
    rw [RingHom.map_det, RingHom.mapMatrix_apply, map_genMatrix]
    rfl

theorem eval_bind₁_invSubst (g : ZariskiGL ι k) (P : MvPolynomial (ι × ι ⊕ Unit) k) :
    eval g (bind₁ (invSubst ι k) P) = eval g⁻¹ P := by
  have hadj : ∀ i j, eval g ((genMatrix ι k).adjugate i j) =
      (toGL g : Matrix ι ι k).adjugate i j := by
    intro i j
    have h := congrArg (fun M => M i j) (AlgHom.map_adjugate (eval g) (genMatrix ι k))
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply] at h
    rw [h, map_eval_genMatrix]
  have hdet : eval g (genMatrix ι k).det = (toGL g : Matrix ι ι k).det := by
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply, map_eval_genMatrix]
  have hinv : ((toGL g⁻¹ : Matrix.GeneralLinearGroup ι k) : Matrix ι ι k) =
      (toGL g : Matrix ι ι k)⁻¹ := by
    rw [map_inv, Matrix.coe_units_inv]
  have h : (eval g).comp (bind₁ (invSubst ι k)) = eval g⁻¹ := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rcases v with ⟨i, j⟩ | ⟨⟩
    · rw [AlgHom.comp_apply, bind₁_X_right, eval_X_inl, hinv, Matrix.inv_def,
        Ring.inverse_eq_inv']
      simp only [invSubst, Sum.elim_inl, map_mul, eval_X_inr, hadj, Matrix.smul_apply,
        smul_eq_mul]
    · rw [AlgHom.comp_apply, bind₁_X_right, eval_X_inr, hinv, Matrix.det_nonsing_inv,
        Ring.inverse_eq_inv', inv_inv]
      simp only [invSubst, Sum.elim_inr, hdet]
  exact congrArg (fun f : MvPolynomial (ι × ι ⊕ Unit) k →ₐ[k] k => f P) h

theorem isDefinedOver_mapSubgroup {G : Subgroup (ZariskiGL ι k)} {H : Subgroup (ZariskiGL κ k)}
    {φ : G →* H} (hG : IsDefinedOver k₀ (G : Set (ZariskiGL ι k))) (hφ : IsMorphismOver k₀ φ) :
    IsDefinedOver k₀ (mapSubgroup φ G : Set (ZariskiGL κ k)) := by
  choose P hP0 hP using hφ
  set D : MvPolynomial (ι × ι ⊕ Unit) k :=
    (Matrix.of fun a b => bind₁ (invSubst ι k) (P a b)).det with hD
  set Ψ : κ × κ ⊕ Unit → MvPolynomial (ι × ι ⊕ Unit) k :=
    Sum.elim (fun p => P p.1 p.2) fun _ => D with hΨdef
  have hbind : ∀ a b, bind₁ (invSubst ι k) (P a b) ∈ (MvPolynomial.map k₀.subtype).range := by
    intro a b
    obtain ⟨Q₀, hQ₀⟩ := RingHom.mem_range.1 ((coeffsIn_iff_mem_range k₀).1 (hP0 a b))
    choose S₀ hS₀ using fun v : ι × ι ⊕ Unit =>
      RingHom.mem_range.1 ((coeffsIn_iff_mem_range k₀).1 (coeffsIn_invSubst (k₀ := k₀) v))
    refine ⟨bind₁ S₀ Q₀, ?_⟩
    have hS : (fun i => MvPolynomial.map k₀.subtype (S₀ i)) = invSubst ι k := funext hS₀
    rw [map_bind₁, hQ₀, hS]
  have hΨ : ∀ v, CoeffsIn k₀ (Ψ v) := by
    rintro (⟨a, b⟩ | ⟨⟩)
    · exact hP0 a b
    · rw [coeffsIn_iff_mem_range]
      choose M₀ hM₀ using fun a b => RingHom.mem_range.1 (hbind a b)
      refine ⟨(Matrix.of M₀).det, ?_⟩
      rw [RingHom.map_det]
      show _ = D
      rw [hD]
      congr 1
      ext a b
      simp [hM₀]
  have hΨg : ∀ g : G, (fun v => aeval (glVec (g : ZariskiGL ι k)) (Ψ v)) =
      glVec (φ g : ZariskiGL κ k) := by
    intro g
    funext v
    rcases v with ⟨a, b⟩ | ⟨⟩
    · exact (hP a b g).symm
    · show eval (g : ZariskiGL ι k) D = ((toGL (φ g : ZariskiGL κ k) : Matrix κ κ k).det)⁻¹
      rw [hD, AlgHom.map_det, AlgHom.mapMatrix_apply]
      have hmat : (Matrix.of fun a b => bind₁ (invSubst ι k) (P a b)).map
          (eval (g : ZariskiGL ι k)) = (toGL (φ g⁻¹ : ZariskiGL κ k) : Matrix κ κ k) := by
        ext a b
        rw [Matrix.map_apply, Matrix.of_apply, eval_bind₁_invSubst, hP a b g⁻¹]
        rfl
      rw [hmat, map_inv φ, Subgroup.coe_inv, map_inv, Matrix.coe_units_inv,
        Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have heq : vanishingIdeal (mapSubgroup φ G : Set (ZariskiGL κ k)) =
      Ideal.comap (bind₁ Ψ) (vanishingIdeal (G : Set (ZariskiGL ι k))) := by
    ext Q
    rw [Ideal.mem_comap, mem_vanishingIdeal, mem_vanishingIdeal]
    constructor
    · intro hQ g hg
      rw [eval_eq_aeval, aeval_bind₁, hΨg ⟨g, hg⟩]
      exact hQ _ (mem_mapSubgroup.2 ⟨⟨g, hg⟩, hg, rfl⟩)
    · intro hQ y hy
      obtain ⟨g, hg, rfl⟩ := mem_mapSubgroup.1 hy
      have h := hQ g hg
      rwa [eval_eq_aeval, aeval_bind₁, hΨg g] at h
  rw [IsDefinedOver, heq]
  exact hG.comap_bind₁ hΨ

variable (ι k) in
@[expose] def mulSubst : ι × ι ⊕ Unit → MvPolynomial ((ι × ι ⊕ Unit) ⊕ (ι × ι ⊕ Unit)) k :=
  Sum.elim (fun p => ∑ l, X (Sum.inl (Sum.inl (p.1, l))) * X (Sum.inr (Sum.inl (l, p.2))))
    fun _ => X (Sum.inl (Sum.inr ())) * X (Sum.inr (Sum.inr ()))

omit [DecidableEq ι] in
theorem coeffsIn_mulSubst (v : ι × ι ⊕ Unit) : CoeffsIn k₀ (mulSubst ι k v) := by
  rw [coeffsIn_iff_mem_range]
  rcases v with ⟨i, j⟩ | ⟨⟩
  · exact ⟨∑ l, X (Sum.inl (Sum.inl (i, l))) * X (Sum.inr (Sum.inl (l, j))), by simp [mulSubst]⟩
  · exact ⟨X (Sum.inl (Sum.inr ())) * X (Sum.inr (Sum.inr ())), by simp [mulSubst]⟩

theorem aeval_mulSubst (g h : ZariskiGL ι k) :
    (fun v => aeval (Sum.elim (glVec g) (glVec h)) (mulSubst ι k v)) = glVec (g * h) := by
  funext v
  rcases v with ⟨i, j⟩ | ⟨⟩
  · simp [mulSubst, glVec, map_mul, Matrix.mul_apply]
  · simp [mulSubst, glVec, map_mul, Matrix.det_mul, mul_comm]

variable [IsAlgClosed k]

theorem isDefinedOver_mul {S T : Set (ZariskiGL ι k)} (hS : IsDefinedOver k₀ S)
    (hT : IsDefinedOver k₀ T) : IsDefinedOver k₀ (S * T) := by
  have heq : vanishingIdeal (S * T) = Ideal.comap (bind₁ (mulSubst ι k))
      (MvPolynomial.vanishingIdeal k
        (Set.image2 (fun x y => Sum.elim x y) (glVec '' S) (glVec '' T))) := by
    ext Q
    rw [Ideal.mem_comap, mem_vanishingIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    constructor
    · rintro hQ _ ⟨_, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
      rw [aeval_bind₁, aeval_mulSubst]
      exact hQ _ (Set.mul_mem_mul hs ht)
    · rintro hQ _ ⟨s, hs, t, ht, rfl⟩
      have h := hQ _ ⟨_, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
      rwa [aeval_bind₁, aeval_mulSubst] at h
  rw [IsDefinedOver, heq, vanishingIdeal_image2_sumElim]
  exact IsGeneratedOver.comap_bind₁ (IsGeneratedOver.sup (hS.map_rename _) (hT.map_rename _))
    (coeffsIn_mulSubst (k₀ := k₀))

omit [IsAlgClosed k] in
theorem isDefinedOver_one : IsDefinedOver k₀ ({1} : Set (ZariskiGL ι k)) := by
  have heq : vanishingIdeal ({1} : Set (ZariskiGL ι k)) =
      Ideal.comap (bind₁ fun v => (C (glVec (1 : ZariskiGL ι k) v) :
        MvPolynomial (ι × ι ⊕ Unit) k)) (⊥ : Ideal (MvPolynomial (ι × ι ⊕ Unit) k)) := by
    ext Q
    rw [Ideal.mem_comap, mem_vanishingIdeal, Set.forall_mem_singleton, Ideal.mem_bot]
    have hbind : (bind₁ (fun v => C (glVec (1 : ZariskiGL ι k) v)) Q :
        MvPolynomial (ι × ι ⊕ Unit) k) = C (aeval (glVec (1 : ZariskiGL ι k)) Q) := by
      have : (bind₁ fun v => C (glVec (1 : ZariskiGL ι k) v) :
          MvPolynomial (ι × ι ⊕ Unit) k →ₐ[k] MvPolynomial (ι × ι ⊕ Unit) k) =
          (Algebra.ofId k _).comp (aeval (glVec (1 : ZariskiGL ι k))) :=
        MvPolynomial.algHom_ext fun v => by simp
      exact congrArg (fun f : MvPolynomial (ι × ι ⊕ Unit) k →ₐ[k] _ => f Q) this
    rw [hbind, C_eq_zero, eval_eq_aeval]
  rw [IsDefinedOver, heq]
  refine isGeneratedOver_bot.comap_bind₁ fun v m => ?_
  rw [coeff_C]
  split_ifs
  · rcases v with ⟨i, j⟩ | ⟨⟩
    · simp only [glVec, Sum.elim_inl, map_one, Units.val_one, Matrix.one_apply]
      split_ifs
      · exact k₀.one_mem
      · exact k₀.zero_mem
    · simp only [glVec, Sum.elim_inr, map_one, Units.val_one, Matrix.det_one, inv_one]
      exact k₀.one_mem
  · exact k₀.zero_mem

end ZariskiGL

end CFSG.LieType.AlgebraicGroups.SeminaireExp3
