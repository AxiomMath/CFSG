module

public import CFSG.LieType.Universal.SpinCenter
public import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Basic

public section

namespace CFSG.LieType.Universal.Spin

open Module CliffordAlgebra
open scoped TensorProduct

universe u v w

section Prod

variable {K : Type u} [Field K] [CharP K 2]
  {V₁ : Type v} [AddCommGroup V₁] [Module K V₁] {V₂ : Type w} [AddCommGroup V₂] [Module K V₂]
  (Q₁ : QuadraticForm K V₁) (Q₂ : QuadraticForm K V₂)

private theorem add_self_eq_zero' {A : Type*} [Ring A] [Algebra K A] (x : A) : x + x = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  calc x + x = (2 : K) • x := by rw [two_smul]
    _ = 0 := by rw [h2, zero_smul]

theorem commute_ι_inl_ι_inr (v₁ : V₁) (v₂ : V₂) :
    Commute (ι (Q₁.prod Q₂) (v₁, 0)) (ι (Q₁.prod Q₂) (0, v₂)) := by
  have h := ι_mul_ι_add_swap (Q := Q₁.prod Q₂) (v₁, 0) (0, v₂)
  rw [QuadraticMap.polar_prod, QuadraticMap.polar_zero_right, QuadraticMap.polar_zero_left,
    add_zero, map_zero] at h
  have hneg := eq_neg_of_add_eq_zero_left h
  rw [Commute, SemiconjBy, hneg, neg_eq_iff_add_eq_zero]
  exact add_self_eq_zero' (K := K) _

theorem commute_map_inl_map_inr (a : CliffordAlgebra Q₁) (b : CliffordAlgebra Q₂) :
    Commute (map (QuadraticMap.Isometry.inl Q₁ Q₂) a)
      (map (QuadraticMap.Isometry.inr Q₁ Q₂) b) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r _
  | ι v₁ =>
    induction b using CliffordAlgebra.induction with
    | algebraMap r => rw [AlgHom.commutes]; exact (Algebra.commutes r _).symm
    | ι v₂ =>
      rw [map_apply_ι, map_apply_ι]
      exact commute_ι_inl_ι_inr Q₁ Q₂ v₁ v₂
    | mul b b' hb hb' => rw [map_mul]; exact hb.mul_right hb'
    | add b b' hb hb' => rw [map_add]; exact hb.add_right hb'
  | mul a a' ha ha' => rw [map_mul]; exact ha.mul_left ha'
  | add a a' ha ha' => rw [map_add]; exact ha.add_left ha'

noncomputable def cliffordProdHom :
    CliffordAlgebra Q₁ ⊗[K] CliffordAlgebra Q₂ →ₐ[K] CliffordAlgebra (Q₁.prod Q₂) :=
  Algebra.TensorProduct.lift (map (QuadraticMap.Isometry.inl Q₁ Q₂))
    (map (QuadraticMap.Isometry.inr Q₁ Q₂)) (commute_map_inl_map_inr Q₁ Q₂)

theorem cliffordProdHom_surjective : Function.Surjective (cliffordProdHom Q₁ Q₂) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← CliffordAlgebra.adjoin_range_ι, Algebra.adjoin_le_iff]
  rintro _ ⟨⟨v₁, v₂⟩, rfl⟩
  have : ι (Q₁.prod Q₂) (v₁, v₂) = ι (Q₁.prod Q₂) (v₁, 0) + ι (Q₁.prod Q₂) (0, v₂) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [this]
  refine add_mem ⟨ι Q₁ v₁ ⊗ₜ 1, ?_⟩ ⟨1 ⊗ₜ ι Q₂ v₂, ?_⟩
  · simp [cliffordProdHom]
  · simp [cliffordProdHom]

variable [FiniteDimensional K V₁] [FiniteDimensional K V₂]

theorem cliffordProdHom_bijective : Function.Bijective (cliffordProdHom Q₁ Q₂) := by
  have := finiteDimensional_cliffordAlgebra' Q₁
  have := finiteDimensional_cliffordAlgebra' Q₂
  have := finiteDimensional_cliffordAlgebra' (Q₁.prod Q₂)
  have hdim : finrank K (CliffordAlgebra Q₁ ⊗[K] CliffordAlgebra Q₂) =
      finrank K (CliffordAlgebra (Q₁.prod Q₂)) := by
    rw [Module.finrank_tensorProduct, finrank_cliffordAlgebra', finrank_cliffordAlgebra',
      finrank_cliffordAlgebra', Module.finrank_prod, pow_add]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (cliffordProdHom Q₁ Q₂).toLinearMap) hdim).2 (cliffordProdHom_surjective Q₁ Q₂),
    cliffordProdHom_surjective Q₁ Q₂⟩

noncomputable def cliffordProdEquiv :
    CliffordAlgebra Q₁ ⊗[K] CliffordAlgebra Q₂ ≃ₐ[K] CliffordAlgebra (Q₁.prod Q₂) :=
  AlgEquiv.ofBijective _ (cliffordProdHom_bijective Q₁ Q₂)

theorem isCentral_cliffordAlgebra_prod [Algebra.IsCentral K (CliffordAlgebra Q₁)]
    [Algebra.IsCentral K (CliffordAlgebra Q₂)] :
    Algebra.IsCentral K (CliffordAlgebra (Q₁.prod Q₂)) :=
  Algebra.IsCentral.of_algEquiv K _ _ (cliffordProdEquiv Q₁ Q₂)

end Prod


section Binary

variable (K : Type u) [Field K] (b c : K)

noncomputable def bilinBinary : LinearMap.BilinForm K (Fin 2 → K) :=
  LinearMap.mk₂ K (fun x y => x 0 * y 0 + b * x 0 * y 1 + c * x 1 * y 1)
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun r x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun r x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

noncomputable def binaryForm : QuadraticForm K (Fin 2 → K) := (bilinBinary K b c).toQuadraticMap

theorem binaryForm_apply (x : Fin 2 → K) :
    binaryForm K b c x = x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2 := by
  simp only [binaryForm, bilinBinary, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.mk₂_apply]
  ring

variable {K}

private noncomputable abbrev gA : CliffordAlgebra (binaryForm K b c) := ι _ (Pi.single 0 1)

private noncomputable abbrev gB : CliffordAlgebra (binaryForm K b c) := ι _ (Pi.single 1 1)

private theorem gA_mul_gA : gA b c * gA b c = 1 := by
  rw [ι_sq_scalar, binaryForm_apply]
  simp

private theorem gB_mul_gB : gB b c * gB b c = algebraMap K _ c := by
  rw [ι_sq_scalar, binaryForm_apply]
  simp

private theorem gB_mul_gA : gB b c * gA b c = algebraMap K _ b - gA b c * gB b c := by
  rw [eq_sub_iff_add_eq, add_comm, ι_mul_ι_add_swap]
  congr 1
  simp only [QuadraticMap.polar, binaryForm_apply]
  simp
  ring

private noncomputable def mono : Fin 4 → CliffordAlgebra (binaryForm K b c) :=
  ![1, gA b c, gB b c, gA b c * gB b c]

private theorem ι_eq (v : Fin 2 → K) : ι (binaryForm K b c) v = v 0 • gA b c + v 1 • gB b c := by
  have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → K) + v 1 • Pi.single 1 1 := by
    funext k
    fin_cases k <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul]

private theorem range_mono :
    Set.range (mono b c) = {1, gA b c, gB b c, gA b c * gB b c} := by
  simp only [mono, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]

private theorem gA_mul_mem {z : CliffordAlgebra (binaryForm K b c)}
    (hz : z ∈ Submodule.span K (Set.range (mono b c))) :
    gA b c * z ∈ Submodule.span K (Set.range (mono b c)) := by
  rw [range_mono] at hz ⊢
  have h1 : (1 : CliffordAlgebra (binaryForm K b c)) ∈
      Submodule.span K {1, gA b c, gB b c, gA b c * gB b c} := Submodule.subset_span (by simp)
  have hA : gA b c ∈ Submodule.span K {1, gA b c, gB b c, gA b c * gB b c} :=
    Submodule.subset_span (by simp)
  have hB : gB b c ∈ Submodule.span K {1, gA b c, gB b c, gA b c * gB b c} :=
    Submodule.subset_span (by simp)
  have hAB : gA b c * gB b c ∈ Submodule.span K {1, gA b c, gB b c, gA b c * gB b c} :=
    Submodule.subset_span (by simp)
  induction hz using Submodule.span_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · rwa [mul_one]
    · rwa [gA_mul_gA]
    · exact hAB
    · rwa [← mul_assoc, gA_mul_gA, one_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

private theorem gB_mul_mem {z : CliffordAlgebra (binaryForm K b c)}
    (hz : z ∈ Submodule.span K (Set.range (mono b c))) :
    gB b c * z ∈ Submodule.span K (Set.range (mono b c)) := by
  rw [range_mono] at hz ⊢
  have h1 : (1 : CliffordAlgebra (binaryForm K b c)) ∈
      Submodule.span K {1, gA b c, gB b c, gA b c * gB b c} := Submodule.subset_span (by simp)
  have hA : gA b c ∈ Submodule.span K {1, gA b c, gB b c, gA b c * gB b c} :=
    Submodule.subset_span (by simp)
  have hB : gB b c ∈ Submodule.span K {1, gA b c, gB b c, gA b c * gB b c} :=
    Submodule.subset_span (by simp)
  have hAB : gA b c * gB b c ∈ Submodule.span K {1, gA b c, gB b c, gA b c * gB b c} :=
    Submodule.subset_span (by simp)
  induction hz using Submodule.span_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · rwa [mul_one]
    · rw [gB_mul_gA, Algebra.algebraMap_eq_smul_one]
      exact sub_mem (Submodule.smul_mem _ _ h1) hAB
    · rw [gB_mul_gB, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ h1
    · rw [← mul_assoc, gB_mul_gA, sub_mul, mul_assoc, gB_mul_gB, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
      exact sub_mem (Submodule.smul_mem _ _ hB) (Submodule.smul_mem _ _ hA)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

private theorem span_mono : Submodule.span K (Set.range (mono b c)) = ⊤ := by
  have key : ∀ x : CliffordAlgebra (binaryForm K b c), ∀ z ∈ Submodule.span K
      (Set.range (mono b c)), x * z ∈ Submodule.span K (Set.range (mono b c)) := by
    intro x
    induction x using CliffordAlgebra.induction with
    | algebraMap r =>
      intro z hz
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ r hz
    | ι v =>
      intro z hz
      rw [ι_eq, add_mul, smul_mul_assoc, smul_mul_assoc]
      exact add_mem (Submodule.smul_mem _ _ (gA_mul_mem b c hz))
        (Submodule.smul_mem _ _ (gB_mul_mem b c hz))
    | mul x y hx hy => intro z hz; rw [mul_assoc]; exact hx _ (hy z hz)
    | add x y hx hy => intro z hz; rw [add_mul]; exact add_mem (hx z hz) (hy z hz)
  rw [eq_top_iff]
  intro x _
  simpa using key x 1 (Submodule.subset_span (Set.mem_range.mpr ⟨0, rfl⟩))

private theorem linearIndependent_mono : LinearIndependent K (mono b c) := by
  have := finiteDimensional_cliffordAlgebra' (binaryForm K b c)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank (span_mono b c).ge ?_
  rw [Fintype.card_fin, finrank_cliffordAlgebra', Module.finrank_fin_fun]
  norm_num

variable [CharP K 2]

theorem isCentral_cliffordAlgebra_binary (hb : b ≠ 0) :
    Algebra.IsCentral K (CliffordAlgebra (binaryForm K b c)) where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    have hmem : x ∈ Submodule.span K (Set.range (mono b c)) := by
      rw [span_mono]; exact Submodule.mem_top
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hli := linearIndependent_mono b c
    rw [Fintype.linearIndependent_iff] at hli
    simp only [Fin.sum_univ_four, mono, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hx ⊢
    have hA := hx (gA b c)
    have hB := hx (gB b c)
    have eA : (a 0 • 1 + a 1 • gA b c + a 2 • gB b c + a 3 • (gA b c * gB b c)) * gA b c -
        gA b c * (a 0 • 1 + a 1 • gA b c + a 2 • gB b c + a 3 • (gA b c * gB b c)) =
        (a 2 * b) • mono b c 0 + (a 3 * b) • mono b c 1 + (-(2 * a 3)) • mono b c 2 +
          (-(2 * a 2)) • mono b c 3 := by
      simp only [mono, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc,
        gA_mul_gA, gB_mul_gA]
      rw [← mul_assoc (gA b c) (gA b c), gA_mul_gA, one_mul, mul_sub, ← mul_assoc (gA b c)
        (gA b c), gA_mul_gA, one_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
      module
    have eB : (a 0 • 1 + a 1 • gA b c + a 2 • gB b c + a 3 • (gA b c * gB b c)) * gB b c -
        gB b c * (a 0 • 1 + a 1 • gA b c + a 2 • gB b c + a 3 • (gA b c * gB b c)) =
        (-(a 1 * b)) • mono b c 0 + (2 * a 3 * c) • mono b c 1 + (-(a 3 * b)) • mono b c 2 +
          (2 * a 1) • mono b c 3 := by
      simp only [mono, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc,
        gB_mul_gB, gB_mul_gA]
      rw [← mul_assoc (gB b c) (gA b c), gB_mul_gA, sub_mul, mul_assoc (gA b c) (gB b c),
        gB_mul_gB]
      simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
      module
    have hd := hli ![a 2 * b, a 3 * b, -(2 * a 3), -(2 * a 2)] (by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
      rw [← eA, sub_eq_zero.mpr hA.symm])
    have hd' := hli ![-(a 1 * b), 2 * a 3 * c, -(a 3 * b), 2 * a 1] (by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
      rw [← eB, sub_eq_zero.mpr hB.symm])
    have ha2 : a 2 = 0 := by
      have := hd 0
      simp only [Fin.isValue, Matrix.cons_val_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hb
    have ha3 : a 3 = 0 := by
      have := hd 1
      simp only [Fin.isValue, Matrix.cons_val_one] at this
      exact (mul_eq_zero.mp this).resolve_right hb
    have ha1 : a 1 = 0 := by
      have := hd' 0
      simp only [Fin.isValue, Matrix.cons_val_zero, neg_eq_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hb
    rw [ha1, ha2, ha3, zero_smul, zero_smul, zero_smul, add_zero, add_zero, add_zero,
      ← Algebra.algebraMap_eq_smul_one]
    exact Subalgebra.algebraMap_mem _ _

end Binary


section Minus

variable (n : ℕ) (K : Type u) [Field K] (b c : K)

noncomputable def quadMinusIsometry :
    (quadMinus n K b c).IsometryEquiv ((quadPlus (n - 1) K).prod (binaryForm K b c)) where
  toFun v := (Sum.elim (fun i => v (.inl i)) (fun i => v (.inr (.inl i))),
    fun k => v (.inr (.inr k)))
  invFun x := Sum.elim (fun i => x.1 (.inl i)) (Sum.elim (fun i => x.1 (.inr i)) x.2)
  left_inv v := by
    funext j
    rcases j with i | i | k <;> rfl
  right_inv x := by
    obtain ⟨x, y⟩ := x
    refine Prod.ext ?_ rfl
    funext j
    rcases j with i | i <;> rfl
  map_add' v w := by
    refine Prod.ext ?_ rfl
    funext j
    rcases j with i | i <;> rfl
  map_smul' r v := by
    refine Prod.ext ?_ rfl
    funext j
    rcases j with i | i <;> rfl
  map_app' v := by
    simp only [QuadraticMap.prod_apply, quadPlus_apply, binaryForm_apply, quadMinus_apply,
      Sum.elim_inl, Sum.elim_inr]
    ring

variable {K}

theorem isCentral_cliffordAlgebra_quadMinus_of_charTwo [CharP K 2] (hb : b ≠ 0) :
    Algebra.IsCentral K (CliffordAlgebra (quadMinus n K b c)) := by
  have := isCentral_cliffordAlgebra_quadPlus K (n - 1)
  have := isCentral_cliffordAlgebra_binary b c hb
  have := isCentral_cliffordAlgebra_prod (quadPlus (n - 1) K) (binaryForm K b c)
  exact Algebra.IsCentral.of_algEquiv K _ _ (equivOfIsometry (quadMinusIsometry n K b c)).symm

theorem isCentral_cliffordAlgebra_quadMinus [Finite K] (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Algebra.IsCentral K (CliffordAlgebra (quadMinus n K b c)) := by
  by_cases h2 : (2 : K) = 0
  · have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    have hd := discr_ne_zero_of_finite h
    have hb : b ≠ 0 := by
      rintro rfl
      apply hd
      have h4 : (4 : K) = 0 := by
        rw [show (4 : K) = 2 * 2 by norm_num, h2, zero_mul]
      rw [h4]
      ring
    exact isCentral_cliffordAlgebra_quadMinus_of_charTwo n b c hb
  · have : NeZero (2 : K) := ⟨h2⟩
    refine CliffordAlgebra.isCentral_of_even_finrank (nondegenerate_quadMinus_of_finite n K h) ?_
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    exact ⟨n - 1 + 1, by ring⟩

end Minus

end CFSG.LieType.Universal.Spin
