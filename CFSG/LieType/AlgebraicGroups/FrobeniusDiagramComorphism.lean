module

public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupIdeal
public import CFSG.LieType.AlgebraicGroups.GLCoordPoints
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Algebra
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct WithConv
open scoped CFSG.ConvolutionPoints

section Tangent

variable {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A] {x : A →ₐ[k] k}
  {D : A →ₗ[k] k}

theorem tangent_pow (hD : D ∈ tangentSpace k A x) (a : A) (n : ℕ) :
    D (a ^ (n + 1)) = ((n + 1 : ℕ) : k) * x a ^ n * D a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, (mem_tangentSpace.1 hD) (a ^ (n + 1)) a, ih, map_pow]
    push_cast
    ring

theorem tangent_pow_char (p : ℕ) [CharP k p] {e : ℕ} (he : 1 ≤ e)
    (hD : D ∈ tangentSpace k A x) (a : A) : D (a ^ p ^ e) = 0 := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    rw [zero_pow (by omega), pow_zero]
    exact map_one_of_mem_tangentSpace hD
  obtain ⟨n, hn⟩ : ∃ n, p ^ e = n + 1 := ⟨p ^ e - 1, by have := pow_pos hp e; omega⟩
  rw [hn, tangent_pow hD a n, ← hn]
  have : ((p ^ e : ℕ) : k) = 0 := by
    rw [CharP.cast_eq_zero_iff k p]
    exact dvd_pow_self p (by omega)
  rw [this, zero_mul, zero_mul]

theorem eq_zero_of_mem_tangentSpace_of_adjoin_eq_top {s : Set A}
    (hs : Algebra.adjoin k s = ⊤) (hD : D ∈ tangentSpace k A x) (h0 : ∀ a ∈ s, D a = 0) :
    D = 0 := by
  let S : Subalgebra k A :=
    { carrier := {a | D a = 0}
      mul_mem' := fun {a b} ha hb => by
        change D (a * b) = 0
        rw [(mem_tangentSpace.1 hD) a b, ha, hb, mul_zero, mul_zero, add_zero]
      add_mem' := fun {a b} ha hb => by
        change D (a + b) = 0
        rw [map_add, ha, hb, add_zero]
      algebraMap_mem' := fun c => by
        change D (algebraMap k A c) = 0
        rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one_of_mem_tangentSpace hD,
          smul_zero] }
  have hle : Algebra.adjoin k s ≤ S := Algebra.adjoin_le h0
  rw [hs] at hle
  exact LinearMap.ext fun a => hle Algebra.mem_top

end Tangent

section PointDetection

variable {k : Type} [Field k] [IsAlgClosed k] {B : Type} [CommRing B] [HopfAlgebra k B]
  [Algebra.FiniteType k B] [IsReduced B]

omit [IsAlgClosed k] [Algebra.FiniteType k B] [IsReduced B] in
theorem productMap_comul (y z : B →ₐ[k] k) (b : B) :
    Algebra.TensorProduct.productMap y z (Coalgebra.comul b) = (toConv y * toConv z).ofConv b := by
  rw [AlgHom.convMul_apply]
  induction Coalgebra.comul (R := k) b with
  | tmul a c => simp
  | add s t hs ht => simp only [map_add, hs, ht]

omit [IsAlgClosed k] [Algebra.FiniteType k B] [IsReduced B] in
theorem productMap_map_apply (y z : B →ₐ[k] k) (f g : B →ₐ[k] B) (t : B ⊗[k] B) :
    Algebra.TensorProduct.productMap y z (Algebra.TensorProduct.map f g t) =
      Algebra.TensorProduct.productMap (y.comp f) (z.comp g) t := by
  induction t with
  | tmul a c => simp
  | add s t hs ht => simp only [map_add, hs, ht]

omit [IsAlgClosed k] [Algebra.FiniteType k B] [IsReduced B] in
theorem one_comp_of_pointMul (φ : B →ₐ[k] B)
    (hφ : ∀ y z : WithConv (B →ₐ[k] k), toConv ((y * z).ofConv.comp φ) =
      toConv (y.ofConv.comp φ) * toConv (z.ofConv.comp φ)) :
    toConv ((1 : WithConv (B →ₐ[k] k)).ofConv.comp φ) = 1 := by
  have h := hφ 1 1
  rw [mul_one] at h
  exact mul_eq_left.1 h.symm

@[expose] def bialgHomOfPointMul (φ : B →ₐ[k] B)
    (hφ : ∀ y z : WithConv (B →ₐ[k] k), toConv ((y * z).ofConv.comp φ) =
      toConv (y.ofConv.comp φ) * toConv (z.ofConv.comp φ)) : B →ₐc[k] B :=
  BialgHom.ofAlgHom φ
    (by
      have h := congrArg ofConv (one_comp_of_pointMul φ hφ)
      rw [ofConv_toConv, convOne_ofConv_eq_counit] at h
      exact h)
    (by
      refine AlgHom.ext fun b => ?_
      rw [← sub_eq_zero]
      refine tensor_eq_zero_of_forall_algHom k B B _ fun y z => ?_
      rw [map_sub, sub_eq_zero, AlgHom.comp_apply, AlgHom.comp_apply,
        Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply, productMap_map_apply,
        productMap_comul, productMap_comul]
      have h := congrArg (fun w : WithConv (B →ₐ[k] k) => w.ofConv b) (hφ (toConv y) (toConv z))
      simp only [AlgHom.comp_apply] at h
      exact h.symm)

omit [IsAlgClosed k] [Algebra.FiniteType k B] [IsReduced B] in
@[simp] theorem coe_bialgHomOfPointMul [IsAlgClosed k] [Algebra.FiniteType k B] [IsReduced B]
    (φ : B →ₐ[k] B)
    (hφ : ∀ y z : WithConv (B →ₐ[k] k), toConv ((y * z).ofConv.comp φ) =
      toConv (y.ofConv.comp φ) * toConv (z.ofConv.comp φ)) :
    (bialgHomOfPointMul φ hφ : B →ₐ[k] B) = φ :=
  rfl

end PointDetection

section Descent

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

theorem map_mem_subgroupIdeal (G : Subgroup (WithConv (A →ₐ[k] k))) (φ : A →ₐ[k] A)
    (hφ : ∀ y ∈ subgroupPoints G, y.comp φ ∈ subgroupPoints G) {a : A}
    (ha : a ∈ subgroupIdeal G) : φ a ∈ subgroupIdeal G :=
  mem_pointsIdeal.2 fun y hy => mem_pointsIdeal.1 ha _ (hφ y hy)

@[expose] def quotientCo (G : Subgroup (WithConv (A →ₐ[k] k))) (φ : A →ₐ[k] A)
    (hφ : ∀ y ∈ subgroupPoints G, y.comp φ ∈ subgroupPoints G) :
    (A ⧸ subgroupIdeal G) →ₐ[k] (A ⧸ subgroupIdeal G) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ k _).comp φ) fun _ ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (map_mem_subgroupIdeal G φ hφ ha)

theorem quotientCo_comp_mkₐ (G : Subgroup (WithConv (A →ₐ[k] k))) (φ : A →ₐ[k] A)
    (hφ : ∀ y ∈ subgroupPoints G, y.comp φ ∈ subgroupPoints G) :
    (quotientCo G φ hφ).comp (Ideal.Quotient.mkₐ k (subgroupIdeal G)) =
      (Ideal.Quotient.mkₐ k (subgroupIdeal G)).comp φ :=
  AlgHom.ext fun _ => rfl

theorem comp_quotientCo_comp_mkₐ (G : Subgroup (WithConv (A →ₐ[k] k))) (φ : A →ₐ[k] A)
    (hφ : ∀ y ∈ subgroupPoints G, y.comp φ ∈ subgroupPoints G)
    (ψ : (A ⧸ subgroupIdeal G) →ₐ[k] k) :
    (ψ.comp (quotientCo G φ hφ)).comp (Ideal.Quotient.mkₐ k (subgroupIdeal G)) =
      (ψ.comp (Ideal.Quotient.mkₐ k (subgroupIdeal G))).comp φ := by
  rw [AlgHom.comp_assoc, quotientCo_comp_mkₐ, AlgHom.comp_assoc]

variable [IsAlgClosed k] [Algebra.FiniteType k A]

theorem toConv_comp_mkₐ_mul (G : Subgroup (WithConv (A →ₐ[k] k)))
    (ψ χ : WithConv ((A ⧸ subgroupIdeal G) →ₐ[k] k)) :
    toConv ((ψ * χ).ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal G))) =
      toConv (ψ.ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal G))) *
        toConv (χ.ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal G))) :=
  congrArg toConv
    (AlgHom.convMul_comp_bialgHom_distrib ψ χ (Bialgebra.Quotient.mkBialgHom (subgroupIdeal G)))

theorem quotientCo_pointMul (G : Subgroup (WithConv (A →ₐ[k] k))) (φ : A →ₐ[k] A)
    (hφ : ∀ y ∈ subgroupPoints G, y.comp φ ∈ subgroupPoints G)
    (hmul : ∀ y z : WithConv (A →ₐ[k] k), toConv ((y * z).ofConv.comp φ) =
      toConv (y.ofConv.comp φ) * toConv (z.ofConv.comp φ))
    (ψ χ : WithConv ((A ⧸ subgroupIdeal G) →ₐ[k] k)) :
    toConv ((ψ * χ).ofConv.comp (quotientCo G φ hφ)) =
      toConv (ψ.ofConv.comp (quotientCo G φ hφ)) * toConv (χ.ofConv.comp (quotientCo G φ hφ)) := by
  apply WithConv.ext
  apply Ideal.Quotient.algHom_ext k
  rw [ofConv_toConv, comp_quotientCo_comp_mkₐ]
  have h2 := hmul (toConv (ψ.ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal G))))
    (toConv (χ.ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal G))))
  rw [← toConv_comp_mkₐ_mul] at h2
  have h1 := toConv_comp_mkₐ_mul G (toConv (ψ.ofConv.comp (quotientCo G φ hφ)))
    (toConv (χ.ofConv.comp (quotientCo G φ hφ)))
  simp only [comp_quotientCo_comp_mkₐ] at h1 h2
  rw [← h1] at h2
  exact congrArg ofConv h2

end Descent

section Frobenius

variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι] (p : ℕ) [Fact p.Prime]
  [CharP k p]

instance charP_GLCoord : CharP (GLCoord k ι) p :=
  charP_of_injective_algebraMap (algebraMap k (GLCoord k ι)).injective p

theorem det_map_pow_glEntryMatrix (e : ℕ) :
    ((glEntryMatrix k ι).map (· ^ p ^ e)).det * glDetInv k ι ^ p ^ e = 1 := by
  have h : (glEntryMatrix k ι).map (· ^ p ^ e) =
      (iterateFrobenius (GLCoord k ι) p e).mapMatrix (glEntryMatrix k ι) := by
    ext a b
    rfl
  rw [h, ← RingHom.map_det, iterateFrobenius_def, ← mul_pow, det_glEntryMatrix_mul_glDetInv,
    one_pow]

@[expose] def frobCo (e : ℕ) : GLCoord k ι →ₐ[k] GLCoord k ι :=
  GLCoord.lift k ι ((glEntryMatrix k ι).map (· ^ p ^ e)) (glDetInv k ι ^ p ^ e)
    (det_map_pow_glEntryMatrix p e)

theorem frobCo_glEntry (e : ℕ) (a b : ι) :
    frobCo p e (glEntry k ι a b) = glEntry k ι a b ^ p ^ e :=
  GLCoord.lift_glEntry k ι _ _ _ a b

theorem frobCo_glDetInv (e : ℕ) : frobCo p e (glDetInv k ι) = glDetInv k ι ^ p ^ e :=
  GLCoord.lift_glDetInv k ι _ _ _

theorem tangent_comp_frobCo {e : ℕ} (he : 1 ≤ e) {x : GLCoord k ι →ₐ[k] k}
    {D : GLCoord k ι →ₗ[k] k} (hD : D ∈ tangentSpace k (GLCoord k ι) x) :
    D ∘ₗ (frobCo p e).toLinearMap = 0 := by
  have hD' : D ∘ₗ (frobCo p e).toLinearMap ∈ tangentSpace k (GLCoord k ι) (x.comp (frobCo p e)) :=
    (tangentMap (frobCo p e) rfl ⟨D, hD⟩).2
  refine eq_zero_of_mem_tangentSpace_of_adjoin_eq_top (GLCoord.adjoin_eq_top k ι) hD' ?_
  rintro a (⟨⟨i, j⟩, rfl⟩ | ha)
  · change D (frobCo p e (glEntry k ι i j)) = 0
    rw [frobCo_glEntry]
    exact tangent_pow_char p he hD _
  · rw [Set.mem_singleton_iff] at ha
    subst ha
    change D (frobCo p e (glDetInv k ι)) = 0
    rw [frobCo_glDetInv]
    exact tangent_pow_char p he hD _

end Frobenius

end CFSG.LieType.AlgebraicGroups
