module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDFrob

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section Trace

variable {p : ℕ} {F : Type} [Field F] [Algebra (ZMod p) F] {W : Type} [AddCommGroup W] [Module (ZMod p) W]

@[expose] noncomputable def traceTensor : F ⊗[ZMod p] W →ₗ[ZMod p] W :=
  TensorProduct.lift ((LinearMap.lsmul (ZMod p) W).comp (Algebra.trace (ZMod p) F))

theorem traceTensor_tmul (c : F) (w : W) :
    traceTensor (c ⊗ₜ[ZMod p] w) = Algebra.trace (ZMod p) F c • w := by
  simp [traceTensor]

end Trace

section Descent

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]
  {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod p) W]

omit [Finite F] in
theorem frobTensor_pow_tmul (i : ℕ) (c : F) (w : W) :
    (frobTensor W ^ i) (c ⊗ₜ[ZMod p] w) = (c ^ p ^ i) ⊗ₜ[ZMod p] w := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ih, frobTensor_tmul, ← pow_mul, ← pow_succ]

theorem sum_frobTensor_pow (y : F ⊗[ZMod p] W) :
    ∑ i ∈ Finset.range (Module.finrank (ZMod p) F), (frobTensor W ^ i) y =
      (1 : F) ⊗ₜ[ZMod p] traceTensor y := by
  induction y using TensorProduct.inductionOn with
  | tmul c w =>
    simp only [frobTensor_pow_tmul, traceTensor_tmul]
    rw [← TensorProduct.sum_tmul]
    have h := FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) F c
    rw [Nat.card_zmod] at h
    rw [← h, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    rw [map_add, TensorProduct.tmul_add, ← hx, ← hy, ← Finset.sum_add_distrib]
    simp [map_add]

omit [CharP F p] in
theorem exists_trace_expansion :
    ∃ b' b : Fin (Module.finrank (ZMod p) F) → F, ∀ y : F ⊗[ZMod p] W,
      y = ∑ i, b' i • ((1 : F) ⊗ₜ[ZMod p] traceTensor (b i • y)) := by
  classical
  let bs := Module.finBasis (ZMod p) F
  have hnd := traceForm_nondegenerate (ZMod p) F
  let ds := (Algebra.traceForm (ZMod p) F).dualBasis hnd bs
  refine ⟨fun i => ds i, fun i => bs i, fun y => ?_⟩
  induction y using TensorProduct.inductionOn with
  | tmul c w =>
    have hterm : ∀ i, ds i • ((1 : F) ⊗ₜ[ZMod p] traceTensor (bs i • (c ⊗ₜ[ZMod p] w))) =
        (Algebra.trace (ZMod p) F (bs i * c) • ds i) ⊗ₜ[ZMod p] w := by
      intro i
      simp only [TensorProduct.smul_tmul', smul_eq_mul, traceTensor_tmul, mul_one]
      rw [← TensorProduct.smul_tmul]
    simp only [hterm]
    rw [← TensorProduct.sum_tmul]
    congr 1
    have h := ds.sum_repr c
    simp only [ds, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at h
    simpa [mul_comm] using h.symm
  | add x y hx hy =>
    simp only [smul_add, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hx, ← hy]

theorem frobTensor_stable_eq_bot_or_top (σ : Representation (ZMod p) G W)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod p) G) σ.asModule)
    (T : Submodule F (F ⊗[ZMod p] W)) (hΦ : ∀ x ∈ T, frobTensor W x ∈ T)
    (hG : ∀ g : G, ∀ x ∈ T, (σ g).baseChange F x ∈ T) : T = ⊥ ∨ T = ⊤ := by
  classical
  have hirr : σ.IsIrreducible := (Representation.irreducible_iff_isSimpleModule_asModule σ).mpr hW
  have hpow : ∀ (i : ℕ) (y : F ⊗[ZMod p] W), y ∈ T → (frobTensor W ^ i) y ∈ T := by
    intro i
    induction i with
    | zero => intro y hy; simpa using hy
    | succ i ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      exact hΦ _ (ih y hy)
  have hrat : ∀ x ∈ T, ∀ c : F, (1 : F) ⊗ₜ[ZMod p] traceTensor (c • x) ∈ T := by
    intro x hx c
    rw [← sum_frobTensor_pow]
    exact T.sum_mem fun i _ => hpow i _ (T.smul_mem c hx)
  let R : Subrepresentation σ :=
    { toSubmodule :=
        { carrier := {w | (1 : F) ⊗ₜ[ZMod p] w ∈ T}
          add_mem' := fun {a b} ha hb => by
            have h := T.add_mem ha hb
            rwa [← TensorProduct.tmul_add] at h
          zero_mem' := by simp
          smul_mem' := fun a w hw => by
            show (1 : F) ⊗ₜ[ZMod p] (a • w) ∈ T
            rw [TensorProduct.tmul_smul, ← algebraMap_smul F a]
            exact T.smul_mem _ hw }
      apply_mem_toSubmodule := fun g w hw => by
        show (1 : F) ⊗ₜ[ZMod p] (σ g w) ∈ T
        have h := hG g _ hw
        simpa using h }
  have hmemR : ∀ w, w ∈ R ↔ (1 : F) ⊗ₜ[ZMod p] w ∈ T := fun w => Iff.rfl
  rcases @IsSimpleOrder.eq_bot_or_eq_top _ _ _ hirr R with h | h
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [Submodule.mem_bot]
    obtain ⟨b', b, hexp⟩ := exists_trace_expansion (p := p) (F := F) (W := W)
    rw [hexp x]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : traceTensor (b i • x) ∈ R := (hmemR _).mpr (hrat x hx (b i))
    rw [h] at hi
    have h0 : traceTensor (b i • x) = 0 := hi
    rw [h0, TensorProduct.tmul_zero, smul_zero]
  · right
    refine eq_top_iff.mpr fun x hx => ?_
    clear hx
    induction x using TensorProduct.inductionOn with
    | tmul c w =>
      have hw : w ∈ R := by rw [h]; trivial
      have h1 : (1 : F) ⊗ₜ[ZMod p] w ∈ T := hw
      have h2 : c ⊗ₜ[ZMod p] w = c • ((1 : F) ⊗ₜ[ZMod p] w) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h2]
      exact T.smul_mem c h1
    | add x y hx hy => exact T.add_mem hx hy

end Descent

end CFSG.GH74.GLS.Stage4.Rest
