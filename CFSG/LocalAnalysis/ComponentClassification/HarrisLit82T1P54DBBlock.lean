module

public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup Matrix Assembly.LowTwoRank

variable {K : Type} [Field K]

section Iso

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def isoGroup (Q : (ι → K) → K) : Subgroup (GL ι K) where
  carrier := {A | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}
  mul_mem' {A B} hA hB v := by
    change Q (((A * B : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v
    rw [Units.val_mul, ← mulVec_mulVec, hA, hB]
  one_mem' v := by
    change Q (((1 : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v
    rw [Units.val_one, one_mulVec]
  inv_mem' {A} hA v := by
    change Q (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v
    rw [← hA (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v), mulVec_mulVec, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mulVec]

theorem mem_isoGroup {Q : (ι → K) → K} {A : GL ι K} :
    A ∈ isoGroup Q ↔ ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v :=
  Iff.rfl

theorem statedOmega_eq (Q : (ι → K) → K) : StatedOmega Q = ⁅isoGroup Q, isoGroup Q⁆ := by
  have h : Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} =
      isoGroup Q :=
    Subgroup.closure_eq (isoGroup Q)
  rw [StatedOmega, h]

theorem statedOmega_le_isoGroup (Q : (ι → K) → K) : StatedOmega Q ≤ isoGroup Q := by
  rw [statedOmega_eq]
  exact Subgroup.commutator_le_self _

theorem conj_mem_commutator {G : Type*} [Group G] {H : Subgroup G} {h x : G} (hh : h ∈ H)
    (hx : x ∈ ⁅H, H⁆) : h * x * h⁻¹ ∈ ⁅H, H⁆ := by
  have hH : H.map (MulAut.conj h).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hh hy) (inv_mem hh)
  have h1 : (MulAut.conj h).toMonoidHom x ∈ (⁅H, H⁆).map (MulAut.conj h).toMonoidHom :=
    mem_map_of_mem _ hx
  rw [map_commutator] at h1
  exact commutator_mono hH hH h1

theorem conj_mem_statedOmega {Q : (ι → K) → K} {h x : GL ι K} (hh : h ∈ isoGroup Q)
    (hx : x ∈ StatedOmega Q) : h * x * h⁻¹ ∈ StatedOmega Q := by
  rw [statedOmega_eq] at hx ⊢
  exact conj_mem_commutator hh hx

end Iso

section Reindex

variable {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ]

@[expose] def reGL (e : σ ≃ τ) : GL σ K ≃* GL τ K :=
  Units.mapEquiv (Matrix.reindexRingEquiv K e).toMulEquiv

theorem coe_reGL (e : σ ≃ τ) (A : GL σ K) :
    ((reGL e A : GL τ K) : Matrix τ τ K) = Matrix.reindex e e (A : Matrix σ σ K) :=
  rfl

theorem reGL_mulVec (e : σ ≃ τ) (A : GL σ K) (w : τ → K) :
    ((reGL e A : GL τ K) : Matrix τ τ K) *ᵥ w = ((A : Matrix σ σ K) *ᵥ (w ∘ e)) ∘ e.symm := by
  rw [coe_reGL, Matrix.reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm]

@[expose] def pullQ (e : σ ≃ τ) (Q : (τ → K) → K) (v : σ → K) : K :=
  Q (v ∘ e.symm)

theorem reGL_mem_isoGroup_iff (e : σ ≃ τ) {Q : (τ → K) → K} {A : GL σ K} :
    reGL e A ∈ isoGroup Q ↔ A ∈ isoGroup (pullQ e Q) := by
  constructor
  · intro h v
    have h1 := h (v ∘ e.symm)
    rw [reGL_mulVec, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] at h1
    exact h1
  · intro h w
    rw [reGL_mulVec]
    have h1 := h (w ∘ e)
    rw [pullQ, pullQ, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at h1
    exact h1

theorem map_reGL_statedOmega (e : σ ≃ τ) (Q : (τ → K) → K) :
    (StatedOmega (pullQ e Q)).map (reGL e).toMonoidHom = StatedOmega Q := by
  have hiso : (isoGroup (pullQ e Q)).map (reGL e).toMonoidHom = isoGroup Q := by
    ext B
    rw [mem_map_equiv, ← reGL_mem_isoGroup_iff e, MulEquiv.apply_symm_apply]
  rw [statedOmega_eq, statedOmega_eq, map_commutator, hiso]

theorem reGL_neg_one (e : σ ≃ τ) : reGL e (-1 : GL σ K) = -1 := by
  apply Units.ext
  rw [coe_reGL, Units.val_neg, Units.val_neg, Units.val_one, Units.val_one]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.neg_apply, Matrix.one_apply,
    e.symm.injective.eq_iff]

end Reindex

section Block

variable {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]

@[expose] def sumQ (Q₁ : (ι₁ → K) → K) (Q₂ : (ι₂ → K) → K) (v : ι₁ ⊕ ι₂ → K) : K :=
  Q₁ (fun i => v (.inl i)) + Q₂ (fun j => v (.inr j))

omit [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] in
theorem sumQ_elim (Q₁ : (ι₁ → K) → K) (Q₂ : (ι₂ → K) → K) (x : ι₁ → K) (y : ι₂ → K) :
    sumQ Q₁ Q₂ (Sum.elim x y) = Q₁ x + Q₂ y :=
  rfl

variable (ι₂) in
@[expose] def blockL : GL ι₁ K →* GL (ι₁ ⊕ ι₂) K where
  toFun g := ⟨fromBlocks (g : Matrix ι₁ ι₁ K) 0 0 1,
    fromBlocks ((g⁻¹ : GL ι₁ K) : Matrix ι₁ ι₁ K) 0 0 1,
    by rw [fromBlocks_multiply]; simp, by rw [fromBlocks_multiply]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [fromBlocks_multiply])

variable (ι₁) in
@[expose] def blockR : GL ι₂ K →* GL (ι₁ ⊕ ι₂) K where
  toFun g := ⟨fromBlocks 1 0 0 (g : Matrix ι₂ ι₂ K),
    fromBlocks 1 0 0 ((g⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K),
    by rw [fromBlocks_multiply]; simp, by rw [fromBlocks_multiply]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [fromBlocks_multiply])

@[simp]
theorem coe_blockL (g : GL ι₁ K) :
    ((blockL ι₂ g : GL (ι₁ ⊕ ι₂) K) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K) =
      fromBlocks (g : Matrix ι₁ ι₁ K) 0 0 1 :=
  rfl

@[simp]
theorem coe_blockR (g : GL ι₂ K) :
    ((blockR ι₁ g : GL (ι₁ ⊕ ι₂) K) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K) =
      fromBlocks 1 0 0 (g : Matrix ι₂ ι₂ K) :=
  rfl

theorem blockL_injective : Function.Injective (blockL ι₂ : GL ι₁ K →* GL (ι₁ ⊕ ι₂) K) := by
  intro g h hgh
  have e := congrArg (fun x : GL (ι₁ ⊕ ι₂) K => (x : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K)) hgh
  simp only [coe_blockL] at e
  exact Units.ext (fromBlocks_inj.mp e).1

theorem blockL_mulVec (g : GL ι₁ K) (v : ι₁ ⊕ ι₂ → K) :
    ((blockL ι₂ g : GL (ι₁ ⊕ ι₂) K) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K) *ᵥ v =
      Sum.elim ((g : Matrix ι₁ ι₁ K) *ᵥ fun i => v (.inl i)) fun j => v (.inr j) := by
  rw [coe_blockL, fromBlocks_mulVec]
  simp only [zero_mulVec, one_mulVec, add_zero, zero_add]
  rfl

theorem blockR_mulVec (g : GL ι₂ K) (v : ι₁ ⊕ ι₂ → K) :
    ((blockR ι₁ g : GL (ι₁ ⊕ ι₂) K) : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) K) *ᵥ v =
      Sum.elim (fun i => v (.inl i)) ((g : Matrix ι₂ ι₂ K) *ᵥ fun j => v (.inr j)) := by
  rw [coe_blockR, fromBlocks_mulVec]
  simp only [zero_mulVec, one_mulVec, add_zero, zero_add]
  rfl

theorem commute_blockL_blockR (g : GL ι₁ K) (h : GL ι₂ K) :
    blockL ι₂ g * blockR ι₁ h = blockR ι₁ h * blockL ι₂ g :=
  Units.ext (by simp [fromBlocks_multiply])

theorem blockL_neg_one_mul_blockR_neg_one :
    blockL ι₂ (-1 : GL ι₁ K) * blockR ι₁ (-1 : GL ι₂ K) = -1 := by
  apply Units.ext
  simp only [Units.val_mul, coe_blockL, coe_blockR, Units.val_neg, Units.val_one]
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

variable {Q₁ : (ι₁ → K) → K} {Q₂ : (ι₂ → K) → K}

theorem blockL_mem_isoGroup {g : GL ι₁ K} (hg : g ∈ isoGroup Q₁) :
    blockL ι₂ g ∈ isoGroup (sumQ Q₁ Q₂) := by
  intro v
  rw [blockL_mulVec, sumQ_elim, hg]
  rfl

theorem map_blockL_statedOmega_le :
    (StatedOmega Q₁).map (blockL ι₂) ≤ StatedOmega (sumQ Q₁ Q₂) := by
  have hle : (isoGroup Q₁).map (blockL ι₂) ≤ isoGroup (sumQ Q₁ Q₂) := by
    rintro _ ⟨g, hg, rfl⟩
    exact blockL_mem_isoGroup hg
  rw [statedOmega_eq, statedOmega_eq, map_commutator]
  exact commutator_mono hle hle

end Block

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
