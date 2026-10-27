module
public import CFSG.FeitThompson.Representations.CoprimeAbelianWeightDecomposition
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Polynomial

section Block

variable {k V V' ι : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup V']
  [Module k V'] {W : ι → Submodule k V}

def blockSubmodule (W : ι → Submodule k V) (σ : ι → ι) : Submodule k (Module.End k V) where
  carrier := {f | ∀ i, ∀ v ∈ W i, f v ∈ W (σ i)}
  add_mem' hf hg i v hv := by simpa using Submodule.add_mem _ (hf i v hv) (hg i v hv)
  zero_mem' i v hv := by simp
  smul_mem' c f hf i v hv := by simpa using Submodule.smul_mem _ c (hf i v hv)

@[simp]
lemma mem_blockSubmodule_iff {σ : ι → ι} {f : Module.End k V} :
    f ∈ blockSubmodule W σ ↔ ∀ i, ∀ v ∈ W i, f v ∈ W (σ i) := Iff.rfl

variable [DecidableEq ι]

lemma eq_of_eqOn_isInternal (h : DirectSum.IsInternal W) {F G : V →ₗ[k] V'}
    (hFG : ∀ i, ∀ v ∈ W i, F v = G v) : F = G := by
  rw [← sub_eq_zero, ← LinearMap.ker_eq_top, eq_top_iff, ← h.submodule_iSup_eq_top]
  exact iSup_le fun i x hx ↦ by simpa [sub_eq_zero] using hFG i x hx

noncomputable def internalProjection (h : DirectSum.IsInternal W) (i : ι) : V →ₗ[k] W i :=
  DirectSum.component k ι (fun i ↦ (W i : Type _)) i ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) h).symm.toLinearMap

lemma internalProjection_apply (h : DirectSum.IsInternal W) (i : ι) (v : V) :
    internalProjection h i v = (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) h).symm v i :=
  (DirectSum.apply_eq_component k _ i).symm

@[simp]
lemma internalProjection_coe_of_mem (h : DirectSum.IsInternal W) {i : ι} {v : V} (hv : v ∈ W i) :
    (internalProjection h i v : V) = v := by
  rw [internalProjection_apply, h.ofBijective_coeLinearMap_of_mem hv]

@[simp]
lemma internalProjection_of_mem_ne (h : DirectSum.IsInternal W) {i j : ι} (hij : i ≠ j) {v : V}
    (hv : v ∈ W i) : internalProjection h j v = 0 := by
  rw [internalProjection_apply, h.ofBijective_coeLinearMap_of_mem_ne hij hv]

variable [Fintype ι]

private lemma sum_blockSubmodule_apply (h : DirectSum.IsInternal W) {σ : ι → ι}
    (g : ∀ i, W i →ₗ[k] W (σ i)) {i : ι} {v : V} (hv : v ∈ W i) :
    (∑ j, (W (σ j)).subtype ∘ₗ g j ∘ₗ internalProjection h j) v
      = (g i (internalProjection h i v) : V) := by
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype]
  refine Finset.sum_eq_single i (fun j _ hj ↦ ?_) fun hi ↦ absurd (Finset.mem_univ i) hi
  rw [internalProjection_of_mem_ne h (Ne.symm hj) hv, map_zero, Submodule.coe_zero]

noncomputable def blockRestrictEquiv (h : DirectSum.IsInternal W) (σ : ι → ι) :
    blockSubmodule W σ ≃ₗ[k] ∀ i, W i →ₗ[k] W (σ i) where
  toFun f i := LinearMap.restrict (f : Module.End k V) (f.2 i)
  map_add' f g := by ext i v; rfl
  map_smul' c f := by ext i v; rfl
  invFun g := ⟨∑ i, (W (σ i)).subtype ∘ₗ g i ∘ₗ internalProjection h i, fun i v hv ↦ by
    rw [sum_blockSubmodule_apply h g hv]; exact (g i _).2⟩
  left_inv f := by
    refine Subtype.ext (eq_of_eqOn_isInternal h fun i v hv ↦ ?_)
    rw [sum_blockSubmodule_apply h _ hv, LinearMap.coe_restrict_apply,
      internalProjection_coe_of_mem h hv]
  right_inv g := by
    ext i v
    rw [LinearMap.coe_restrict_apply, sum_blockSubmodule_apply h g v.2,
      show internalProjection h i (v : V) = v from
        Subtype.ext (internalProjection_coe_of_mem h v.2)]

lemma finrank_blockSubmodule [FiniteDimensional k V] (h : DirectSum.IsInternal W) (σ : ι → ι) :
    finrank k (blockSubmodule W σ) = ∑ i, finrank k (W i) * finrank k (W (σ i)) := by
  rw [(blockRestrictEquiv h σ).finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun i _ ↦ Module.finrank_linearMap k k _ _

lemma finrank_eq_sum_finrank_of_isInternal [FiniteDimensional k V] (h : DirectSum.IsInternal W) :
    finrank k V = ∑ i, finrank k (W i) := by
  rw [← Module.finrank_directSum (R := k) fun i ↦ (W i : Type _)]
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) h).finrank_eq.symm

end Block

section Cyclic

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {r : ℕ} {ε : k}

def cyclicEigenspace (ε : k) {r : ℕ} (T : V ≃ₗ[k] V) (i : ZMod r) : Submodule k V :=
  Module.End.eigenspace (T : Module.End k V) (ε ^ i.val)

@[simp]
lemma mem_cyclicEigenspace_iff {T : V ≃ₗ[k] V} {i : ZMod r} {v : V} :
    v ∈ cyclicEigenspace ε T i ↔ T v = ε ^ i.val • v := Module.End.mem_eigenspace_iff

lemma cyclicEigenspace_eq_eigenspace (T : V ≃ₗ[k] V) (i : ZMod r) :
    cyclicEigenspace ε T i = Module.End.eigenspace (T : Module.End k V) (ε ^ i.val) := (rfl)

def conjEigenspace (ε : k) {r : ℕ} (T : V ≃ₗ[k] V) (m : ZMod r) :
    Submodule k (Module.End k V) :=
  Module.End.eigenspace (T.conj : Module.End k (Module.End k V)) (ε ^ m.val)

lemma mem_conjEigenspace_iff {T : V ≃ₗ[k] V} {m : ZMod r} {f : Module.End k V} :
    f ∈ conjEigenspace ε T m ↔ T.conj f = ε ^ m.val • f := Module.End.mem_eigenspace_iff

lemma mem_conjEigenspace_iff' {T : V ≃ₗ[k] V} {m : ZMod r} {f : Module.End k V} :
    f ∈ conjEigenspace ε T m ↔ ∀ v : V, T (f (T.symm v)) = ε ^ m.val • f v := by
  rw [mem_conjEigenspace_iff, LinearMap.ext_iff]
  simp [LinearEquiv.conj_apply]

lemma coe_pow_toLinearMap (T : V ≃ₗ[k] V) (n : ℕ) :
    ((T ^ n : V ≃ₗ[k] V) : Module.End k V) = (T : Module.End k V) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

private lemma pow_apply_of_eigen {f : Module.End k V} {μ : k} {v : V} (hv : f v = μ • v) (n : ℕ) :
    (f ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

lemma isSemisimple_of_pow_eq_one (hr : (r : k) ≠ 0) {T : V ≃ₗ[k] V} (hT : T ^ r = 1) :
    Module.End.IsSemisimple (T : Module.End k V) := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C (1 : k) hr one_ne_zero).squarefree ?_
  have h : ((T : Module.End k V)) ^ r = 1 := by rw [← coe_pow_toLinearMap, hT]; rfl
  simp [h]

variable [NeZero r]

lemma pow_val_add (hε : ε ^ r = 1) (i j : ZMod r) :
    ε ^ (i + j).val = ε ^ i.val * ε ^ j.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hε, pow_add]

lemma injective_pow_val (hε : IsPrimitiveRoot ε r) :
    Function.Injective fun i : ZMod r ↦ ε ^ i.val := fun i j h ↦
  ZMod.val_injective r (hε.pow_inj i.val_lt j.val_lt h)

lemma iSupIndep_cyclicEigenspace (hε : IsPrimitiveRoot ε r) (T : V ≃ₗ[k] V) :
    iSupIndep (cyclicEigenspace ε (r := r) T) :=
  (Module.End.eigenspaces_iSupIndep (T : Module.End k V)).comp (injective_pow_val hε)

lemma iSup_cyclicEigenspace_eq_top [IsAlgClosed k] [FiniteDimensional k V] (hr : (r : k) ≠ 0)
    (hε : IsPrimitiveRoot ε r) {T : V ≃ₗ[k] V} (hT : T ^ r = 1) :
    ⨆ i : ZMod r, cyclicEigenspace ε T i = ⊤ := by
  refine top_unique ?_
  rw [← (isSemisimple_of_pow_eq_one hr hT).iSup_eigenspace_eq_top]
  refine iSup_le fun μ ↦ ?_
  rcases eq_or_ne (Module.End.eigenspace (T : Module.End k V) μ) ⊥ with h | h
  · rw [h]; exact bot_le
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [Module.End.mem_eigenspace_iff] at hv
  have hone : ((T : Module.End k V) ^ r) v = v := by rw [← coe_pow_toLinearMap, hT]; rfl
  have hμ : μ ^ r = 1 := by
    have h2 : (μ ^ r - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← pow_apply_of_eigen hv r, hone, sub_self]
    have h3 := (smul_eq_zero.1 h2).resolve_right hv0
    linear_combination h3
  obtain ⟨i, hi, hiμ⟩ := hε.eq_pow_of_pow_eq_one hμ
  exact le_iSup_of_le (i : ZMod r)
    (by rw [cyclicEigenspace_eq_eigenspace, ZMod.val_natCast_of_lt hi, hiμ])

def cyclicRepresentation {T : V ≃ₗ[k] V} (hT : T ^ r = 1) :
    Representation k (Multiplicative (ZMod r)) V where
  toFun a := ((T ^ (Multiplicative.toAdd a).val : V ≃ₗ[k] V) : Module.End k V)
  map_one' := by
    change ((T ^ (0 : ZMod r).val : V ≃ₗ[k] V) : Module.End k V) = 1
    simp; rfl
  map_mul' a b := by
    have h : (T ^ ((Multiplicative.toAdd a + Multiplicative.toAdd b).val) : V ≃ₗ[k] V)
        = T ^ (Multiplicative.toAdd a).val * T ^ (Multiplicative.toAdd b).val := by
      rw [ZMod.val_add, ← pow_eq_pow_mod _ hT, pow_add]
    change ((T ^ ((Multiplicative.toAdd a + Multiplicative.toAdd b).val) : V ≃ₗ[k] V)
      : Module.End k V) = _
    rw [h, LinearEquiv.coe_toLinearMap_mul]

lemma cyclicRepresentation_apply {T : V ≃ₗ[k] V} (hT : T ^ r = 1) (a : Multiplicative (ZMod r))
    (v : V) :
    cyclicRepresentation hT a v = ((T : Module.End k V) ^ (Multiplicative.toAdd a).val) v := by
  change ((T ^ (Multiplicative.toAdd a).val : V ≃ₗ[k] V) : Module.End k V) v = _
  rw [coe_pow_toLinearMap]

def primitiveRootUnit (hε : IsPrimitiveRoot ε r) : kˣ :=
  Units.mk0 ε (hε.ne_zero (NeZero.ne r))

@[simp]
lemma coe_primitiveRootUnit (hε : IsPrimitiveRoot ε r) : (primitiveRootUnit hε : k) = ε := (rfl)

lemma primitiveRootUnit_pow_eq_one (hε : IsPrimitiveRoot ε r) : primitiveRootUnit hε ^ r = 1 :=
  Units.ext (by push_cast [coe_primitiveRootUnit]; simpa using hε.pow_eq_one)

def cyclicCharacter (hε : IsPrimitiveRoot ε r) (i : ZMod r) : Multiplicative (ZMod r) →* kˣ where
  toFun a := primitiveRootUnit hε ^ (i * Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have h : (i * (Multiplicative.toAdd a + Multiplicative.toAdd b)).val
        = (i * Multiplicative.toAdd a + i * Multiplicative.toAdd b).val := by rw [mul_add]
    change primitiveRootUnit hε ^ (i * (Multiplicative.toAdd a + Multiplicative.toAdd b)).val = _
    rw [h, ZMod.val_add, ← pow_eq_pow_mod _ (primitiveRootUnit_pow_eq_one hε), pow_add]

@[simp]
lemma coe_cyclicCharacter (hε : IsPrimitiveRoot ε r) (i : ZMod r) (a : Multiplicative (ZMod r)) :
    ((cyclicCharacter hε i a : kˣ) : k) = ε ^ (i * Multiplicative.toAdd a).val := by
  change ((primitiveRootUnit hε ^ (i * Multiplicative.toAdd a).val : kˣ) : k) = _
  push_cast
  rw [coe_primitiveRootUnit]

lemma characterSpace_cyclicCharacter (hr2 : 2 ≤ r) (hε : IsPrimitiveRoot ε r) {T : V ≃ₗ[k] V}
    (hT : T ^ r = 1) (i : ZMod r) :
    Representation.characterSpace (cyclicRepresentation hT) (cyclicCharacter hε i)
      = cyclicEigenspace ε T i := by
  have h1 : (1 : ZMod r).val = 1 := haveI : Fact (1 < r) := ⟨by omega⟩; ZMod.val_one r
  have hεr : ε ^ r = 1 := hε.pow_eq_one
  ext v
  rw [Representation.mem_characterSpace_iff, mem_cyclicEigenspace_iff]
  refine ⟨fun h ↦ ?_, fun h a ↦ ?_⟩
  · have h2 := h (Multiplicative.ofAdd (1 : ZMod r))
    rw [cyclicRepresentation_apply, coe_cyclicCharacter] at h2
    simpa [h1] using h2
  · rw [cyclicRepresentation_apply, coe_cyclicCharacter, pow_apply_of_eigen h, ← pow_mul,
      ZMod.val_mul, ← pow_eq_pow_mod _ hεr]

theorem isInternal_cyclicEigenspace [IsAlgClosed k] [FiniteDimensional k V] (hr : (r : k) ≠ 0)
    (hε : IsPrimitiveRoot ε r) {T : V ≃ₗ[k] V} (hT : T ^ r = 1) :
    DirectSum.IsInternal (cyclicEigenspace ε (r := r) T) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_cyclicEigenspace hε T, iSup_cyclicEigenspace_eq_top hr hε hT⟩

theorem finrank_eq_sum_finrank_cyclicEigenspace [IsAlgClosed k] [FiniteDimensional k V]
    (hr : (r : k) ≠ 0) (hε : IsPrimitiveRoot ε r) {T : V ≃ₗ[k] V} (hT : T ^ r = 1) :
    finrank k V = ∑ i : ZMod r, finrank k (cyclicEigenspace ε T i) :=
  finrank_eq_sum_finrank_of_isInternal (isInternal_cyclicEigenspace hr hε hT)

lemma conjEigenspace_eq_blockSubmodule [IsAlgClosed k] [FiniteDimensional k V] (hr : (r : k) ≠ 0)
    (hε : IsPrimitiveRoot ε r) {T : V ≃ₗ[k] V} (hT : T ^ r = 1) (m : ZMod r) :
    conjEigenspace ε T m
      = blockSubmodule (cyclicEigenspace ε (r := r) T) (fun i ↦ i + m) := by
  have hεr : ε ^ r = 1 := hε.pow_eq_one
  have hpow : ∀ i : ZMod r, ε ^ i.val ≠ 0 :=
    fun i ↦ pow_ne_zero _ (hε.ne_zero (NeZero.ne r))
  have hTinv : ∀ (i : ZMod r) (v : V), v ∈ cyclicEigenspace ε (r := r) T i →
      T.symm v = (ε ^ i.val)⁻¹ • v := by
    intro i v hv
    rw [mem_cyclicEigenspace_iff] at hv
    apply T.injective
    rw [T.apply_symm_apply, map_smul, hv, smul_smul, inv_mul_cancel₀ (hpow i), one_smul]
  refine le_antisymm (fun f hf i v hv ↦ ?_) fun f hf ↦ ?_
  · rw [mem_conjEigenspace_iff'] at hf
    have h1 := hf v
    rw [hTinv i v hv, map_smul, map_smul] at h1
    rw [mem_cyclicEigenspace_iff, pow_val_add hεr, ← smul_smul, ← h1, smul_smul,
      mul_inv_cancel₀ (hpow i), one_smul]
  · rw [mem_conjEigenspace_iff']
    have key : (T : V →ₗ[k] V) ∘ₗ (f : Module.End k V) ∘ₗ (T.symm : V →ₗ[k] V)
        = (ε ^ m.val) • (f : Module.End k V) := by
      refine eq_of_eqOn_isInternal (isInternal_cyclicEigenspace hr hε hT) fun i v hv ↦ ?_
      have hfv : T (f v) = ε ^ (i + m).val • f v := by
        have := hf i v hv
        rwa [mem_cyclicEigenspace_iff] at this
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.smul_apply]
      rw [hTinv i v hv, map_smul, map_smul, hfv, smul_smul, pow_val_add hεr, ← mul_assoc,
        inv_mul_cancel₀ (hpow i), one_mul]
    exact fun v ↦ LinearMap.congr_fun key v

theorem finrank_conjEigenspace [IsAlgClosed k] [FiniteDimensional k V] (hr : (r : k) ≠ 0)
    (hε : IsPrimitiveRoot ε r) {T : V ≃ₗ[k] V} (hT : T ^ r = 1) (m : ZMod r) :
    finrank k (conjEigenspace ε T m)
      = ∑ i : ZMod r, finrank k (cyclicEigenspace ε T i)
          * finrank k (cyclicEigenspace ε T (i + m)) := by
  rw [conjEigenspace_eq_blockSubmodule hr hε hT m,
    finrank_blockSubmodule (isInternal_cyclicEigenspace hr hε hT)]

theorem sum_finrank_conjEigenspace [IsAlgClosed k] [FiniteDimensional k V] (hr : (r : k) ≠ 0)
    (hε : IsPrimitiveRoot ε r) {T : V ≃ₗ[k] V} (hT : T ^ r = 1) :
    ∑ m : ZMod r, finrank k (conjEigenspace ε T m) = finrank k V ^ 2 := by
  rw [Finset.sum_congr rfl fun m _ ↦ finrank_conjEigenspace hr hε hT m, Finset.sum_comm,
    finrank_eq_sum_finrank_cyclicEigenspace hr hε hT, sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    Fintype.sum_equiv (Equiv.addLeft i) _ _ fun m ↦ by rw [Equiv.coe_addLeft]

theorem two_mul_finrank_conjEigenspace_sub [IsAlgClosed k] [FiniteDimensional k V]
    (hr : (r : k) ≠ 0) (hε : IsPrimitiveRoot ε r) {T : V ≃ₗ[k] V} (hT : T ^ r = 1) (m : ZMod r) :
    2 * ((finrank k (conjEigenspace ε T (0 : ZMod r)) : ℤ) - finrank k (conjEigenspace ε T m))
      = ∑ i : ZMod r, ((finrank k (cyclicEigenspace ε T i) : ℤ)
          - finrank k (cyclicEigenspace ε T (i + m))) ^ 2 := by
  set n : ZMod r → ℤ := fun i ↦ (finrank k (cyclicEigenspace ε T i) : ℤ) with hndef
  have hc0 : (finrank k (conjEigenspace ε T (0 : ZMod r)) : ℤ) = ∑ i : ZMod r, n i * n i := by
    rw [finrank_conjEigenspace hr hε hT 0]
    push_cast
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hndef, add_zero]
  have hcm : (finrank k (conjEigenspace ε T m) : ℤ) = ∑ i : ZMod r, n i * n (i + m) := by
    rw [finrank_conjEigenspace hr hε hT m]
    push_cast
    rfl
  have hshift : ∑ i : ZMod r, n (i + m) * n (i + m) = ∑ i : ZMod r, n i * n i :=
    Fintype.sum_equiv (Equiv.addRight m) _ _ fun i ↦ by rw [Equiv.coe_addRight]
  rw [hc0, hcm, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) ↦
    show (n i - n (i + m)) ^ 2
      = n i * n i - 2 * (n i * n (i + m)) + n (i + m) * n (i + m) by ring,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, hshift, ← Finset.mul_sum]
  ring

end Cyclic

end CFSG.FeitThompson
