module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace EvenLinearSL

variable {K : Type*} [Field K] {n : ℕ}

theorem mul_sub_one_mulVec (M N : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (M * N - 1) *ᵥ x = (M - 1) *ᵥ (N *ᵥ x) + (N - 1) *ᵥ x := by
  rw [mulVec_mulVec, ← add_mulVec]
  congr 1
  noncomm_ring

theorem mulVec_eq_add_sub_one (N : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    N *ᵥ x = x + (N - 1) *ᵥ x := by
  rw [sub_mulVec, one_mulVec, add_sub_cancel]

@[expose] def IsFlagKernelMatrix (W L : Submodule K (Fin n → K))
    (M : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ w ∈ W, (M - 1) *ᵥ w = 0) ∧ (∀ v ∈ L, (M - 1) *ᵥ v ∈ W) ∧ ∀ v, (M - 1) *ᵥ v ∈ L

theorem isFlagKernelMatrix_one (W L : Submodule K (Fin n → K)) :
    IsFlagKernelMatrix W L (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨fun _ _ => ?_, fun _ _ => ?_, fun _ => ?_⟩ <;>
    simp only [sub_self, zero_mulVec, Submodule.zero_mem]

theorem isFlagKernelMatrix_mul {W L : Submodule K (Fin n → K)} (hWL : W ≤ L)
    {M N : Matrix (Fin n) (Fin n) K} (hM : IsFlagKernelMatrix W L M)
    (hN : IsFlagKernelMatrix W L N) : IsFlagKernelMatrix W L (M * N) := by
  obtain ⟨hu1, hu2, hu3⟩ := hM
  obtain ⟨hv1, hv2, hv3⟩ := hN
  refine ⟨fun w hw => ?_, fun x hx => ?_, fun x => ?_⟩
  · rw [mul_sub_one_mulVec, mulVec_eq_add_sub_one N w, hv1 w hw]
    simp only [add_zero]
    exact hu1 w hw
  · rw [mul_sub_one_mulVec]
    refine W.add_mem (hu2 _ ?_) (hv2 x hx)
    rw [mulVec_eq_add_sub_one]
    exact L.add_mem hx (hWL (hv2 x hx))
  · rw [mul_sub_one_mulVec]
    exact L.add_mem (hu3 _) (hv3 x)

theorem IsFlagKernelMatrix.cube {W L : Submodule K (Fin n → K)} {M : Matrix (Fin n) (Fin n) K}
    (hM : IsFlagKernelMatrix W L M) : (M - 1) * (M - 1) * (M - 1) = 0 := by
  obtain ⟨hu1, hu2, hu3⟩ := hM
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec, zero_mulVec]
  exact hu1 _ (hu2 _ (hu3 x))

theorem isFlagKernelMatrix_of_mul_eq_one {W L : Submodule K (Fin n → K)} (hWL : W ≤ L)
    {M M' : Matrix (Fin n) (Fin n) K} (hM : IsFlagKernelMatrix W L M) (hMM' : M' * M = 1) :
    IsFlagKernelMatrix W L M' := by
  have hN3 := hM.cube
  obtain ⟨hu1, hu2, hu3⟩ := hM
  set N := M - 1 with hN
  have hinv : M' = 1 - N + N * N := by
    have h2 : M * (1 - N + N * N) = 1 := by
      have hu : M = 1 + N := by rw [hN, add_sub_cancel]
      rw [hu]
      calc (1 + N) * (1 - N + N * N) = 1 + N * N * N := by noncomm_ring
        _ = 1 := by rw [hN3, add_zero]
    calc M' = M' * (M * (1 - N + N * N)) := by rw [h2, Matrix.mul_one]
      _ = 1 - N + N * N := by rw [← Matrix.mul_assoc, hMM', Matrix.one_mul]
  have hform : ∀ x, (M' - 1) *ᵥ x = N *ᵥ (N *ᵥ x) - N *ᵥ x := by
    intro x
    rw [hinv, show (1 : Matrix (Fin n) (Fin n) K) - N + N * N - 1 = N * N - N by abel,
      sub_mulVec, mulVec_mulVec]
  refine ⟨fun w hw => ?_, fun x hx => ?_, fun x => ?_⟩
  · rw [hform, hu1 w hw, mulVec_zero, sub_zero]
  · rw [hform, hu1 _ (hu2 x hx), zero_sub]
    exact W.neg_mem (hu2 x hx)
  · rw [hform]
    exact L.sub_mem (hWL (hu2 _ (hu3 x))) (hu3 x)

@[expose] def flagKernel (W L : Submodule K (Fin n → K)) (hWL : W ≤ L) :
    Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {u | IsFlagKernelMatrix W L (u : Matrix (Fin n) (Fin n) K)}
  mul_mem' hu hv := isFlagKernelMatrix_mul hWL hu hv
  one_mem' := isFlagKernelMatrix_one (n := n) W L
  inv_mem' {u} hu :=
    isFlagKernelMatrix_of_mul_eq_one hWL hu (congrArg Subtype.val (inv_mul_cancel u))

variable {W L : Submodule K (Fin n → K)} {hWL : W ≤ L}

theorem mem_flagKernel {u : SpecialLinearGroup (Fin n) K} :
    u ∈ flagKernel W L hWL ↔ (∀ w ∈ W, ((u : Matrix (Fin n) (Fin n) K) - 1) *ᵥ w = 0) ∧
      (∀ v ∈ L, ((u : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v ∈ W) ∧
      ∀ v, ((u : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v ∈ L :=
  Iff.rfl

theorem flagKernel_cube {u : SpecialLinearGroup (Fin n) K} (hu : u ∈ flagKernel W L hWL) :
    ((u : Matrix (Fin n) (Fin n) K) - 1) * ((u : Matrix (Fin n) (Fin n) K) - 1) *
      ((u : Matrix (Fin n) (Fin n) K) - 1) = 0 :=
  IsFlagKernelMatrix.cube hu

theorem pow_four_of_cube [CharP K 2] [NeZero n] {M : Matrix (Fin n) (Fin n) K}
    (hM : (M - 1) * (M - 1) * (M - 1) = 0) : M ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_pow_char_pow_of_commute (R := Matrix (Fin n) (Fin n) K) (p := 2) (n := 2)
    (Commute.one_right M)
  rw [one_pow, show (2 : ℕ) ^ 2 = 4 from rfl, pow_succ, pow_three', hM, Matrix.zero_mul] at h
  exact (sub_eq_zero.mp h.symm)

theorem flagKernel_pow_four [CharP K 2] [NeZero n] {u : SpecialLinearGroup (Fin n) K}
    (hu : u ∈ flagKernel W L hWL) : u ^ 4 = 1 :=
  Subtype.ext (pow_four_of_cube (flagKernel_cube hu))

theorem isPGroup_flagKernel [CharP K 2] [NeZero n] : IsPGroup 2 (flagKernel W L hWL) := by
  intro u
  refine ⟨2, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, show (2 : ℕ) ^ 2 = 4 from rfl, flagKernel_pow_four u.2]
  rfl

theorem eq_one_of_pow_four [CharP K 2] {x : K} (hx : x ^ 4 = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_pow_char_pow (R := K) (p := 2) (n := 2) x 1
  rw [one_pow, show (2 : ℕ) ^ 2 = 4 from rfl, hx, sub_self] at h
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)

variable (W L hWL)

@[expose] def flagKernelInner : flagKernel W L hWL →* MulAut (projectiveSL n K) :=
  (conjAut n K).comp (SpecialLinearGroup.toGL.comp (flagKernel W L hWL).subtype)

variable {W L hWL}

theorem flagKernelInner_apply (u : flagKernel W L hWL) :
    flagKernelInner W L hWL u = conjAut n K (SpecialLinearGroup.toGL (u : SpecialLinearGroup
      (Fin n) K)) :=
  rfl

theorem flagKernelInner_range_le_inner :
    (flagKernelInner W L hWL).range ≤ inner (projectiveSL n K) := by
  rintro _ ⟨u, rfl⟩
  exact ⟨proj n K u, (conjAut_toGL (u : SpecialLinearGroup (Fin n) K)).symm⟩

theorem flagKernelInner_injective [Finite K] [CharP K 2] (hn : 3 ≤ n) :
    Function.Injective (flagKernelInner W L hWL) := by
  have : NeZero n := ⟨by omega⟩
  rw [injective_iff_map_eq_one]
  intro u hu
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hn _).mp hu
  have hc' : GeneralLinearGroup.scalar (Fin n) c =
      SpecialLinearGroup.toGL (u : SpecialLinearGroup (Fin n) K) := hc
  have h4 : (u : SpecialLinearGroup (Fin n) K) ^ 4 = 1 := flagKernel_pow_four u.2
  have h1 : GeneralLinearGroup.scalar (Fin n) (c ^ 4) = 1 := by
    rw [map_pow, hc', ← map_pow, h4, map_one]
  have hc4 : (c : K) ^ 4 = 1 := by
    have h2 := congrArg (fun g : GL (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) h1
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, Units.val_one,
      one_apply_eq, Units.val_pow_eq_pow_val] at h2
    exact h2
  have hc1 : c = 1 := Units.ext (eq_one_of_pow_four hc4)
  rw [hc1, map_one] at hc'
  apply Subtype.ext
  apply SpecialLinearGroup.toGL_injective
  exact hc'.symm.trans (map_one _).symm

@[expose] def semilin (A : GL (Fin n) K) (φ : K ≃+* K) (v : Fin n → K) : Fin n → K :=
  (A : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (v i)

section Semilin

variable {A : GL (Fin n) K} {φ : K ≃+* K}

theorem semilin_add (v w : Fin n → K) :
    semilin A φ (v + w) = semilin A φ v + semilin A φ w := by
  simp only [semilin, Pi.add_apply, map_add]
  rw [← mulVec_add]
  rfl

theorem semilin_sub (v w : Fin n → K) :
    semilin A φ (v - w) = semilin A φ v - semilin A φ w := by
  simp only [semilin, Pi.sub_apply, map_sub]
  rw [← mulVec_sub]
  rfl

theorem semilin_smul (c : K) (v : Fin n → K) : semilin A φ (c • v) = φ c • semilin A φ v := by
  simp only [semilin, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← mulVec_smul]
  rfl

theorem semilin_zero : semilin A φ 0 = 0 := by
  simp only [semilin, Pi.zero_apply, map_zero]
  exact mulVec_zero _

theorem inv_mul_self_val (A : GL (Fin n) K) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem semilin_injective : Function.Injective (semilin A φ) := by
  intro v w h
  have h1 : (fun i => φ (v i)) = fun i => φ (w i) := by
    have := congrArg (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) h
    simpa only [semilin, mulVec_mulVec, inv_mul_self_val, one_mulVec] using this
  funext i
  exact φ.injective (congrFun h1 i)

theorem semilin_ne_zero {v : Fin n → K} (hv : v ≠ 0) : semilin A φ v ≠ 0 := fun h =>
  hv (semilin_injective (h.trans semilin_zero.symm))

theorem semilin_mulVec (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    semilin A φ (M *ᵥ v) =
      ((A : Matrix (Fin n) (Fin n) K) * M.map φ) *ᵥ fun i => φ (v i) := by
  simp only [semilin]
  rw [← mulVec_mulVec]
  congr 1
  funext i
  exact RingHom.map_mulVec (φ : K →+* K) M v i

theorem conj_mulVec_semilin (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    ((A : Matrix (Fin n) (Fin n) K) * M.map φ * ((A⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) *ᵥ semilin A φ v = semilin A φ (M *ᵥ v) := by
  rw [semilin_mulVec, semilin, mulVec_mulVec,
    Matrix.mul_assoc ((A : Matrix (Fin n) (Fin n) K) * M.map φ), inv_mul_self_val,
    Matrix.mul_one]

theorem conj_sub_one_mulVec_semilin (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    ((A : Matrix (Fin n) (Fin n) K) * M.map φ * ((A⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) - 1) *ᵥ semilin A φ v = semilin A φ ((M - 1) *ᵥ v) := by
  rw [sub_mulVec, one_mulVec, conj_mulVec_semilin, sub_mulVec, one_mulVec, semilin_sub]

theorem exists_semilin_preimage [Finite K] {S : Submodule K (Fin n → K)}
    (hS : ∀ x ∈ S, semilin A φ x ∈ S) : ∀ y ∈ S, ∃ x ∈ S, semilin A φ x = y := by
  intro y hy
  let f : S → S := fun x => ⟨semilin A φ x, hS x x.2⟩
  have hf : Function.Injective f := fun x x' h =>
    Subtype.ext (semilin_injective (congrArg Subtype.val h))
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.mp hf ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem isFlagKernelMatrix_conj [Finite K] {W L : Submodule K (Fin n → K)}
    (hTW : ∀ w ∈ W, semilin A φ w ∈ W) (hTL : ∀ v ∈ L, semilin A φ v ∈ L)
    {M : Matrix (Fin n) (Fin n) K} (hM : IsFlagKernelMatrix W L M) :
    IsFlagKernelMatrix W L ((A : Matrix (Fin n) (Fin n) K) * M.map φ *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun w hw => ?_, fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨w', hw', rfl⟩ := exists_semilin_preimage hTW w hw
    rw [conj_sub_one_mulVec_semilin, h1 w' hw', semilin_zero]
  · obtain ⟨x', hx', rfl⟩ := exists_semilin_preimage hTL x hx
    rw [conj_sub_one_mulVec_semilin]
    exact hTW _ (h2 x' hx')
  · obtain ⟨x', -, rfl⟩ := exists_semilin_preimage (A := A) (φ := φ) (S := ⊤)
      (fun _ _ => Submodule.mem_top) x Submodule.mem_top
    rw [conj_sub_one_mulVec_semilin]
    exact hTL _ (h3 x')

end Semilin

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H] {g : G}
    (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨hg h, fun hgh => ?_⟩
  let f : H → H := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (by simpa [f] using congrArg Subtype.val hxy)
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hf) ⟨_, hgh⟩
  have hxh : (x : G) = h := by
    have h1 : g * (x : G) * g⁻¹ = g * h * g⁻¹ := congrArg Subtype.val hx
    simpa using h1
  rw [← hxh]
  exact x.2

theorem conj_mem_flagKernelInner_range [Finite K] {A : GL (Fin n) K} {φ : K ≃+* K}
    (hTW : ∀ w ∈ W, semilin A φ w ∈ W) (hTL : ∀ v ∈ L, semilin A φ v ∈ L)
    {x : MulAut (projectiveSL n K)} (hx : x ∈ (flagKernelInner W L hWL).range) :
    conjAut n K A * fieldAut n K φ * x * (conjAut n K A * fieldAut n K φ)⁻¹ ∈
      (flagKernelInner W L hWL).range := by
  obtain ⟨u, rfl⟩ := hx
  set u' := CatalogueBHigherLinearAction.slConjugation n K A
    (SpecialLinearGroup.map (φ : K →+* K) (u : SpecialLinearGroup (Fin n) K)) with hu'def
  have hu' : u' ∈ flagKernel W L hWL := by
    have h := isFlagKernelMatrix_conj hTW hTL u.2
    change IsFlagKernelMatrix W L (u' : Matrix (Fin n) (Fin n) K)
    rw [hu'def, CatalogueBHigherLinearAction.slConjugation_matrix]
    exact h
  refine ⟨⟨u', hu'⟩, ?_⟩
  rw [flagKernelInner_apply, flagKernelInner_apply, conj_conjAut_fieldAut]
  congr 1
  change SpecialLinearGroup.toGL u' = _
  rw [hu'def, CatalogueBHigherLinearAction.toGL_slConjugation]
  congr 2
  exact Units.ext rfl

theorem vecMulVec_mulVec' (x a v : Fin n → K) : vecMulVec x a *ᵥ v = (a ⬝ᵥ v) • x := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem det_one_add_vecMulVec (x a : Fin n → K) : det (1 + vecMulVec x a) = 1 + a ⬝ᵥ x := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

@[expose] def rankOne (x a : Fin n → K) (h : a ⬝ᵥ x = 0) : SpecialLinearGroup (Fin n) K :=
  ⟨1 + vecMulVec x a, by rw [det_one_add_vecMulVec, h, add_zero]⟩

theorem rankOne_mulVec (x a : Fin n → K) (h : a ⬝ᵥ x = 0) (v : Fin n → K) :
    ((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      v + (a ⬝ᵥ v) • x := by
  change (1 + vecMulVec x a) *ᵥ v = _
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec']

theorem rankOne_sub_one_mulVec (x a : Fin n → K) (h : a ⬝ᵥ x = 0) (v : Fin n → K) :
    (((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v =
      (a ⬝ᵥ v) • x := by
  rw [sub_mulVec, one_mulVec, rankOne_mulVec, add_sub_cancel_left]

theorem rankOne_mem_of_mem_L {x a : Fin n → K} (hx : x ∈ L) (ha : a ∈ dotOrth L)
    (h : a ⬝ᵥ x = 0) : rankOne x a h ∈ flagKernel W L hWL := by
  refine ⟨fun w hw => ?_, fun y hy => ?_, fun y => ?_⟩
  · rw [rankOne_sub_one_mulVec, mem_dotOrth.mp ha w (hWL hw), zero_smul]
  · rw [rankOne_sub_one_mulVec, mem_dotOrth.mp ha y hy, zero_smul]
    exact W.zero_mem
  · rw [rankOne_sub_one_mulVec]
    exact L.smul_mem _ hx

theorem rankOne_mem_of_mem_W {w m : Fin n → K} (hw : w ∈ W) (hm : m ∈ dotOrth W)
    (h : m ⬝ᵥ w = 0) : rankOne w m h ∈ flagKernel W L hWL := by
  refine ⟨fun w' hw' => ?_, fun y _ => ?_, fun y => ?_⟩
  · rw [rankOne_sub_one_mulVec, mem_dotOrth.mp hm w' hw', zero_smul]
  · rw [rankOne_sub_one_mulVec]
    exact W.smul_mem _ hw
  · rw [rankOne_sub_one_mulVec]
    exact hWL (W.smul_mem _ hw)

theorem exists_dotOrth_pair (hL : L ≠ ⊤) : ∃ a ∈ dotOrth L, ∃ v₀ : Fin n → K, a ⬝ᵥ v₀ = 1 := by
  classical
  have hne : dotOrth L ≠ ⊥ := by
    intro h
    apply hL
    rw [← dotOrth_dotOrth L, h, eq_top_iff]
    intro v _
    rw [mem_dotOrth]
    intro w hw
    rw [(Submodule.mem_bot K).mp hw, dotProduct_zero]
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ha0 (funext hall)
  refine ⟨a, ha, Pi.single j (a j)⁻¹, ?_⟩
  rw [dotProduct_single, mul_inv_cancel₀ hj]

theorem mem_of_forall_dotOrth {y : Fin n → K} (hy : ∀ m ∈ dotOrth W, m ⬝ᵥ y = 0) : y ∈ W := by
  rw [← dotOrth_dotOrth W, mem_dotOrth]
  intro m hm
  rw [dotProduct_comm]
  exact hy m hm

theorem conj_eq_of_mem_centralizer [Finite K] [CharP K 2] (hn : 3 ≤ n) {A : GL (Fin n) K}
    {φ : K ≃+* K} (hα : conjAut n K A * fieldAut n K φ ∈
      centralizer ((flagKernelInner W L hWL).range : Set (MulAut (projectiveSL n K))))
    (u : flagKernel W L hWL) :
    A * GeneralLinearGroup.map (φ : K →+* K) (SpecialLinearGroup.toGL
      (u : SpecialLinearGroup (Fin n) K)) * A⁻¹ =
        SpecialLinearGroup.toGL (u : SpecialLinearGroup (Fin n) K) := by
  have : NeZero n := ⟨by omega⟩
  set g := SpecialLinearGroup.toGL (u : SpecialLinearGroup (Fin n) K) with hg
  have h1 : conjAut n K (A * GeneralLinearGroup.map (φ : K →+* K) g * A⁻¹) = conjAut n K g := by
    rw [← conj_conjAut_fieldAut]
    have hc := mem_centralizer_iff.mp hα (flagKernelInner W L hWL u) ⟨u, rfl⟩
    rw [flagKernelInner_apply] at hc
    rw [← hg] at hc
    rw [← hc]
    group
  obtain ⟨c, hc⟩ := (conjAut_eq_conjAut_iff hn _ _).mp h1
  have hg4 : g ^ 4 = 1 := by rw [hg, ← map_pow, flagKernel_pow_four u.2, map_one]
  have hX4 : (A * GeneralLinearGroup.map (φ : K →+* K) g * A⁻¹) ^ 4 = 1 := by
    rw [conj_pow, ← map_pow, hg4, map_one, mul_one, mul_inv_cancel]
  have hs4 : GeneralLinearGroup.scalar (Fin n) (c ^ 4) = 1 := by
    have hcomm : Commute g (GeneralLinearGroup.scalar (Fin n) c) :=
      (GeneralLinearGroup.scalar_commute c g).symm
    rw [hc, hcomm.mul_pow, hg4, one_mul, ← map_pow] at hX4
    exact hX4
  have hc4 : (c : K) ^ 4 = 1 := by
    have h2 := congrArg (fun g : GL (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) hs4
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, Units.val_one,
      one_apply_eq, Units.val_pow_eq_pow_val] at h2
    exact h2
  have hc1 : c = 1 := Units.ext (eq_one_of_pow_four hc4)
  rw [hc, hc1, map_one, mul_one]

theorem mem_map_center_of_mem_centralizer [Finite K] [CharP K 2] (hn : 3 ≤ n) (hW : W ≠ ⊥)
    (hL : L ≠ ⊤) {α : MulAut (projectiveSL n K)} (hαE : α ∈ semilinearAutGroup n K)
    (hα : α ∈ centralizer ((flagKernelInner W L hWL).range : Set (MulAut (projectiveSL n K)))) :
    α ∈ (center (flagKernel W L hWL)).map (flagKernelInner W L hWL) := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨A, φ, rfl⟩ := mem_semilinearAutGroup_iff.mp hαE
  have hmat : ∀ u ∈ flagKernel W L hWL, (A : Matrix (Fin n) (Fin n) K) *
      (u : Matrix (Fin n) (Fin n) K).map φ = (u : Matrix (Fin n) (Fin n) K) * A := by
    intro u hu
    have h' : (A : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K).map φ *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (u : Matrix (Fin n) (Fin n) K) :=
      congrArg Units.val (conj_eq_of_mem_centralizer hn hα ⟨u, hu⟩)
    calc (A : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K).map φ
        = (A : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K).map φ *
          (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) := by
          rw [inv_mul_self_val, Matrix.mul_one]
      _ = (A : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K).map φ *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A := by
          simp only [Matrix.mul_assoc]
      _ = (u : Matrix (Fin n) (Fin n) K) * A := by rw [h']
  have hT : ∀ u ∈ flagKernel W L hWL, ∀ v, semilin A φ ((u : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (u : Matrix (Fin n) (Fin n) K) *ᵥ semilin A φ v := by
    intro u hu v
    rw [semilin_mulVec, hmat u hu, semilin, mulVec_mulVec]
  have hrank : ∀ (x a : Fin n → K) (h : a ⬝ᵥ x = 0), rankOne x a h ∈ flagKernel W L hWL →
      ∀ v, φ (a ⬝ᵥ v) • semilin A φ x = (a ⬝ᵥ semilin A φ v) • x := by
    intro x a h hmem v
    have h1 := hT _ hmem v
    rw [rankOne_mulVec, rankOne_mulVec, semilin_add, semilin_smul] at h1
    exact add_left_cancel h1
  obtain ⟨a₀, ha₀, v₀, hav₀⟩ := exists_dotOrth_pair hL
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  set c := a₀ ⬝ᵥ semilin A φ v₀ with hcdef
  have hTL : ∀ x ∈ L, semilin A φ x = c • x := by
    intro x hx
    have h := hrank x a₀ (mem_dotOrth.mp ha₀ x hx) (rankOne_mem_of_mem_L hx ha₀ _) v₀
    rwa [hav₀, map_one, one_smul] at h
  have hc0 : c ≠ 0 := by
    intro hc
    apply semilin_ne_zero (A := A) (φ := φ) hw₀0
    rw [hTL w₀ (hWL hw₀), hc, zero_smul]
  have hφ : φ = 1 := by
    apply RingEquiv.ext
    intro t
    have hta : t • a₀ ∈ dotOrth L := (dotOrth L).smul_mem t ha₀
    have hdot : (t • a₀) ⬝ᵥ w₀ = 0 := mem_dotOrth.mp hta w₀ (hWL hw₀)
    have h := hrank w₀ (t • a₀) hdot (rankOne_mem_of_mem_L (hWL hw₀) hta hdot) v₀
    rw [smul_dotProduct, smul_dotProduct, hav₀, smul_eq_mul, smul_eq_mul, mul_one,
      hTL w₀ (hWL hw₀), ← hcdef, smul_smul] at h
    have h2 : φ t * c = t * c := smul_left_injective K hw₀0 h
    exact mul_right_cancel₀ hc0 h2
  subst hφ
  have hsemi : ∀ v, semilin A 1 v = (A : Matrix (Fin n) (Fin n) K) *ᵥ v := fun v => rfl
  have hAL : ∀ x ∈ L, (A : Matrix (Fin n) (Fin n) K) *ᵥ x = c • x := fun x hx =>
    (hsemi x).symm.trans (hTL x hx)
  have hAW : ∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ v - c • v ∈ W := by
    intro v
    apply mem_of_forall_dotOrth
    intro m hm
    have hdot : m ⬝ᵥ w₀ = 0 := mem_dotOrth.mp hm w₀ hw₀
    have h := hrank w₀ m hdot (rankOne_mem_of_mem_W hw₀ hm hdot) v
    rw [hTL w₀ (hWL hw₀), smul_smul] at h
    have h2 : (1 : K ≃+* K) (m ⬝ᵥ v) * c = m ⬝ᵥ semilin A 1 v :=
      smul_left_injective K hw₀0 h
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hsemi, ← h2]
    change m ⬝ᵥ v * c - c * (m ⬝ᵥ v) = 0
    ring
  set M : Matrix (Fin n) (Fin n) K := c⁻¹ • (A : Matrix (Fin n) (Fin n) K) with hM
  have hMv : ∀ y, (M - 1) *ᵥ y = c⁻¹ • ((A : Matrix (Fin n) (Fin n) K) *ᵥ y - c • y) := by
    intro y
    rw [sub_mulVec, one_mulVec, hM, smul_mulVec, smul_sub, smul_smul, inv_mul_cancel₀ hc0,
      one_smul]
  have hMk : IsFlagKernelMatrix W L M := by
    refine ⟨fun w hw => ?_, fun x hx => ?_, fun y => ?_⟩
    · rw [hMv, hAL w (hWL hw), sub_self, smul_zero]
    · rw [hMv, hAL x hx, sub_self, smul_zero]
      exact W.zero_mem
    · rw [hMv]
      exact hWL (W.smul_mem _ (hAW y))
  have hdet : M.det = 1 := by
    have h4 := pow_four_of_cube hMk.cube
    have h5 : M.det ^ 4 = 1 := by rw [← det_pow, h4, det_one]
    exact eq_one_of_pow_four h5
  set v : SpecialLinearGroup (Fin n) K := ⟨M, hdet⟩ with hvdef
  have hvU : v ∈ flagKernel W L hWL := hMk
  have hAv : A = GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0) *
      SpecialLinearGroup.toGL v := by
    apply Units.ext
    change (A : Matrix (Fin n) (Fin n) K) =
      Matrix.scalar (Fin n) c * (c⁻¹ • (A : Matrix (Fin n) (Fin n) K))
    rw [Matrix.scalar_apply, ← smul_eq_diagonal_mul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hαv : conjAut n K A * fieldAut n K 1 = flagKernelInner W L hWL ⟨v, hvU⟩ := by
    rw [map_one, mul_one, flagKernelInner_apply, hAv, map_mul, conjAut_scalar, one_mul]
  refine ⟨⟨v, hvU⟩, Subgroup.mem_center_iff.mpr fun u => ?_, hαv.symm⟩
  apply flagKernelInner_injective hn
  rw [map_mul, map_mul, ← hαv]
  exact mem_centralizer_iff.mp hα _ ⟨u, rfl⟩

end EvenLinearSL

open EvenLinearSL

theorem even_linear_flag_kernel_projective_centralizer {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    {K : Type*} [Field K] (hK : Nat.card K = 2 ^ f) {W L : Submodule K (Fin n → K)}
    (hW : W ≠ ⊥) (hWL : W ≤ L) (hL : L ≠ ⊤) :
    (∀ u : SpecialLinearGroup (Fin n) K, u ∈ flagKernel W L hWL ↔
      (∀ w ∈ W, ((u : Matrix (Fin n) (Fin n) K) - 1) *ᵥ w = 0) ∧
      (∀ v ∈ L, ((u : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v ∈ W) ∧
      ∀ v, ((u : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v ∈ L) ∧
    Finite (flagKernel W L hWL) ∧ IsPGroup 2 (flagKernel W L hWL) ∧
    (flagKernelInner W L hWL).range ≤ inner (projectiveSL n K) ∧
    (∀ u : flagKernel W L hWL,
      flagKernelInner W L hWL u = conjAut n K (SpecialLinearGroup.toGL (u :
        SpecialLinearGroup (Fin n) K))) ∧
    Function.Injective (flagKernelInner W L hWL) ∧
    (∀ (A : GL (Fin n) K) (φ : K ≃+* K),
      (∀ w ∈ W, (A : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (w i)) ∈ W) →
      (∀ v ∈ L, (A : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (v i)) ∈ L) →
      conjAut n K A * fieldAut n K φ ∈ semilinearAutGroup n K ∧
      conjAut n K A * fieldAut n K φ ∈
        normalizer ((flagKernelInner W L hWL).range : Set (MulAut (projectiveSL n K)))) ∧
    semilinearAutGroup n K ⊓
        centralizer ((flagKernelInner W L hWL).range : Set (MulAut (projectiveSL n K))) =
      (center (flagKernel W L hWL)).map (flagKernelInner W L hWL) ∧
    IsPGroup 2 ↥(semilinearAutGroup n K ⊓
        centralizer ((flagKernelInner W L hWL).range : Set (MulAut (projectiveSL n K)))) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  have hfin : Finite (flagKernelInner W L hWL).range :=
    Finite.of_surjective _ (flagKernelInner W L hWL).rangeRestrict_surjective
  have hcent : semilinearAutGroup n K ⊓
      centralizer ((flagKernelInner W L hWL).range : Set (MulAut (projectiveSL n K))) =
        (center (flagKernel W L hWL)).map (flagKernelInner W L hWL) := by
    apply le_antisymm
    · intro α hα
      exact mem_map_center_of_mem_centralizer hn hW hL (mem_inf.mp hα).1 (mem_inf.mp hα).2
    · rintro _ ⟨z, hz, rfl⟩
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [flagKernelInner_apply]
        exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)
      · rw [mem_centralizer_iff]
        rintro _ ⟨u, rfl⟩
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz u)]
  refine ⟨fun u => Iff.rfl, inferInstance, isPGroup_flagKernel, flagKernelInner_range_le_inner,
    flagKernelInner_apply, flagKernelInner_injective hn, fun A φ hTW hTL =>
      ⟨mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
        (fieldAut_mem_semilinearAutGroup φ),
      mem_normalizer_of_conj_mem fun x hx => conj_mem_flagKernelInner_range hTW hTL hx⟩,
    hcent, ?_⟩
  rw [hcent]
  exact isPGroup_flagKernel.to_subgroup _ |>.map _

end CFSG.ComponentClassification.UnbalancedCatalog
