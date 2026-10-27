module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesReindex
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldUnipotent
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section TwoByTwo

variable {k : Type*} [Field k] [CharP k 2]

theorem exists_swap_vector (A : Matrix (Fin 2) (Fin 2) k) (hA2 : A * A = 1) (hA1 : A ≠ 1) :
    ∃ p : Fin 2 → k, A.mulVec p ≠ p ∧
      ∀ α β : k, α • p + β • A.mulVec p = 0 → α = 0 ∧ β = 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ (1 : Matrix (Fin 2) (Fin 2) k) i j := by
    by_contra hc
    push Not at hc
    exact hA1 (Matrix.ext hc)
  set p : Fin 2 → k := Pi.single j 1 with hp
  have hAp : A.mulVec p ≠ p := by
    intro h
    have := congrFun h i
    simp only [hp, Matrix.mulVec_single_one, Pi.single_apply] at this
    apply hij
    rw [Matrix.one_apply]
    simpa [Matrix.col_apply] using this
  refine ⟨p, hAp, fun α β h => ?_⟩
  have hp0 : p ≠ 0 := by
    intro h0
    have := congrFun h0 j
    simp [hp] at this
  have hAAp : A.mulVec (A.mulVec p) = p := by
    rw [Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec]
  have h2 : α • A.mulVec p + β • p = 0 := by
    have := congrArg A.mulVec h
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hAAp] at this
    rw [Matrix.mulVec_zero] at this
    exact this
  have h3 : (α ^ 2 - β ^ 2) • p = 0 := by
    have e1 : α • (α • p + β • A.mulVec p) = 0 := by rw [h, smul_zero]
    have e2 : β • (α • A.mulVec p + β • p) = 0 := by rw [h2, smul_zero]
    have : (α ^ 2 - β ^ 2) • p = α • (α • p + β • A.mulVec p) - β • (α • A.mulVec p + β • p) := by
      simp only [smul_add, smul_smul, sub_smul]
      module
    rw [this, e1, e2, sub_zero]
  have h4 : α ^ 2 - β ^ 2 = 0 := by
    rcases smul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hp0
  have h5 : α = β := by
    have h6 : (α - β) ^ 2 = 0 := by
      have := sub_pow_char α β (p := 2)
      simpa [this] using h4
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h6)
  subst h5
  have h7 : α • (p + A.mulVec p) = 0 := by rw [smul_add]; exact h
  rcases smul_eq_zero.mp h7 with h8 | h8
  · exact ⟨h8, h8⟩
  · exfalso
    apply hAp
    have := neg_eq_of_add_eq_zero_right h8
    rw [neg_eq_self_of_charTwo k] at this
    exact this.symm

end TwoByTwo

section KerDim

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharP k 2] [Fintype ι] [DecidableEq ι] in
@[expose] def tensorVec (v : Fin 2 → k) : ((ι → Fin 2) → k) →ₗ[k] ((Option ι → Fin 2) → k) where
  toFun m := fun x => v (x none) * m (fun i => x (some i))
  map_add' m m' := by funext x; simp [mul_add]
  map_smul' c m := by funext x; simp [mul_left_comm]

omit [CharP k 2] [Fintype ι] [DecidableEq ι] in
theorem tensorVec_apply (v : Fin 2 → k) (m : (ι → Fin 2) → k) (a : Fin 2) (y : ι → Fin 2) :
    tensorVec v m (optCons a y) = v a * m y := rfl

omit [CharP k 2] [Fintype ι] [DecidableEq ι] in
@[expose] def swapPair (p q : Fin 2 → k) :
    (((ι → Fin 2) → k) × ((ι → Fin 2) → k)) →ₗ[k] ((Option ι → Fin 2) → k) :=
  (tensorVec p).coprod (tensorVec q)

omit [CharP k 2] [Fintype ι] [DecidableEq ι] in
theorem swapPair_apply (p q : Fin 2 → k) (m m' : (ι → Fin 2) → k) (a : Fin 2) (y : ι → Fin 2) :
    swapPair p q (m, m') (optCons a y) = p a * m y + q a * m' y := by
  simp [swapPair, tensorVec_apply]

omit [CharP k 2] [Fintype ι] [DecidableEq ι] in
theorem swapPair_injective (p q : Fin 2 → k)
    (h : ∀ α β : k, α • p + β • q = 0 → α = 0 ∧ β = 0) :
    Function.Injective (swapPair (ι := ι) p q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨m, m'⟩ hm
  have key : ∀ y, m y = 0 ∧ m' y = 0 := by
    intro y
    refine h (m y) (m' y) ?_
    funext a
    have := congrFun hm (optCons a y)
    rw [swapPair_apply, Pi.zero_apply] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination this
  exact Prod.ext (funext fun y => (key y).1) (funext fun y => (key y).2)

end KerDim

section KerDim2

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tensorRep_swapPair (e : Option ι → ℕ) (g : SL(2, F)) (p : Fin 2 → k)
    (hA2 : twistMat k (e none) g * twistMat k (e none) g = 1)
    (m m' : (ι → Fin 2) → k) :
    tensorRep F k e g (swapPair p ((twistMat k (e none) g).mulVec p) (m, m')) =
      swapPair p ((twistMat k (e none) g).mulVec p)
        (tensorRep F k (fun i => e (some i)) g m', tensorRep F k (fun i => e (some i)) g m) := by
  set A := twistMat k (e none) g with hA
  set B := tensorRep F k (fun i => e (some i)) g with hB
  have hAAp : A.mulVec (A.mulVec p) = p := by
    rw [Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec]
  funext x
  obtain ⟨⟨a', y'⟩, rfl⟩ := optConsEquiv.surjective x
  change tensorRep F k e g _ (optCons a' y') = swapPair p (A.mulVec p) _ (optCons a' y')
  rw [tensorRep_option_apply, swapPair_apply]
  have hslice : ∀ a : Fin 2, (fun y => swapPair p (A.mulVec p) (m, m') (optCons a y)) =
      p a • m + (A.mulVec p) a • m' := by
    intro a; funext y; rw [swapPair_apply]; simp
  simp only [hslice, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := congrFun hAAp a'
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
  simp only [Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  rw [← hA]
  linear_combination (B m' y') * h1

end KerDim2

section KerDim3

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finrank_ker_sub_one_option (e : Option ι → ℕ) (g : SL(2, F))
    (hA2 : twistMat k (e none) g * twistMat k (e none) g = 1)
    (hA1 : twistMat k (e none) g ≠ 1)
    (hB2 : tensorRep F k (fun i => e (some i)) g * tensorRep F k (fun i => e (some i)) g = 1) :
    Module.finrank k (LinearMap.ker (tensorRep F k e g - 1)) = 2 ^ Fintype.card ι := by
  obtain ⟨p, hpA, hind⟩ := exists_swap_vector _ hA2 hA1
  let q := (twistMat k (e none) g).mulVec p
  let B := tensorRep F k (fun i => e (some i)) g
  let Φ := swapPair (ι := ι) p q
  have hΦinj : Function.Injective Φ := swapPair_injective p q hind
  have hdim : Module.finrank k (((ι → Fin 2) → k) × ((ι → Fin 2) → k)) =
      Module.finrank k ((Option ι → Fin 2) → k) := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_option, pow_succ]
    ring
  have hΦsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΦinj
  have hBB : ∀ m, B (B m) = m := fun m => by
    have := congrArg (fun T : Module.End k ((ι → Fin 2) → k) => T m) hB2
    simpa using this
  let J : ((ι → Fin 2) → k) →ₗ[k] (((ι → Fin 2) → k) × ((ι → Fin 2) → k)) :=
    LinearMap.prod B LinearMap.id
  have hJ : ∀ m', J m' = (B m', m') := fun m' => rfl
  have hker : LinearMap.ker (tensorRep F k e g - 1) = LinearMap.range (Φ ∘ₗ J) := by
    ext v
    obtain ⟨⟨m, m'⟩, rfl⟩ := hΦsurj v
    have hact : tensorRep F k e g (Φ (m, m')) = Φ (B m', B m) :=
      tensorRep_swapPair e g p hA2 m m'
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      LinearMap.mem_range, LinearMap.comp_apply]
    rw [hact]
    constructor
    · intro h
      have h1 := hΦinj h
      simp only [Prod.mk.injEq] at h1
      exact ⟨m', by rw [hJ, h1.1]⟩
    · rintro ⟨m'', hm''⟩
      have h1 := hΦinj hm''
      rw [hJ] at h1
      simp only [Prod.mk.injEq] at h1
      obtain ⟨h1, h2⟩ := h1
      rw [← h1, ← h2, hBB m'']
  have hinj : Function.Injective (Φ ∘ₗ J) := by
    intro m₁ m₂ h
    have := hΦinj h
    rw [hJ, hJ] at this
    exact congrArg Prod.snd this
  rw [hker, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  simp

end KerDim3

section Rank

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]

theorem twistMat_eq_one_iff (m : ℕ) (g : SL(2, F)) : twistMat k m g = 1 ↔ g = 1 := by
  constructor
  · intro h
    ext i j
    have h1 := congrFun (congrFun h i) j
    rw [twistMat_apply] at h1
    have h2 : algebraMap F k (g i j) = (1 : Matrix (Fin 2) (Fin 2) k) i j := by
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.one_apply_eq] at h1 ⊢
        have h3 : (algebraMap F k (g i i) - 1) ^ (2 ^ m) = 0 := by
          rw [sub_pow_char_pow (p := 2), h1, one_pow, sub_self]
        have := pow_eq_zero_iff (by positivity) |>.mp h3
        simpa [sub_eq_zero] using this
      · simp only [Matrix.one_apply_ne hij] at h1 ⊢
        exact pow_eq_zero_iff (by positivity) |>.mp h1
    apply (algebraMap F k).injective
    rw [h2]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  · rintro rfl; exact twistMat_one m

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharP k 2] in
theorem finrank_ker_of_intertwining {A V W : Type*} [Field A] [AddCommGroup V] [AddCommGroup W]
    [Module A V] [Module A W] (Φ : V ≃ₗ[A] W) (T : V →ₗ[A] V) (S : W →ₗ[A] W)
    (h : ∀ v, Φ (T v) = S (Φ v)) :
    Module.finrank A (LinearMap.ker (S - 1)) = Module.finrank A (LinearMap.ker (T - 1)) := by
  have : LinearMap.ker (S - 1) = Submodule.map (Φ : V →ₗ[A] W) (LinearMap.ker (T - 1)) := by
    ext w
    simp only [LinearMap.mem_ker, Submodule.mem_map]
    constructor
    · intro hw
      have hw' : S w = w := by simpa [sub_eq_zero] using hw
      refine ⟨Φ.symm w, ?_, by simp⟩
      have : T (Φ.symm w) = Φ.symm w := by
        apply Φ.injective
        rw [h, LinearEquiv.apply_symm_apply, hw']
      simp [this]
    · rintro ⟨v, hv, rfl⟩
      have hv' : T v = v := by simpa [sub_eq_zero] using hv
      have : S (Φ v) = Φ v := by rw [← h, hv']
      simp [this]
  rw [this, LinearEquiv.finrank_map_eq]

theorem finrank_ker_tensor_involution [Nonempty ι] (e : ι → ℕ) (a : SL(2, F)) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) :
    Module.finrank k (LinearMap.ker (tensorRep F k e a - 1)) = 2 ^ (Fintype.card ι - 1) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let σ : Option {b : ι // b ≠ i₀} ≃ ι := Equiv.optionSubtypeNe i₀
  let e' : Option {b : ι // b ≠ i₀} → ℕ := fun o => e (σ o)
  let φ := reindexEquiv (F := F) (k := k) σ e' e (fun o => rfl)
  have h1 := finrank_ker_of_intertwining φ.toLinearEquiv (tensorRep F k e' a) (tensorRep F k e a)
    (fun v => equiv_apply φ a v)
  rw [h1]
  have hA2 : twistMat k (e' none) a * twistMat k (e' none) a = 1 := by
    rw [← twistMat_mul, ha2, twistMat_one]
  have hA1 : twistMat k (e' none) a ≠ 1 := fun h => ha1 ((twistMat_eq_one_iff _ _).mp h)
  have hB2 : tensorRep F k (fun i => e' (some i)) a * tensorRep F k (fun i => e' (some i)) a = 1 := by
    rw [← map_mul, ha2, map_one]
  rw [finrank_ker_sub_one_option e' a hA2 hA1 hB2]
  have hc : Fintype.card {b : ι // b ≠ i₀} + 1 = Fintype.card ι := by
    rw [← Fintype.card_option]; exact Fintype.card_congr σ
  congr 1
  omega

theorem finrank_range_tensor_involution [Nonempty ι] (e : ι → ℕ) (a : SL(2, F)) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) :
    Module.finrank k (LinearMap.range (tensorRep F k e a - 1)) = 2 ^ (Fintype.card ι - 1) := by
  have h := LinearMap.finrank_range_add_finrank_ker (tensorRep F k e a - 1)
  rw [finrank_ker_tensor_involution e a ha1 ha2, Module.finrank_fintype_fun_eq_card] at h
  have hcard : Fintype.card (ι → Fin 2) = 2 ^ Fintype.card ι := by simp
  rw [hcard] at h
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  have : 2 ^ Fintype.card ι = 2 ^ (Fintype.card ι - 1) + 2 ^ (Fintype.card ι - 1) := by
    conv_lhs => rw [show Fintype.card ι = (Fintype.card ι - 1) + 1 by omega, pow_succ]
    ring
  omega

end Rank

section RootGroup

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField in
theorem exists_conj_le_rootGroup {F : Type*} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup SL(2, F)) (hA : ∀ a ∈ A, a * a = 1) :
    ∃ x : SL(2, F), ∀ a ∈ A, x⁻¹ * a * x ∈ (upperUnipotent (F := F)).range := by
  have hp : IsPGroup 2 A := fun g => ⟨1, by
    have : (g : SL(2, F)) * g = 1 := hA g g.2
    apply Subtype.ext
    simpa [pow_two] using this⟩
  obtain ⟨x, hx⟩ := pgroup_sl2_conjugate_unipotent A hp
  refine ⟨x, fun a ha => ?_⟩
  exact hx ⟨a, ha, by simp⟩

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField in
theorem card_le_of_involutions {F : Type*} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup SL(2, F)) (hA : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ Nat.card F := by
  have hp : IsPGroup 2 A := fun g => ⟨1, by
    have : (g : SL(2, F)) * g = 1 := hA g g.2
    apply Subtype.ext
    simpa [pow_two] using this⟩
  exact pgroup_sl2_card_le A hp

variable {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finrank_fixed_rootGroup {n : ℕ} (hF : Fintype.card F = 2 ^ n) (e : ι → ℕ)
    (he : Function.Injective e) (hlt : ∀ i, e i < n) :
    Module.finrank k ↥(⨅ t : F, LinearMap.ker (tensorRep F k e (uElt t) - 1)) = 1 := by
  have : (⨅ t : F, LinearMap.ker (tensorRep F k e (uElt t) - 1)) =
      Submodule.span k {(baseVec : (ι → Fin 2) → k)} := by
    ext v
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero, Submodule.mem_span_singleton]
    rw [tensorRep_fixed_iff hF e he hlt v]
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
  rw [this, finrank_span_singleton]
  intro h0
  have h3 := congrFun h0 (fun _ => 0)
  simp [baseVec_apply] at h3

end RootGroup

end CFSG.QuasithinUnique.Setup.SL2Modules
