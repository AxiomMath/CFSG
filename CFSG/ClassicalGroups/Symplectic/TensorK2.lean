module

public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.ClassicalGroups.Symplectic

open Matrix

section Tensor

variable {K : Type*} [Field K] {N E : Type*} [AddCommGroup N] [Module K N] [AddCommGroup E]
  [Module K E]

@[expose] def tensorK2 (ι₁ ι₂ : N →ₗ[K] E) : N →ₗ[K] (Fin 2 → K) →ₗ[K] E :=
  LinearMap.mk₂ K (fun x k => k 0 • ι₁ x + k 1 • ι₂ x)
    (fun x x' k => by simp [smul_add]; abel)
    (fun c x k => by simp [smul_comm c])
    (fun x k k' => by simp [add_smul]; abel)
    (fun c x k => by simp [mul_smul])

theorem tensorK2_apply (ι₁ ι₂ : N →ₗ[K] E) (x : N) (k : Fin 2 → K) :
    tensorK2 ι₁ ι₂ x k = k 0 • ι₁ x + k 1 • ι₂ x := rfl

@[expose] def detFin2 (k k' : Fin 2 → K) : K := k 0 * k' 1 - k 1 * k' 0


theorem tensorK2_add_tensorK2 (ι₁ ι₂ : N →ₗ[K] E) (x₀ x₁ : N) (k₀ k₁ : Fin 2 → K) :
    tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ =
      ι₁ (k₀ 0 • x₀ + k₁ 0 • x₁) + ι₂ (k₀ 1 • x₀ + k₁ 1 • x₁) := by
  simp only [tensorK2_apply, map_add, map_smul]
  module

theorem tensorK2_eq_zero_pair (ι₁ ι₂ : N →ₗ[K] E)
    (hind : ∀ a a', ι₁ a + ι₂ a' = 0 → a = 0 ∧ a' = 0) {k₀ k₁ : Fin 2 → K}
    (hk : detFin2 k₀ k₁ = 1) {x₀ x₁ : N}
    (h : tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ = 0) : x₀ = 0 ∧ x₁ = 0 := by
  rw [tensorK2_add_tensorK2] at h
  obtain ⟨e₁, e₂⟩ := hind _ _ h
  constructor
  · have key : detFin2 k₀ k₁ • x₀ =
        k₁ 1 • (k₀ 0 • x₀ + k₁ 0 • x₁) - k₁ 0 • (k₀ 1 • x₀ + k₁ 1 • x₁) := by
      unfold detFin2
      module
    rw [e₁, e₂, hk, one_smul, smul_zero, smul_zero, sub_zero] at key
    exact key
  · have key : detFin2 k₀ k₁ • x₁ =
        k₀ 0 • (k₀ 1 • x₀ + k₁ 1 • x₁) - k₀ 1 • (k₀ 0 • x₀ + k₁ 0 • x₁) := by
      unfold detFin2
      module
    rw [e₁, e₂, hk, one_smul, smul_zero, smul_zero, sub_zero] at key
    exact key

theorem exists_tensorK2_eq_add (ι₁ ι₂ : N →ₗ[K] E) {k₀ k₁ : Fin 2 → K} (hk : detFin2 k₀ k₁ = 1)
    (a a' : N) : ∃ x₀ x₁ : N, ι₁ a + ι₂ a' = tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ := by
  have hk' : k₀ 0 * k₁ 1 - k₀ 1 * k₁ 0 = 1 := hk
  have h₁ : k₀ 0 • (k₁ 1 • a - k₁ 0 • a') + k₁ 0 • (k₀ 0 • a' - k₀ 1 • a) =
      (k₀ 0 * k₁ 1 - k₀ 1 * k₁ 0) • a := by
    module
  have h₂ : k₀ 1 • (k₁ 1 • a - k₁ 0 • a') + k₁ 1 • (k₀ 0 • a' - k₀ 1 • a) =
      (k₀ 0 * k₁ 1 - k₀ 1 * k₁ 0) • a' := by
    module
  rw [hk', one_smul] at h₁ h₂
  refine ⟨k₁ 1 • a - k₁ 0 • a', k₀ 0 • a' - k₀ 1 • a, ?_⟩
  rw [tensorK2_add_tensorK2, h₁, h₂]

theorem exists_detFin2_eq_one {k₀ : Fin 2 → K} (h : k₀ ≠ 0) :
    ∃ k₁ : Fin 2 → K, detFin2 k₀ k₁ = 1 := by
  by_cases h0 : k₀ 0 = 0
  · have h1 : k₀ 1 ≠ 0 := by
      intro h1
      apply h
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨![-(k₀ 1)⁻¹, 0], ?_⟩
    simp [detFin2, h0, mul_inv_cancel₀ h1]
  · refine ⟨![0, (k₀ 0)⁻¹], ?_⟩
    simp [detFin2, h0]

theorem tensorK2_form {m : ℕ} (Bf : LinearMap.BilinForm K E)
    (ι₁ ι₂ : (Fin m ⊕ Fin m → K) →ₗ[K] E) (c : K) (hsymm : ∀ e f, Bf e f = Bf f e)
    (h₁₁ : ∀ x y, Bf (ι₁ x) (ι₁ y) = 0) (h₂₂ : ∀ x y, Bf (ι₂ x) (ι₂ y) = 0)
    (h₁₂ : ∀ x y, Bf (ι₁ x) (ι₂ y) = c * spForm m K x y)
    (x y : Fin m ⊕ Fin m → K) (k k' : Fin 2 → K) :
    Bf (tensorK2 ι₁ ι₂ x k) (tensorK2 ι₁ ι₂ y k') = c * detFin2 k k' * spForm m K x y := by
  have hyx : Bf (ι₂ x) (ι₁ y) = -(c * spForm m K x y) := by
    rw [hsymm (ι₂ x) (ι₁ y), h₁₂ y x, ← spForm_isAlt.neg_eq x y, mul_neg]
  simp only [tensorK2_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, h₁₁, h₂₂, hyx, h₁₂, detFin2]
  ring

theorem tensorK2_map (ι₁ ι₂ : N →ₗ[K] E) (T : E →ₗ[K] E) (s : N →ₗ[K] N)
    (η : Matrix (Fin 2) (Fin 2) K)
    (h₁ : ∀ x, T (ι₁ x) = ι₁ (η 0 0 • s x) + ι₂ (η 1 0 • s x))
    (h₂ : ∀ x, T (ι₂ x) = ι₁ (η 0 1 • s x) + ι₂ (η 1 1 • s x)) (x : N) (k : Fin 2 → K) :
    T (tensorK2 ι₁ ι₂ x k) = tensorK2 ι₁ ι₂ (s x) (η.mulVec k) := by
  simp only [tensorK2_apply, map_add, map_smul, h₁, h₂, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  module

theorem vec_eq_detFin2_smul_add {k₀ k₁ : Fin 2 → K} (hk : detFin2 k₀ k₁ = 1) (v : Fin 2 → K) :
    v = detFin2 v k₁ • k₀ + detFin2 k₀ v • k₁ := by
  have hk' : k₀ 0 * k₁ 1 - k₀ 1 * k₁ 0 = 1 := hk
  have e0 : v 0 = (detFin2 v k₁ • k₀ + detFin2 k₀ v • k₁) 0 := by
    simp only [detFin2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-v 0) * hk'
  have e1 : v 1 = (detFin2 v k₁ • k₀ + detFin2 k₀ v • k₁) 1 := by
    simp only [detFin2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-v 1) * hk'
  funext i
  fin_cases i
  · exact e0
  · exact e1

theorem matrix_eq_of_mulVec_basis_two {k₀ k₁ : Fin 2 → K} (hk : detFin2 k₀ k₁ = 1)
    {η η' : Matrix (Fin 2) (Fin 2) K} (h₀ : η.mulVec k₀ = η'.mulVec k₀)
    (h₁ : η.mulVec k₁ = η'.mulVec k₁) : η = η' := by
  have hmul : ∀ v : Fin 2 → K, η.mulVec v = η'.mulVec v := by
    intro v
    calc η.mulVec v = η.mulVec (detFin2 v k₁ • k₀ + detFin2 k₀ v • k₁) :=
          congrArg (Matrix.mulVec η) (vec_eq_detFin2_smul_add hk v)
      _ = η'.mulVec (detFin2 v k₁ • k₀ + detFin2 k₀ v • k₁) := by
          simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h₀, h₁]
      _ = η'.mulVec v := congrArg (Matrix.mulVec η') (vec_eq_detFin2_smul_add hk v).symm
  ext i j
  have h := congrFun (hmul (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

theorem eq_one_of_mulVec_basis_two {k₀ k₁ : Fin 2 → K} (hk : detFin2 k₀ k₁ = 1)
    (η : Matrix (Fin 2) (Fin 2) K) (h₀ : η.mulVec k₀ = k₀) (h₁ : η.mulVec k₁ = k₁) :
    η = 1 := by
  refine matrix_eq_of_mulVec_basis_two hk ?_ ?_
  · rw [h₀, Matrix.one_mulVec]
  · rw [h₁, Matrix.one_mulVec]

theorem tensorK2_fix_aux (ι₁ ι₂ : N →ₗ[K] E) (hind : ∀ a a', ι₁ a + ι₂ a' = 0 → a = 0 ∧ a' = 0)
    {u w : N} (hu : u ≠ 0) {k₀ k : Fin 2 → K} (hk₀ : k₀ ≠ 0)
    (h : tensorK2 ι₁ ι₂ w k = tensorK2 ι₁ ι₂ u k₀) :
    ∃ μ : K, μ ≠ 0 ∧ w = μ • u ∧ k = μ⁻¹ • k₀ := by
  simp only [tensorK2_apply] at h
  have key : ι₁ (k 0 • w - k₀ 0 • u) + ι₂ (k 1 • w - k₀ 1 • u) = 0 := by
    simp only [map_sub, map_smul]
    rw [sub_add_sub_comm]
    exact sub_eq_zero.mpr h
  obtain ⟨e0, e1⟩ := hind _ _ key
  have hcoord : ∀ j, k j • w = k₀ j • u :=
    Fin.forall_fin_two.mpr ⟨sub_eq_zero.mp e0, sub_eq_zero.mp e1⟩
  obtain ⟨i, hi⟩ : ∃ i, k₀ i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    exact hk₀ (funext hcon)
  have hki : k i ≠ 0 := by
    intro h0
    have h1 := hcoord i
    rw [h0, zero_smul] at h1
    exact (smul_eq_zero.mp h1.symm).elim hi hu
  have hw0 : w = (k₀ i / k i) • u := by
    have h1 := hcoord i
    calc w = (k i)⁻¹ • (k i • w) := by rw [smul_smul, inv_mul_cancel₀ hki, one_smul]
      _ = (k₀ i / k i) • u := by
          rw [h1, smul_smul, div_eq_mul_inv, mul_comm (k i)⁻¹ (k₀ i)]
  obtain ⟨μ, hμ, hw⟩ : ∃ μ : K, μ ≠ 0 ∧ w = μ • u :=
    ⟨k₀ i / k i, div_ne_zero hi hki, hw0⟩
  have hkj : ∀ j, k j * μ = k₀ j := by
    intro j
    have h1 : k j • w = k₀ j • u := hcoord j
    rw [hw, smul_smul] at h1
    exact smul_left_injective K hu h1
  refine ⟨μ, hμ, hw, ?_⟩
  funext j
  rw [Pi.smul_apply, smul_eq_mul, ← hkj j, mul_comm (k j) μ, ← mul_assoc,
    inv_mul_cancel₀ hμ, one_mul]

theorem unip_of_tensor_fix [CharP K 2] (ι₁ ι₂ : N →ₗ[K] E)
    (hind : ∀ a a', ι₁ a + ι₂ a' = 0 → a = 0 ∧ a' = 0) {u : N} (hu : u ≠ 0)
    {k₀ k₁ : Fin 2 → K} (hk : detFin2 k₀ k₁ = 1) (T : E →ₗ[K] E) (s : N →ₗ[K] N)
    (η : Matrix (Fin 2) (Fin 2) K)
    (hT : ∀ x k, T (tensorK2 ι₁ ι₂ x k) = tensorK2 ι₁ ι₂ (s x) (η.mulVec k))
    (hfix : T (tensorK2 ι₁ ι₂ u k₀) = tensorK2 ι₁ ι₂ u k₀) (hs2 : ∀ x, s (s x) = x)
    (hη2 : η * η = 1) :
    s u = u ∧ η.mulVec k₀ = k₀ ∧ ∃ t : K, η.mulVec k₁ = k₁ + t • k₀ := by
  have hk' : k₀ 0 * k₁ 1 - k₀ 1 * k₁ 0 = 1 := hk
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hk₀ : k₀ ≠ 0 := by
    intro h0
    rw [h0] at hk'
    simp at hk'
  have hsym : tensorK2 ι₁ ι₂ (s u) (η.mulVec k₀) = tensorK2 ι₁ ι₂ u k₀ :=
    (hT u k₀).symm.trans hfix
  obtain ⟨μ, hμ, hsu, hηk⟩ := tensorK2_fix_aux ι₁ ι₂ hind hu hk₀ hsym
  have hμμ : μ * μ = 1 := by
    have h1 : (μ * μ) • u = u := by
      calc (μ * μ) • u = μ • μ • u := by rw [smul_smul]
        _ = μ • s u := by rw [← hsu]
        _ = s (μ • u) := by rw [map_smul]
        _ = s (s u) := by rw [← hsu]
        _ = u := hs2 u
    have h1' : (μ * μ) • u = (1 : K) • u := by
      rw [one_smul]
      exact h1
    exact smul_left_injective K hu h1'
  have hμ1 : μ = 1 := by
    have h3 : (μ - 1) * (μ - 1) = 0 := by linear_combination hμμ + (1 - μ) * h2
    linear_combination mul_self_eq_zero.mp h3
  have hsu1 : s u = u := by rw [hsu, hμ1, one_smul]
  have hηk0 : η.mulVec k₀ = k₀ := by rw [hηk, hμ1, inv_one, one_smul]
  refine ⟨hsu1, hηk0, ?_⟩
  obtain ⟨a, d, hv⟩ : ∃ a d : K, η.mulVec k₁ = a • k₀ + d • k₁ :=
    ⟨detFin2 (η.mulVec k₁) k₁, detFin2 k₀ (η.mulVec k₁), vec_eq_detFin2_smul_add hk _⟩
  have hηη : η.mulVec (η.mulVec k₁) = k₁ := by
    rw [Matrix.mulVec_mulVec, hη2, Matrix.one_mulVec]
  have hηη' : η.mulVec (a • k₀ + d • k₁) = k₁ := by
    rw [← hv]
    exact hηη
  have h3 : a • k₀ + d • (a • k₀ + d • k₁) = k₁ := by
    have e := hηη'
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hηk0, hv] at e
    exact e
  have E0 := congrFun h3 0
  have E1 := congrFun h3 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at E0 E1
  have hdd : d * d = 1 := by
    linear_combination (-k₀ 1) * E0 + k₀ 0 * E1 - (d * d - 1) * hk'
  have hd1 : d = 1 := by
    have h5 : (d - 1) * (d - 1) = 0 := by linear_combination hdd + (1 - d) * h2
    linear_combination mul_self_eq_zero.mp h5
  refine ⟨a, ?_⟩
  rw [hv, hd1, one_smul]
  exact add_comm _ _

theorem card_le_of_unipotent_subgroup [Finite K] {k₀ k₁ : Fin 2 → K} (hk : detFin2 k₀ k₁ = 1)
    (R : Subgroup (GL (Fin 2) K))
    (hR : ∀ h ∈ R, (h : Matrix (Fin 2) (Fin 2) K).mulVec k₀ = k₀ ∧
      ∃ t : K, (h : Matrix (Fin 2) (Fin 2) K).mulVec k₁ = k₁ + t • k₀) :
    Nat.card R ≤ Nat.card K := by
  have hex : ∀ h : R, ∃ t : K,
      (h.1 : Matrix (Fin 2) (Fin 2) K).mulVec k₁ = k₁ + t • k₀ :=
    fun h => (hR h.1 h.2).2
  choose t ht using hex
  have hinj : Function.Injective t := by
    intro h₁ h₂ htEq
    have hmat : (h₁.1 : Matrix (Fin 2) (Fin 2) K) = (h₂.1 : Matrix (Fin 2) (Fin 2) K) := by
      apply matrix_eq_of_mulVec_basis_two hk
      · rw [(hR h₁.1 h₁.2).1, (hR h₂.1 h₂.2).1]
      · rw [ht h₁, ht h₂, htEq]
    exact Subtype.ext (Units.ext hmat)
  exact Nat.card_le_card_of_injective t hinj

end Tensor

section Orth

variable {m : ℕ} {K : Type} [Field K]

theorem card_orthogonal_vec [Finite K] {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) :
    Nat.card {x : Fin m ⊕ Fin m → K // spForm m K x u = 0} = Nat.card K ^ (2 * m - 1) := by
  obtain ⟨f, hf⟩ : ∃ f : (Fin m ⊕ Fin m → K) →ₗ[K] K, ∀ x, f x = spForm m K x u :=
    ⟨LinearMap.flip (spForm m K) u, fun x => LinearMap.flip_apply (spForm m K) x u⟩
  have hne : ∃ x₀, f x₀ ≠ 0 := by
    by_contra hcon
    have hrad : ∀ x, spForm m K x u = 0 := fun x => by
      rw [← hf]
      by_contra h'
      exact hcon ⟨x, h'⟩
    exact hu ((spForm_nondegenerate (m := m) (K := K)).2 u hrad)
  obtain ⟨x₀, hx₀⟩ := hne
  have hsurj : Function.Surjective f := fun c =>
    ⟨(c / f x₀) • x₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hx₀]⟩
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, Module.finrank_self, finrank_spSpace] at hrank
  have hdim : Module.finrank K (LinearMap.ker f) = 2 * m - 1 := by omega
  have hcard : Nat.card {x : Fin m ⊕ Fin m → K // spForm m K x u = 0} =
      Nat.card (LinearMap.ker f) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [LinearMap.mem_ker, hf]
  rw [hcard, Module.natCard_eq_pow_finrank (K := K), hdim]

end Orth

end CFSG.ClassicalGroups.Symplectic
