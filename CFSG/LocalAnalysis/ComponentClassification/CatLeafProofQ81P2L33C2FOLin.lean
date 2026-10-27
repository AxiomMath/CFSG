module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FOEich

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2.OmegaTwo

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def invNil (T : V ≃ₗ[K] V) : V →ₗ[K] V := (T : V →ₗ[K] V) - LinearMap.id

theorem invNil_apply (T : V ≃ₗ[K] V) (x : V) : invNil T x = T x - x := rfl

section Inv

variable [CharP K 2] {T : V ≃ₗ[K] V} (hT : ∀ x, Q (T x) = Q x) (hTT : ∀ x, T (T x) = x)

omit [CharP K 2] in
include hT in
theorem polar_map_inv (x y : V) : polar Q (T x) (T y) = polar Q x y := by
  rw [polar, polar, ← map_add, hT, hT, hT]

omit [CharP K 2] in
include hT hTT in
theorem polar_invNil_left (u v : V) : polar Q (invNil T u) v = polar Q u (invNil T v) := by
  rw [invNil_apply, invNil_apply, polar_sub_left, polar_sub_right]
  congr 1
  rw [← polar_map_inv hT u (T v), hTT]

include hTT in
theorem invNil_invNil (v : V) : invNil T (invNil T v) = 0 := by
  have h2 : ∀ w : V, w + w = 0 := fun w => by
    rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
  rw [invNil_apply, invNil_apply, map_sub, hTT]
  calc v - T v - (T v - v) = (v + v) - (T v + T v) := by abel
    _ = 0 := by rw [h2, h2, sub_zero]

include hT in
theorem map_invNil (x : V) : Q (invNil T x) = polar Q x (invNil T x) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [invNil_apply, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q, hT,
    polar_neg_right, polar_add_right, polar_neg_right, polar_self_eq_two_mul, h2, zero_mul,
    neg_zero, add_zero, polar_comm Q (T x) x]
  linear_combination (Q x - polar Q x (T x)) * h2

end Inv

theorem exists_pairs_of_no [Finite K] [CharP K 2] [FiniteDimensional K V] {n : ℕ} (hn : 4 ≤ n)
    (hdim : finrank K V = 2 * n) (hQ : (polarBilin Q).Nondegenerate) {N : V →ₗ[K] V}
    (hNadj : ∀ u v, polar Q (N u) v = polar Q u (N v)) (hNN : ∀ v, N (N v) = 0)
    (hpNN : ∀ u v, polar Q (N u) (N v) = 0) (hN0 : ∃ x, N x ≠ 0)
    (hno : ∀ x₁ x₂ : V, Q (N x₁) = 0 → Q (N x₂) = 0 → polar Q x₁ (N x₂) = 0) :
    ∃ x₁ y₁ x₂ y₂ : V, Q x₁ = 0 ∧ Q x₂ = 0 ∧ Q y₁ = 0 ∧ Q y₂ = 0 ∧
      polar Q x₁ y₁ = 0 ∧ polar Q x₂ y₂ = 0 ∧ polar Q x₁ x₂ = 0 ∧ polar Q y₁ y₂ = 0 ∧
      polar Q x₁ y₂ = 1 ∧ polar Q x₂ y₁ = 1 ∧
      (∀ z, eichler Q x₁ y₁ (N z) = N (eichler Q x₁ y₁ z)) ∧
      (∀ z, eichler Q x₂ y₂ (N z) = N (eichler Q x₂ y₂ z)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨x₀', hx₀'⟩ : ∃ x, Q (N x) ≠ 0 := by
    by_contra! hall
    obtain ⟨x, hx⟩ := hN0
    exact hx (eq_zero_of_polar_eq_zero hQ fun y => by
      rw [polar_comm]
      exact hno y x (hall y) (hall x))
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (Q (N x₀'))⁻¹
  obtain ⟨x₀, hx₀def⟩ : ∃ x, x = r • x₀' := ⟨_, rfl⟩
  have hQx₀ : Q (N x₀) = 1 := by
    rw [hx₀def, map_smul, map_smul_eq_sq Q, pow_two, ← hr, inv_mul_cancel₀ hx₀']
  obtain ⟨t, ht⟩ : ∃ t, t = N x₀ := ⟨_, rfl⟩
  have hQt : Q t = 1 := by rw [ht, hQx₀]
  have hNt : N t = 0 := by rw [ht, hNN]
  have htt : polar Q t t = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hx₀0 : x₀ ≠ 0 := fun h0 => by
    rw [h0, map_zero, QuadraticMap.map_zero] at hQx₀
    exact zero_ne_one hQx₀
  let K₀ : Submodule K V :=
    { carrier := {x | Q (N x) = 0}
      add_mem' := fun {x y} (hx : Q (N x) = 0) (hy : Q (N y) = 0) => by
        change Q (N (x + y)) = 0
        rw [map_add, QuadraticMap.map_add Q, hx, hy, hpNN, add_zero, add_zero]
      zero_mem' := by
        change Q (N 0) = 0
        rw [map_zero, QuadraticMap.map_zero]
      smul_mem' := fun c x (hx : Q (N x) = 0) => by
        change Q (N (c • x)) = 0
        rw [map_smul, map_smul_eq_sq Q, hx, mul_zero] }
  have hdec : ∀ y, ∃ c : K, y - c • x₀ ∈ K₀ := fun y => by
    obtain ⟨c, hc⟩ := isSquare_of_charTwo' (Q (N y))
    refine ⟨c, ?_⟩
    change Q (N (y - c • x₀)) = 0
    rw [map_sub, map_smul, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q,
      map_smul_eq_sq Q, hQx₀, polar_neg_right, polar_smul_right_eq, hpNN, mul_zero, neg_zero,
      add_zero, hc, mul_one, pow_two]
    linear_combination (c * c) * h2
  let S : Submodule K V := K₀ ⊓ LinearMap.ker (polarBilin Q t)
  have hmemS : ∀ x ∈ S, Q (N x) = 0 ∧ polar Q t x = 0 := fun x hx => by
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    exact ⟨hx1, by simpa using hx2⟩
  have hSN : ∀ x ∈ S, N x = 0 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hmemS x hx
    refine eq_zero_of_polar_eq_zero hQ fun y => ?_
    obtain ⟨c, hc⟩ := hdec y
    have hy : N y = N (y - c • x₀) + c • t := by rw [map_sub, map_smul, ht, sub_add_cancel]
    rw [hNadj, hy, polar_add_right, polar_smul_right_eq, hno x _ hx1 hc, polar_comm, hx2,
      mul_zero, add_zero]
  have hker : ∀ u : V, 2 * n - 1 ≤ finrank K (LinearMap.ker (polarBilin Q u)) := fun u => by
    have h1 := LinearMap.finrank_range_add_finrank_ker (polarBilin Q u)
    have h3 : finrank K (LinearMap.range (polarBilin Q u)) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range (polarBilin Q u))
      rwa [Module.finrank_self] at this
    rw [hdim] at h1
    omega
  have hcut : ∀ (W : Submodule K V) (u : V),
      finrank K W ≤ finrank K ↥(W ⊓ LinearMap.ker (polarBilin Q u)) + 1 := fun W u => by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker (polarBilin Q u))
    have h3 := Submodule.finrank_le (W ⊔ LinearMap.ker (polarBilin Q u))
    have h4 := hker u
    rw [hdim] at h3
    omega
  have hK₀dim : 2 * n - 1 ≤ finrank K K₀ := by
    have hsup : K₀ ⊔ K ∙ x₀ = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨c, hc⟩ := hdec y
      rw [← sub_add_cancel y (c • x₀)]
      exact Submodule.add_mem_sup hc (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self x₀))
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K₀ (K ∙ x₀)
    rw [hsup, finrank_top, hdim, finrank_span_singleton hx₀0] at h1
    omega
  have hSdim : 2 * n - 2 ≤ finrank K S := by
    show 2 * n - 2 ≤ finrank K ↥(K₀ ⊓ LinearMap.ker (polarBilin Q t))
    have := hcut K₀ t
    omega
  have hle_of : ∀ W : Submodule K V, (∀ u ∈ W, ∀ v ∈ W, polar Q u v = 0) →
      W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) W := fun W hW x hx =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun y hy => by
      change polarBilin Q y x = 0
      rw [polarBilin_apply_apply]
      exact hW y hy x hx
  obtain ⟨u₁, hu₁S, v₁', hv₁'S, hne₁⟩ : ∃ u ∈ S, ∃ v ∈ S, polar Q u v ≠ 0 := by
    by_contra! h
    have h1 := Submodule.finrank_mono (hle_of S h)
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, hdim] at h1
    omega
  obtain ⟨v₁, hv₁def⟩ : ∃ v, v = (polar Q u₁ v₁')⁻¹ • v₁' := ⟨_, rfl⟩
  have hv₁S : v₁ ∈ S := by rw [hv₁def]; exact S.smul_mem _ hv₁'S
  have huv₁ : polar Q u₁ v₁ = 1 := by
    rw [hv₁def, polar_smul_right_eq, inv_mul_cancel₀ hne₁]
  let S₁ : Submodule K V :=
    S ⊓ LinearMap.ker (polarBilin Q u₁) ⊓ LinearMap.ker (polarBilin Q v₁)
  have hmemS₁ : ∀ x ∈ S₁, x ∈ S ∧ polar Q u₁ x = 0 ∧ polar Q v₁ x = 0 := fun x hx => by
    obtain ⟨hx12, hx3⟩ := Submodule.mem_inf.mp hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx12
    exact ⟨hx1, by simpa using hx2, by simpa using hx3⟩
  have hS₁dim : 2 * n - 4 ≤ finrank K S₁ := by
    show 2 * n - 4 ≤
      finrank K ↥(S ⊓ LinearMap.ker (polarBilin Q u₁) ⊓ LinearMap.ker (polarBilin Q v₁))
    have h3 := hcut S u₁
    have h4 := hcut (S ⊓ LinearMap.ker (polarBilin Q u₁)) v₁
    omega
  obtain ⟨u₂, hu₂S₁, v₂', hv₂'S₁, hne₂⟩ : ∃ u ∈ S₁, ∃ v ∈ S₁, polar Q u v ≠ 0 := by
    by_contra! h
    have hle := hle_of S₁ h
    have h1 := LinearMap.BilinForm.finrank_orthogonal hQ S₁
    have h3 := Submodule.finrank_mono hle
    rw [hdim] at h1
    have heq : S₁ = LinearMap.BilinForm.orthogonal (polarBilin Q) S₁ :=
      Submodule.eq_of_le_of_finrank_eq hle (by omega)
    have hu₁mem : u₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) S₁ :=
      (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun y hy => by
        change polarBilin Q y u₁ = 0
        rw [polarBilin_apply_apply, polar_comm]
        exact (hmemS₁ y hy).2.1
    rw [← heq] at hu₁mem
    have h5 := (hmemS₁ u₁ hu₁mem).2.2
    rw [polar_comm, huv₁] at h5
    exact one_ne_zero h5
  obtain ⟨v₂, hv₂def⟩ : ∃ v, v = (polar Q u₂ v₂')⁻¹ • v₂' := ⟨_, rfl⟩
  have hv₂S₁ : v₂ ∈ S₁ := by rw [hv₂def]; exact S₁.smul_mem _ hv₂'S₁
  have huv₂ : polar Q u₂ v₂ = 1 := by
    rw [hv₂def, polar_smul_right_eq, inv_mul_cancel₀ hne₂]
  obtain ⟨hu₂S, hu₁u₂, hv₁u₂⟩ := hmemS₁ u₂ hu₂S₁
  obtain ⟨hv₂S, hu₁v₂, hv₁v₂⟩ := hmemS₁ v₂ hv₂S₁
  have hadj : ∀ w ∈ S, ∃ c : K, Q (w + c • t) = 0 ∧ N (w + c • t) = 0 := fun w hw => by
    obtain ⟨c, hc⟩ := isSquare_of_charTwo' (Q w)
    have hwt : polar Q w t = 0 := by rw [polar_comm]; exact (hmemS w hw).2
    refine ⟨c, ?_, ?_⟩
    · rw [QuadraticMap.map_add Q, map_smul_eq_sq Q, hQt, polar_smul_right_eq, hwt, mul_zero,
        add_zero, mul_one, hc, pow_two]
      linear_combination (c * c) * h2
    · rw [map_add, map_smul, hNt, smul_zero, add_zero]
      exact hSN w hw
  have hpair : ∀ w₁ ∈ S, ∀ w₂ ∈ S, ∀ c₁ c₂ : K,
      polar Q (w₁ + c₁ • t) (w₂ + c₂ • t) = polar Q w₁ w₂ := fun w₁ hw₁ w₂ hw₂ c₁ c₂ => by
    have h₁ : polar Q w₁ t = 0 := by rw [polar_comm]; exact (hmemS w₁ hw₁).2
    have h₂ : polar Q t w₂ = 0 := (hmemS w₂ hw₂).2
    rw [polar_add_left, polar_add_right, polar_add_right, polar_smul_left_eq, polar_smul_left_eq,
      polar_smul_right_eq, polar_smul_right_eq, h₁, h₂, htt]
    simp only [mul_zero, add_zero]
  obtain ⟨a₁, hQa₁, hNa₁⟩ := hadj u₁ hu₁S
  obtain ⟨b₁, hQb₁, hNb₁⟩ := hadj v₁ hv₁S
  obtain ⟨a₂, hQa₂, hNa₂⟩ := hadj u₂ hu₂S
  obtain ⟨b₂, hQb₂, hNb₂⟩ := hadj v₂ hv₂S
  refine ⟨u₁ + a₁ • t, v₂ + b₂ • t, u₂ + a₂ • t, v₁ + b₁ • t, hQa₁, hQa₂, hQb₂, hQb₁, ?_, ?_, ?_,
    ?_, ?_, ?_, eichler_comm_ker hNadj hNa₁ hNb₂, eichler_comm_ker hNadj hNa₂ hNb₁⟩
  · rw [hpair _ hu₁S _ hv₂S, hu₁v₂]
  · rw [hpair _ hu₂S _ hv₁S, polar_comm, hv₁u₂]
  · rw [hpair _ hu₁S _ hu₂S, hu₁u₂]
  · rw [hpair _ hv₂S _ hv₁S, polar_comm, hv₁v₂]
  · rw [hpair _ hu₁S _ hv₁S, huv₁]
  · rw [hpair _ hu₂S _ hv₂S, huv₂]

theorem exists_eichler_pair_commuting [Finite K] [CharP K 2] [FiniteDimensional K V] {n : ℕ}
    (hn : 4 ≤ n) (hdim : finrank K V = 2 * n) (hQ : (polarBilin Q).Nondegenerate)
    {T : V ≃ₗ[K] V} (hT : ∀ x, Q (T x) = Q x) (hTT : ∀ x, T (T x) = x) (hT1 : T ≠ 1) :
    ∃ x₁ y₁ x₂ y₂ : V, Q x₁ = 0 ∧ Q x₂ = 0 ∧ Q y₁ = 0 ∧ Q y₂ = 0 ∧
      polar Q x₁ y₁ = 0 ∧ polar Q x₂ y₂ = 0 ∧ polar Q x₁ x₂ = 0 ∧ polar Q y₁ y₂ = 0 ∧
      polar Q x₁ y₂ = 1 ∧ polar Q x₂ y₁ = 1 ∧
      (∀ z, eichler Q x₁ y₁ (T z) = T (eichler Q x₁ y₁ z)) ∧
      (∀ z, eichler Q x₂ y₂ (T z) = T (eichler Q x₂ y₂ z)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨N, hNdef⟩ : ∃ N, N = invNil T := ⟨_, rfl⟩
  have hNadj : ∀ u v, polar Q (N u) v = polar Q u (N v) := by
    rw [hNdef]; exact polar_invNil_left hT hTT
  have hNN : ∀ v, N (N v) = 0 := by rw [hNdef]; exact invNil_invNil hTT
  have hQN : ∀ x, Q (N x) = polar Q x (N x) := by rw [hNdef]; exact map_invNil hT
  have hpNN : ∀ u v, polar Q (N u) (N v) = 0 := fun u v => by
    rw [hNadj, hNN, polar_zero_right]
  have hTN : ∀ z, T z = N z + z := fun z => by rw [hNdef, invNil_apply, sub_add_cancel]
  have toT : ∀ x₁ y₁ : V,
      (∀ z, eichler Q x₁ y₁ (N z) = N (eichler Q x₁ y₁ z)) →
      ∀ z, eichler Q x₁ y₁ (T z) = T (eichler Q x₁ y₁ z) := by
    intro x₁ y₁ hc z
    rw [hTN z, map_add, hc z, hTN (eichler Q x₁ y₁ z)]
  suffices hs : ∃ x₁ y₁ x₂ y₂ : V, Q x₁ = 0 ∧ Q x₂ = 0 ∧ Q y₁ = 0 ∧ Q y₂ = 0 ∧
      polar Q x₁ y₁ = 0 ∧ polar Q x₂ y₂ = 0 ∧ polar Q x₁ x₂ = 0 ∧ polar Q y₁ y₂ = 0 ∧
      polar Q x₁ y₂ = 1 ∧ polar Q x₂ y₁ = 1 ∧
      (∀ z, eichler Q x₁ y₁ (N z) = N (eichler Q x₁ y₁ z)) ∧
      (∀ z, eichler Q x₂ y₂ (N z) = N (eichler Q x₂ y₂ z)) by
    obtain ⟨x₁, y₁, x₂, y₂, hx₁, hx₂, hy₁, hy₂, h11, h22, hxx, hyy, h12, h21, hc₁, hc₂⟩ := hs
    exact ⟨x₁, y₁, x₂, y₂, hx₁, hx₂, hy₁, hy₂, h11, h22, hxx, hyy, h12, h21,
      toT x₁ y₁ hc₁, toT x₂ y₂ hc₂⟩
  have hN0 : ∃ x, N x ≠ 0 := by
    by_contra! h
    apply hT1
    ext x
    have hx := h x
    rw [hNdef, invNil_apply, sub_eq_zero] at hx
    exact hx
  by_cases hyes : ∃ x₁ x₂ : V, Q (N x₁) = 0 ∧ Q (N x₂) = 0 ∧ polar Q x₁ (N x₂) ≠ 0
  ·
    obtain ⟨x₁, x₂', hx₁, hx₂', hne⟩ := hyes
    obtain ⟨x₂, hx₂def⟩ : ∃ x, x = (polar Q x₁ (N x₂'))⁻¹ • x₂' := ⟨_, rfl⟩
    have hx₂ : Q (N x₂) = 0 := by rw [hx₂def, map_smul, map_smul_eq_sq Q, hx₂', mul_zero]
    have h12 : polar Q x₁ (N x₂) = 1 := by
      rw [hx₂def, map_smul, polar_smul_right_eq, inv_mul_cancel₀ hne]
    have h21 : polar Q x₂ (N x₁) = 1 := by rw [← hNadj, polar_comm, h12]
    have hp₁ : polar Q x₁ (N x₁) = 0 := by rw [← hQN, hx₁]
    have hp₂ : polar Q x₂ (N x₂) = 0 := by rw [← hQN, hx₂]
    have hp₂' : polar Q (N x₂) x₂ = 0 := by rw [polar_comm, hp₂]
    obtain ⟨u₁, hu₁⟩ : ∃ u, u = x₁ + Q x₁ • N x₂ := ⟨_, rfl⟩
    obtain ⟨u₂, hu₂⟩ : ∃ u, u = x₂ + (Q x₂ • N x₁ + polar Q x₁ x₂ • N x₂) := ⟨_, rfl⟩
    have hNu₁ : N u₁ = N x₁ := by rw [hu₁, map_add, map_smul, hNN, smul_zero, add_zero]
    have hNu₂ : N u₂ = N x₂ := by
      rw [hu₂, map_add, map_add, map_smul, map_smul, hNN, hNN, smul_zero, smul_zero, add_zero,
        add_zero]
    have hQu₁ : Q u₁ = 0 := by
      rw [hu₁, QuadraticMap.map_add Q, map_smul_eq_sq Q, hx₂, mul_zero, add_zero,
        polar_smul_right_eq, h12, mul_one]
      linear_combination (Q x₁) * h2
    have hQu₂ : Q u₂ = 0 := by
      rw [hu₂, QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq Q,
        map_smul_eq_sq Q, hx₁,
        hx₂, polar_smul_left_eq, polar_smul_right_eq, hpNN, polar_add_right, polar_smul_right_eq,
        polar_smul_right_eq, h21, hp₂]
      linear_combination (Q x₂) * h2
    have hu₁u₂ : polar Q u₁ u₂ = 0 := by
      rw [hu₁, hu₂]
      simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, hp₁,
        h12, hp₂', hpNN, mul_zero, add_zero, mul_one, zero_add]
      linear_combination (polar Q x₁ x₂) * h2
    have hu₁N : polar Q u₁ (N u₂) = 1 := by
      rw [hNu₂, hu₁, polar_add_left, polar_smul_left_eq, hpNN, mul_zero, add_zero, h12]
    have hu₂N : polar Q u₂ (N u₁) = 1 := by
      rw [hNu₁, hu₂, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
        hpNN, hpNN, mul_zero, mul_zero, add_zero, add_zero, h21]
    refine ⟨u₁, N u₁, u₂, N u₂, hQu₁, hQu₂, by rw [hNu₁, hx₁], by rw [hNu₂, hx₂],
      by rw [← hQN, hNu₁, hx₁], by rw [← hQN, hNu₂, hx₂], hu₁u₂, hpNN _ _, hu₁N, hu₂N, ?_, ?_⟩
    · exact eichler_comm_self hNadj hNN hQu₁ (by rw [hNu₁, hx₁]) (by rw [← hQN, hNu₁, hx₁])
    · exact eichler_comm_self hNadj hNN hQu₂ (by rw [hNu₂, hx₂]) (by rw [← hQN, hNu₂, hx₂])
  · push Not at hyes
    exact exists_pairs_of_no hn hdim hQ hNadj hNN hpNN hN0 hyes

theorem exists_eichler_commuting [Finite K] [CharP K 2] [FiniteDimensional K V] {n : ℕ}
    (hn : 4 ≤ n) (hdim : finrank K V = 2 * n) (hQ : (polarBilin Q).Nondegenerate)
    {T : V ≃ₗ[K] V} (hT : ∀ x, Q (T x) = Q x) (hTT : ∀ x, T (T x) = x) (hT1 : T ≠ 1) :
    ∃ h ∈ elementaryGroup Q, (∀ z, h (T z) = T (h z)) ∧ h ^ 3 = 1 ∧ h ≠ 1 := by
  obtain ⟨x₁, y₁, x₂, y₂, hx₁, hx₂, hy₁, hy₂, h11, h22, hxx, hyy, h12, h21, hc₁, hc₂⟩ :=
    exists_eichler_pair_commuting hn hdim hQ hT hTT hT1
  obtain ⟨h3, h1⟩ := eichler_pair_pow_three hx₁ hx₂ hy₁ hy₂ h11 h22 hxx hyy h12 h21
  refine ⟨eichler Q x₁ y₁ * eichler Q x₂ y₂, mul_mem (eichler_mem_elementaryGroup Q _ _)
    (eichler_mem_elementaryGroup Q _ _), fun z => ?_, h3, h1⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hc₂, hc₁]

end CFSG.ComponentClassification.HarrisLit.L33.C2.OmegaTwo
