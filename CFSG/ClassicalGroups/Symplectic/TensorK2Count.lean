module

public import CFSG.ClassicalGroups.Symplectic.TensorK2
public import CFSG.ClassicalGroups.Symplectic.PointRadicalAction

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open Matrix

theorem card_eq_card_mul_card_map_mul_card_range {D A B : Type*} [Group D] [Group A] [Group B]
    (S : D →* A) (H : D →* B) (Dq : Subgroup D) (hDq : ∀ d, d ∈ Dq ↔ (S d = 1 ∧ H d = 1)) :
    Nat.card D = Nat.card Dq * Nat.card (Subgroup.map S H.ker) * Nat.card H.range := by
  have h1 := Subgroup.card_ker_mul_card_range H
  have h2 : (S.ker).relIndex H.ker * Nat.card (S.ker ⊓ H.ker :) = Nat.card H.ker :=
    Subgroup.relIndex_mul_card S.ker H.ker
  have h3 : Dq = S.ker ⊓ H.ker := by
    ext d
    rw [hDq, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]
  rw [Subgroup.relIndex_ker, ← h3] at h2
  rw [← h1, ← h2]
  ring

theorem rt1_arith_one {Dq a r q n m : ℕ} (hDq : 0 < Dq) (hq : 2 ≤ q) (hm : 2 ≤ m)
    (hn : 2 * m ≤ n) (ha : a ≤ q) (hr : r ≤ q) (hge : Dq * q ^ (n - 1) ≤ Dq * a * r) :
    False := by
  have h1 : q ^ (n - 1) ≤ a * r := by
    refine Nat.le_of_mul_le_mul_left ?_ hDq
    simpa [mul_assoc] using hge
  have h2 : a * r ≤ q * q := Nat.mul_le_mul ha hr
  have h3 : q ^ 3 ≤ q ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : q ^ 3 = q * q * q := by ring
  nlinarith

theorem rt1_arith_two {Dq r v q n m : ℕ} (hDq : 0 < Dq) (hq : 2 ≤ q) (hm : 1 ≤ m)
    (hn : 2 * m ≤ n) (hr2 : 2 ≤ r) (hrq : r ≤ q) (hv₁ : v ≤ q ^ (2 * m))
    (hv₂ : q ^ (2 * m) ≤ v)
    (hcnt : Dq * q ^ (2 * m - 1) * r * (q * v) = Dq * q ^ (2 * n)) : False := by
  have hv : v = q ^ (2 * m) := le_antisymm hv₁ hv₂
  subst hv
  have hqpos : 0 < q := by omega
  have e1 : Dq * q ^ (2 * m - 1) * r * (q * q ^ (2 * m)) = Dq * (r * q ^ (4 * m)) := by
    have : q ^ (2 * m - 1) * q = q ^ (2 * m) := by
      rw [← pow_succ]; congr 1; omega
    calc Dq * q ^ (2 * m - 1) * r * (q * q ^ (2 * m))
        = Dq * r * ((q ^ (2 * m - 1) * q) * q ^ (2 * m)) := by ring
      _ = Dq * r * (q ^ (2 * m) * q ^ (2 * m)) := by rw [this]
      _ = Dq * (r * q ^ (4 * m)) := by
        rw [← pow_add]; ring_nf
  rw [e1] at hcnt
  have e2 : r * q ^ (4 * m) = q ^ (2 * n) := Nat.eq_of_mul_eq_mul_left hDq hcnt
  have e3 : q ^ (2 * n) = q ^ (4 * m) * q ^ (2 * n - 4 * m) := by
    rw [← pow_add]; congr 1; omega
  have e4 : r = q ^ (2 * n - 4 * m) := by
    refine Nat.eq_of_mul_eq_mul_left (pow_pos hqpos (4 * m)) ?_
    rw [e3] at e2
    rw [mul_comm] at e2
    exact e2
  by_cases hn' : n = 2 * m
  · rw [e4] at hr2
    have : 2 * n - 4 * m = 0 := by omega
    rw [this, pow_zero] at hr2
    omega
  · have h5 : 2 ≤ 2 * n - 4 * m := by omega
    have h6 : q ^ 2 ≤ q ^ (2 * n - 4 * m) := Nat.pow_le_pow_right hqpos h5
    have h7 : q < q ^ 2 := by nlinarith
    omega

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} {E : Type*} [AddCommGroup E]
  [Module K E] {D : Type*} [Group D]

theorem card_le_pow_of_decomp (hm : 2 ≤ m) (ι₁ ι₂ : (Fin m ⊕ Fin m → K) →ₗ[K] E)
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) {k₀ k₁ : Fin 2 → K}
    (T : D →* (E ≃ₗ[K] E)) (S : D →* GL (Fin m ⊕ Fin m) K) (H : D →* GL (Fin 2) K)
    (hT : ∀ (d : D) (x : Fin m ⊕ Fin m → K) (k : Fin 2 → K), T d (tensorK2 ι₁ ι₂ x k) =
      tensorK2 ι₁ ι₂ ((S d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)
        ((H d : Matrix (Fin 2) (Fin 2) K) *ᵥ k))
    (hLuall : ∀ g ∈ LspGL m K u, ∃ d : D, H d = 1 ∧ S d = g)
    (Yp V : AddSubgroup E)
    (hdec : ∀ v : E, ∃ (x₀ x₁ : Fin m ⊕ Fin m → K) (z : E), z ∈ Yp ∧
      v = tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ + z)
    (hYp : ∀ (x₀ x₁ : Fin m ⊕ Fin m → K) (z : E), z ∈ Yp →
      tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ + z = 0 → x₀ = 0 ∧ x₁ = 0)
    (hTYp : ∀ d : D, ∀ z ∈ Yp, T d z = z)
    (hV1 : ∀ d : D, ∀ v ∈ V, ∃ s : K, T d v - v = s • tensorK2 ι₁ ι₂ u k₀)
    (hV3 : ∀ v ∈ V, (∀ d : D, T d v = v) → ∃ s : K, v = s • tensorK2 ι₁ ι₂ u k₀) :
    Nat.card V ≤ Nat.card K ^ (2 * m) := by
  classical
  have hshape : ∀ v ∈ V, ∃ (x₀ : Fin m ⊕ Fin m → K) (μ : K) (z : E),
      spForm m K x₀ u = 0 ∧ z ∈ Yp ∧
        v = tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ (μ • u) k₁ + z := by
    intro v hv
    obtain ⟨x₀, x₁, z, hz, hvz⟩ := hdec v
    have hgg : ∀ g ∈ LspGL m K u, ∃ s : K,
        (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x₀ = x₀ + s • u ∧
          (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x₁ = x₁ := by
      intro g hg
      obtain ⟨d, hHd, hSd⟩ := hLuall g hg
      obtain ⟨s, hs⟩ := hV1 d v hv
      have hTv : T d v =
          tensorK2 ι₁ ι₂ ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x₀) k₀ +
          tensorK2 ι₁ ι₂ ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x₁) k₁ + z := by
        rw [hvz, map_add, map_add, hT, hT, hTYp d z hz, hSd, hHd]
        simp
      have hsum : tensorK2 ι₁ ι₂
            ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x₀ - x₀ - s • u) k₀ +
          tensorK2 ι₁ ι₂ ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x₁ - x₁) k₁ + 0 =
            0 := by
        have h1 : tensorK2 ι₁ ι₂ ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x₀ - x₀ - s • u)
            k₀ + tensorK2 ι₁ ι₂ ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x₁ - x₁) k₁ + 0 =
            (T d v - v) - s • tensorK2 ι₁ ι₂ u k₀ := by
          rw [hTv]
          conv_rhs => rw [hvz]
          simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
          abel
        rw [h1, hs, sub_self]
      obtain ⟨h0, h1⟩ := hYp _ _ 0 Yp.zero_mem hsum
      refine ⟨s, ?_, ?_⟩
      · rw [sub_sub, sub_eq_zero] at h0
        rw [h0, add_comm]
      · exact sub_eq_zero.mp h1
    have hfix₁ : ∀ g ∈ LspGL m K u,
        (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x₁ = x₁ := fun g hg =>
      (hgg g hg).choose_spec.2
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (mem_span_of_forall_LspGL_apply_eq hu hfix₁)
    have hperp : spForm m K x₀ u = 0 :=
      spForm_eq_zero_of_forall_LspGL_apply_sub_mem hm hu fun g hg =>
        ⟨(hgg g hg).choose, (hgg g hg).choose_spec.1⟩
    exact ⟨x₀, μ, z, hperp, hz, by rw [hμ]; exact hvz⟩
  choose! x₀ μ z hx₀ hz hv using hshape
  let f : V → {x : Fin m ⊕ Fin m → K // spForm m K x u = 0} × K := fun v =>
    (⟨x₀ v, hx₀ v v.2⟩, μ v)
  have hf : Function.Injective f := by
    intro v v' hvv
    have hx : x₀ v = x₀ v' := congrArg (fun p => (p.1 : Fin m ⊕ Fin m → K)) hvv
    have hμ' : μ v = μ v' := congrArg Prod.snd hvv
    have hsub : (v : E) - v' = z v - z v' := by
      have h1 := hv v v.2
      have h2 := hv v' v'.2
      calc (v : E) - v' = (tensorK2 ι₁ ι₂ (x₀ v) k₀ + tensorK2 ι₁ ι₂ (μ v • u) k₁ + z v) -
            (tensorK2 ι₁ ι₂ (x₀ v') k₀ + tensorK2 ι₁ ι₂ (μ v' • u) k₁ + z v') := by rw [← h1, ← h2]
        _ = z v - z v' := by rw [hx, hμ']; abel
    have hmem : z v - z v' ∈ Yp := Yp.sub_mem (hz v v.2) (hz v' v'.2)
    have hVsub : (v : E) - v' ∈ V := V.sub_mem v.2 v'.2
    have hfixd : ∀ d : D, T d ((v : E) - v') = (v : E) - v' := by
      intro d
      rw [hsub]
      exact hTYp d _ hmem
    obtain ⟨s, hs⟩ := hV3 _ hVsub hfixd
    have hs0 : s • u = 0 ∧ (0 : Fin m ⊕ Fin m → K) = 0 := by
      refine hYp (s • u) 0 (-(z v - z v')) (Yp.neg_mem hmem) ?_
      have h1 : s • tensorK2 ι₁ ι₂ u k₀ = z v - z v' := by rw [← hs, hsub]
      simp only [map_smul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply] at h1 ⊢
      rw [h1]
      abel
    have : s = 0 := (smul_eq_zero.mp hs0.1).resolve_right hu
    rw [this, zero_smul] at hs
    exact Subtype.ext (sub_eq_zero.mp hs)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, card_orthogonal_vec hu] at hcard
  have e : 2 * m = (2 * m - 1) + 1 := by omega
  rw [e, pow_succ]
  exact hcard


theorem pow_le_card_of_translate [Finite E] (hm : 2 ≤ m)
    (ι₁ ι₂ : (Fin m ⊕ Fin m → K) →ₗ[K] E) {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    {k₀ k₁ : Fin 2 → K}
    (T : D →* (E ≃ₗ[K] E)) (S : D →* GL (Fin m ⊕ Fin m) K) (H : D →* GL (Fin 2) K)
    (hT : ∀ (d : D) (x : Fin m ⊕ Fin m → K) (k : Fin 2 → K), T d (tensorK2 ι₁ ι₂ x k) =
      tensorK2 ι₁ ι₂ ((S d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)
        ((H d : Matrix (Fin 2) (Fin 2) K) *ᵥ k))
    (hLuall : ∀ g ∈ LspGL m K u, ∃ d : D, H d = 1 ∧ S d = g)
    (V : AddSubgroup E)
    (hV2 : ∀ (d : D) (x : Fin m ⊕ Fin m → K) (k : Fin 2 → K), spForm m K x u = 0 →
      T d (tensorK2 ι₁ ι₂ x k) - tensorK2 ι₁ ι₂ x k ∈ V)
    (hind : ∀ (x₀ x₁ : Fin m ⊕ Fin m → K),
      tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ = 0 → x₀ = 0 ∧ x₁ = 0)
    {d₁ : D} {t : K} (ht : t ≠ 0)
    (hH₁ : (H d₁ : Matrix (Fin 2) (Fin 2) K) *ᵥ k₁ = k₁ + t • k₀) :
    Nat.card K ^ (2 * m) ≤ Nat.card V := by
  classical
  obtain ⟨s, hs, x, hxu, l, hl, hsx⟩ := exists_mem_LspGL_apply_sub_smul hm hu
  obtain ⟨d₀, hHd₀, hSd₀⟩ := hLuall s hs
  have hmuV : ∀ μ : K, tensorK2 ι₁ ι₂ (μ • u) k₁ ∈ V := by
    intro μ
    have hperp : spForm m K ((μ * l⁻¹) • x) u = 0 := by simp [hxu]
    have h1 := hV2 d₀ ((μ * l⁻¹) • x) k₁ hperp
    have h2 : T d₀ (tensorK2 ι₁ ι₂ ((μ * l⁻¹) • x) k₁) - tensorK2 ι₁ ι₂ ((μ * l⁻¹) • x) k₁ =
        tensorK2 ι₁ ι₂ (μ • u) k₁ := by
      rw [hT, hSd₀, hHd₀]
      simp only [Units.val_one, Matrix.one_mulVec, Matrix.mulVec_smul, hsx, smul_add, map_add,
        LinearMap.add_apply, smul_smul]
      have : μ * l⁻¹ * l = μ := by field_simp
      rw [this]
      abel
    rwa [h2] at h1
  let F : {x : Fin m ⊕ Fin m → K // spForm m K x u = 0} × K → V := fun p =>
    ⟨(T d₁ (tensorK2 ι₁ ι₂ p.1 k₁) - tensorK2 ι₁ ι₂ p.1 k₁) + tensorK2 ι₁ ι₂ (p.2 • u) k₁,
      V.add_mem (hV2 d₁ p.1 k₁ p.1.2) (hmuV p.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨x, hx⟩, μ⟩ ⟨⟨x', hx'⟩, μ'⟩ h
    have h' := congrArg Subtype.val h
    simp only [F] at h'
    rw [hT, hT, hH₁] at h'
    have hsum : tensorK2 ι₁ ι₂ (t • ((S d₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (x - x')))
        k₀ + tensorK2 ι₁ ι₂ ((S d₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (x - x') -
          (x - x') + (μ - μ') • u) k₁ = 0 := by
      rw [← sub_eq_zero] at h'
      rw [← h']
      simp only [Matrix.mulVec_sub, map_sub, map_add, map_smul, LinearMap.sub_apply,
        LinearMap.add_apply, LinearMap.smul_apply, sub_smul]
      module
    obtain ⟨h1, h2⟩ := hind _ _ hsum
    have h3 : (S d₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (x - x') = 0 :=
      (smul_eq_zero.mp h1).resolve_left ht
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr (S d₁).isUnit
    have h4 : x - x' = 0 := by
      apply hinj
      rw [h3, Matrix.mulVec_zero]
    have h5 : x = x' := sub_eq_zero.mp h4
    subst h5
    have h6 : (μ - μ') • u = 0 := by
      rw [sub_self, Matrix.mulVec_zero, sub_self, zero_add] at h2
      exact h2
    have h7 : μ = μ' := sub_eq_zero.mp ((smul_eq_zero.mp h6).resolve_right hu)
    subst h7
    rfl
  have hcard := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, card_orthogonal_vec hu] at hcard
  have e : 2 * m = (2 * m - 1) + 1 := by omega
  rw [e, pow_succ]
  exact hcard

theorem false_of_H_trivial (hm : 2 ≤ m)
    (ι₁ ι₂ : (Fin m ⊕ Fin m → K) →ₗ[K] E) {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    {k₀ k₁ : Fin 2 → K}
    (T : D →* (E ≃ₗ[K] E)) (S : D →* GL (Fin m ⊕ Fin m) K) (H : D →* GL (Fin 2) K)
    (hT : ∀ (d : D) (x : Fin m ⊕ Fin m → K) (k : Fin 2 → K), T d (tensorK2 ι₁ ι₂ x k) =
      tensorK2 ι₁ ι₂ ((S d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)
        ((H d : Matrix (Fin 2) (Fin 2) K) *ᵥ k))
    (hLuall : ∀ g ∈ LspGL m K u, ∃ d : D, H d = 1 ∧ S d = g)
    (hSu : ∀ d : D, (S d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u)
    (hHtriv : ∀ d : D, H d = 1) (V : AddSubgroup E)
    (hV2 : ∀ (d : D) (x : Fin m ⊕ Fin m → K) (k : Fin 2 → K), spForm m K x u = 0 →
      T d (tensorK2 ι₁ ι₂ x k) - tensorK2 ι₁ ι₂ x k ∈ V)
    (hV3 : ∀ v ∈ V, (∀ d : D, T d v = v) → ∃ s : K, v = s • tensorK2 ι₁ ι₂ u k₀)
    (hind : ∀ (x₀ x₁ : Fin m ⊕ Fin m → K),
      tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ = 0 → x₀ = 0 ∧ x₁ = 0) : False := by
  classical
  obtain ⟨s, hs, x, hxu, l, hl, hsx⟩ := exists_mem_LspGL_apply_sub_smul hm hu
  obtain ⟨d₀, -, hSd₀⟩ := hLuall s hs
  have hmem : tensorK2 ι₁ ι₂ (l • u) k₁ ∈ V := by
    have h1 := hV2 d₀ x k₁ hxu
    have h2 : T d₀ (tensorK2 ι₁ ι₂ x k₁) - tensorK2 ι₁ ι₂ x k₁ = tensorK2 ι₁ ι₂ (l • u) k₁ := by
      rw [hT, hSd₀, hHtriv d₀]
      simp only [Units.val_one, Matrix.one_mulVec, hsx, map_add, LinearMap.add_apply]
      abel
    rwa [h2] at h1
  have hfix : ∀ d : D, T d (tensorK2 ι₁ ι₂ (l • u) k₁) = tensorK2 ι₁ ι₂ (l • u) k₁ := by
    intro d
    rw [hT, hHtriv d]
    simp [Matrix.mulVec_smul, hSu d]
  obtain ⟨s', hs'⟩ := hV3 _ hmem hfix
  have hsum : tensorK2 ι₁ ι₂ (s' • u) k₀ + tensorK2 ι₁ ι₂ (-(l • u)) k₁ = 0 := by
    have h1 : tensorK2 ι₁ ι₂ (s' • u) k₀ = s' • tensorK2 ι₁ ι₂ u k₀ := by simp
    rw [h1, ← hs']
    simp
  obtain ⟨-, h2⟩ := hind _ _ hsum
  exact hl ((smul_eq_zero.mp (neg_eq_zero.mp h2)).resolve_right hu)

omit [CharP K 2] in
theorem card_le_of_transvection_subgroup (u : Fin m ⊕ Fin m → K)
    (R : Subgroup (GL (Fin m ⊕ Fin m) K))
    (hR : ∀ g ∈ R, ∃ c : K, ∀ v : Fin m ⊕ Fin m → K,
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v + (c * spForm m K v u) • u) :
    Nat.card R ≤ Nat.card K := by
  classical
  choose! c hc using hR
  have hinj : Function.Injective (fun g : R => c g) := by
    intro g g' hgg
    refine Subtype.ext (Units.ext ?_)
    apply Matrix.ext_of_mulVec_single
    intro i
    simp only at hgg
    rw [hc g g.2, hc g' g'.2, hgg]
  exact Nat.card_le_card_of_injective _ hinj

end Core

end CFSG.ClassicalGroups.Symplectic
