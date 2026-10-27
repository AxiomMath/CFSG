module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Pair
public import Mathlib.FieldTheory.Separable

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 CFSG.HardMathSupport.GuralnickMalle QuadraticMap Module

section Odd

open Polynomial

theorem squarefree_X_sub_one_mul {K : Type*} [Field K] [CharP K 2] {t : K} (ht : t ≠ 0) :
    Squarefree ((X - 1) * (X ^ 2 + C t * X + 1) : K[X]) := by
  have h2 : (2 : K[X]) = 0 := CharP.ofNat_eq_zero K[X] 2
  have hC : C t * C t⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ ht, C_1]
  have hd : derivative ((X - 1) * (X ^ 2 + C t * X + 1) : K[X]) = X ^ 2 + C t + 1 := by
    simp only [derivative_mul, derivative_sub, derivative_add, derivative_X, derivative_one,
      derivative_C, derivative_X_sq, C_ofNat, zero_mul, zero_add, sub_zero, mul_one, one_mul,
      add_zero]
    linear_combination (X ^ 2 + C t * X - X - C t) * h2
  apply Polynomial.Separable.squarefree
  rw [Polynomial.separable_def, hd]
  refine ⟨C t⁻¹ ^ 2, -(C t⁻¹ ^ 2 * (X + C t + 1)), ?_⟩
  linear_combination (-(C t * C t⁻¹ + 1)) * hC +
    (-(1 + C t⁻¹ ^ 2 * (X ^ 2 + C t * X + C t + 1))) * h2

theorem odd_orderOf_of_annihilated {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] (g : V ≃ₗ[K] V) {t : K} (ht : t ≠ 0) (hord : orderOf g ≠ 0)
    (hg : ((g : V →ₗ[K] V) - 1) * ((g : V →ₗ[K] V) ^ 2 + t • (g : V →ₗ[K] V) + 1) = 0) :
    Odd (orderOf g) := by
  rcases Nat.even_or_odd (orderOf g) with ⟨k, hk⟩ | hodd
  · exfalso
    have h2 : (2 : K[X]) = 0 := CharP.ofNat_eq_zero K[X] 2
    have hk0 : k ≠ 0 := by
      intro h0
      apply hord
      omega
    have hklt : k < orderOf g := by omega
    have hgk1 : g ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0 hklt
    set T : Module.End K V := (g : V →ₗ[K] V) with hT
    have hcoe : ∀ n : ℕ, ((g ^ n : V ≃ₗ[K] V) : V →ₗ[K] V) = T ^ n := fun n =>
      map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom g n
    have hT2k : T ^ (k + k) = 1 := by
      rw [← hk, ← hcoe, pow_orderOf_eq_one]
      exact map_one LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    have hf : aeval T ((X - 1) * (X ^ 2 + C t * X + 1) : K[X]) = 0 := by
      simp only [map_mul, map_sub, map_add, map_pow, aeval_X, aeval_C, map_one]
      rw [← Algebra.smul_def]
      exact hg
    have hμf : minpoly K T ∣ ((X - 1) * (X ^ 2 + C t * X + 1) : K[X]) :=
      minpoly.dvd K T hf
    have hsq : Squarefree (minpoly K T) :=
      Squarefree.squarefree_of_dvd hμf (squarefree_X_sub_one_mul ht)
    set P : K[X] := X ^ k - 1 with hP
    have hP2 : P ^ 2 = X ^ (k + k) - 1 := by
      rw [hP]
      linear_combination (1 - X ^ k) * h2
    have hμP2 : minpoly K T ∣ P ^ 2 := by
      apply minpoly.dvd K T
      rw [hP2]
      simp [hT2k]
    have hμP : minpoly K T ∣ P := (hsq.dvd_pow_iff_dvd two_ne_zero).mp hμP2
    have hPT : aeval T P = 0 := by
      obtain ⟨c, hc⟩ := hμP
      rw [hc, map_mul, minpoly.aeval, zero_mul]
    have hTk : T ^ k = 1 := by
      have hPk : aeval T P = T ^ k - 1 := by simp [hP]
      rw [hPk] at hPT
      exact sub_eq_zero.mp hPT
    apply hgk1
    apply LinearEquiv.toLinearMap_injective
    exact (hcoe k).trans (hTk.trans rfl)
  · exact hodd

end Odd

section Dual

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

theorem exists_dual_pair_of_inf_orthogonal_eq_bot {A' : Submodule K V}
    (hA' : finrank K A' = 2) {a₁ a₂ : V}
    (hperp : A' ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf)
      (Submodule.span K ({a₁, a₂} : Set V)) = ⊥) :
    ∃ a₁' ∈ A', ∃ a₂' ∈ A', polar Qf a₁ a₁' = 1 ∧ polar Qf a₁ a₂' = 0 ∧
      polar Qf a₂ a₁' = 0 ∧ polar Qf a₂ a₂' = 1 := by
  have hfin : Module.Finite K A' := Module.finite_of_finrank_pos (by omega)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : A' →ₗ[K] (Fin 2 → K),
      ∀ x : A', Φ x = ![polar Qf a₁ (x : V), polar Qf a₂ (x : V)] := by
    refine ⟨LinearMap.pi ![(polarBilin Qf a₁).comp A'.subtype,
      (polarBilin Qf a₂).comp A'.subtype], fun x => ?_⟩
    funext i
    fin_cases i <;> simp [LinearMap.pi_apply]
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero Φ]
    intro x hx
    rw [hΦ x] at hx
    have h₁ : polar Qf a₁ (x : V) = 0 := by simpa using congrFun hx 0
    have h₂ : polar Qf a₂ (x : V) = 0 := by simpa using congrFun hx 1
    have hmem : (x : V) ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf)
        (Submodule.span K ({a₁, a₂} : Set V)) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
      simp only [polarBilin_apply_apply, polar_add_left, polar_smul_left, h₁, h₂, smul_zero,
        add_zero]
    have hxmem : (x : V) ∈ A' ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf)
        (Submodule.span K ({a₁, a₂} : Set V)) := Submodule.mem_inf.mpr ⟨x.2, hmem⟩
    rw [hperp, Submodule.mem_bot] at hxmem
    exact Subtype.ext (by simpa using hxmem)
  have hdim : finrank K A' = finrank K (Fin 2 → K) := by
    rw [hA', Module.finrank_fin_fun K]
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨y, hy⟩ := hsurj ![1, 0]
  obtain ⟨z, hz⟩ := hsurj ![0, 1]
  rw [hΦ y] at hy
  rw [hΦ z] at hz
  refine ⟨(y : V), y.2, (z : V), z.2, ?_, ?_, ?_, ?_⟩
  · simpa using congrFun hy 0
  · simpa using congrFun hz 0
  · simpa using congrFun hy 1
  · simpa using congrFun hz 1

end Dual

section Relation

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

theorem siegel_pair_relation {a₁ a₂ a₁' a₂' : V} {c c' : K} {s s' : V ≃ₗ[K] V}
    (hs : ∀ v, s v = v + c • (polar Qf v a₁ • a₂ + polar Qf v a₂ • a₁))
    (hs' : ∀ v, s' v = v + c' • (polar Qf v a₁' • a₂' + polar Qf v a₂' • a₁'))
    (h12 : polar Qf a₁ a₂ = 0) (h12' : polar Qf a₁' a₂' = 0)
    (d11 : polar Qf a₁ a₁' = 1) (d12 : polar Qf a₁ a₂' = 0)
    (d21 : polar Qf a₂ a₁' = 0) (d22 : polar Qf a₂ a₂' = 1) :
    (((s * s' : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) *
      (((s * s' : V ≃ₗ[K] V) : V →ₗ[K] V) ^ 2 + (c * c') • ((s * s' : V ≃ₗ[K] V) : V →ₗ[K] V) + 1)
      = 0 := by
  have e2 : ∀ z : V, z + z = 0 := fun z => by
    rw [← two_smul K z, CharTwo.two_eq_zero, zero_smul]
  have e2K : ∀ t : K, t + t = 0 := fun t => by
    rw [← two_mul, CharTwo.two_eq_zero, zero_mul]
  have v11 : polar Qf a₁ a₁ = 0 :=
    polar_self_eq_zero a₁
  have v22 : polar Qf a₂ a₂ = 0 :=
    polar_self_eq_zero a₂
  have v33 : polar Qf a₁' a₁' = 0 :=
    polar_self_eq_zero a₁'
  have v44 : polar Qf a₂' a₂' = 0 :=
    polar_self_eq_zero a₂'
  have v12 : polar Qf a₁ a₂ = 0 := h12
  have v21 : polar Qf a₂ a₁ = 0 := by rw [polar_comm]; exact h12
  have v34 : polar Qf a₁' a₂' = 0 := h12'
  have v43 : polar Qf a₂' a₁' = 0 := by rw [polar_comm]; exact h12'
  have v13 : polar Qf a₁ a₁' = 1 := d11
  have v31 : polar Qf a₁' a₁ = 1 := by rw [polar_comm]; exact d11
  have v14 : polar Qf a₁ a₂' = 0 := d12
  have v41 : polar Qf a₂' a₁ = 0 := by rw [polar_comm]; exact d12
  have v23 : polar Qf a₂ a₁' = 0 := d21
  have v32 : polar Qf a₁' a₂ = 0 := by rw [polar_comm]; exact d21
  have v24 : polar Qf a₂ a₂' = 1 := d22
  have v42 : polar Qf a₂' a₂ = 1 := by rw [polar_comm]; exact d22
  obtain ⟨corr, hcorr⟩ : ∃ f : V → V, ∀ z, f z =
      c • (polar Qf z a₁ • a₂ + polar Qf z a₂ • a₁) +
        c' • (polar Qf z a₁' • a₂' + polar Qf z a₂' • a₁') +
        (c * c') • (polar Qf z a₁' • a₁ + polar Qf z a₂' • a₂) := ⟨_, fun _ => rfl⟩
  obtain ⟨pj, hpj⟩ : ∃ f : V → V, ∀ z, f z =
      polar Qf z a₁' • a₁ + polar Qf z a₂' • a₂ + polar Qf z a₁ • a₁' + polar Qf z a₂ • a₂' :=
    ⟨_, fun _ => rfl⟩
  set G : V →ₗ[K] V := ((s * s' : V ≃ₗ[K] V) : V →ₗ[K] V)
  have hgz : ∀ z, s (s' z) = z + corr z := by
    intro z
    rw [hcorr z, hs (s' z), hs' z]
    simp only [polar_add_left, polar_smul_left, v11, v12, v13, v14, v21, v22, v23, v24,
      v31, v32, v33, v34, v41, v42, v43, v44, smul_eq_mul, mul_zero, mul_one, zero_add,
      add_zero, smul_zero]
    module
  have hGz : ∀ z, G z = z + corr z := fun z => hgz z
  have hcadd : ∀ u v, corr (u + v) = corr u + corr v := by
    intro u v
    rw [hcorr (u + v), hcorr u, hcorr v]
    simp only [polar_add_left]
    module
  have hGGx : ∀ x, G (G x) = x + corr (corr x) := by
    intro x
    rw [hGz (G x), hGz x, hcadd]
    linear_combination (norm := module) e2 (corr x)
  have hcc : ∀ x, corr (corr x) + (c * c') • corr x = (c * c') • pj x := by
    intro x
    rw [hcorr (corr x), hcorr x, hpj x]
    simp only [polar_add_left, polar_smul_left, v11, v12, v13, v14, v21, v22, v23, v24,
      v31, v32, v33, v34, v41, v42, v43, v44, smul_eq_mul]
    linear_combination (norm := module)
      (c ^ 2 * c' * polar Qf x a₁ + c ^ 2 * c' ^ 2 * polar Qf x a₂') • e2 a₂ +
      (c ^ 2 * c' * polar Qf x a₂ + c ^ 2 * c' ^ 2 * polar Qf x a₁') • e2 a₁ +
      (c * c' ^ 2 * polar Qf x a₂') • e2 a₁' + (c * c' ^ 2 * polar Qf x a₁') • e2 a₂'
  have key : ∀ x, G (G x) + (c * c') • G x + x = (c * c') • (x + pj x) := by
    intro x
    rw [hGGx x, hGz x]
    linear_combination (norm := module) e2 x + hcc x
  have hzero : ∀ z, polar Qf z a₁ = 0 → polar Qf z a₂ = 0 → polar Qf z a₁' = 0 →
      polar Qf z a₂' = 0 → corr z = 0 := by
    intro z h1 h2 h3 h4
    rw [hcorr z, h1, h2, h3, h4]
    simp
  have hfix : ∀ x, G (x + pj x) = x + pj x := by
    intro x
    have h1 : polar Qf (x + pj x) a₁ = 0 := by
      rw [hpj x]
      simp only [polar_add_left, polar_smul_left, v11, v12, v13, v14, v21, v22, v23, v24,
        v31, v32, v33, v34, v41, v42, v43, v44, smul_eq_mul]
      linear_combination e2K (polar Qf x a₁)
    have h2 : polar Qf (x + pj x) a₂ = 0 := by
      rw [hpj x]
      simp only [polar_add_left, polar_smul_left, v11, v12, v13, v14, v21, v22, v23, v24,
        v31, v32, v33, v34, v41, v42, v43, v44, smul_eq_mul]
      linear_combination e2K (polar Qf x a₂)
    have h3 : polar Qf (x + pj x) a₁' = 0 := by
      rw [hpj x]
      simp only [polar_add_left, polar_smul_left, v11, v12, v13, v14, v21, v22, v23, v24,
        v31, v32, v33, v34, v41, v42, v43, v44, smul_eq_mul]
      linear_combination e2K (polar Qf x a₁')
    have h4 : polar Qf (x + pj x) a₂' = 0 := by
      rw [hpj x]
      simp only [polar_add_left, polar_smul_left, v11, v12, v13, v14, v21, v22, v23, v24,
        v31, v32, v33, v34, v41, v42, v43, v44, smul_eq_mul]
      linear_combination e2K (polar Qf x a₂')
    rw [hGz, hzero _ h1 h2 h3 h4, add_zero]
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply, pow_two]
  rw [key x, map_smul, hfix x, sub_self]

end Relation

section Main

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Qf : QuadraticForm K V}

theorem pow_four_eq_one_or_odd_orderOf_mul
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s') :
    (s * s') ^ 4 = 1 ∨ Odd (orderOf (s * s')) := by
  by_cases h4 : (s * s') ^ 4 = 1
  · exact Or.inl h4
  right
  obtain ⟨h1, h2, -, -, -⟩ := corollary_one_three hnd hs hs' h4
  have hAs : ∀ w ∈ movedSpace s, Qf w = 0 := fun w hw => hs.qf_eq_zero_of_mem_movedSpace hw
  have hA's : ∀ w ∈ movedSpace s', Qf w = 0 := fun w hw => hs'.qf_eq_zero_of_mem_movedSpace hw
  obtain ⟨a₁, a₂, ha₁, ha₂, hli, hspan⟩ :=
    exists_basis_of_finrank_eq_two (hs.finrank_movedSpace hnd)
  have hperp : movedSpace s' ⊓ LinearMap.BilinForm.orthogonal (polarBilin Qf)
      (Submodule.span K ({a₁, a₂} : Set V)) = ⊥ := by
    rw [hspan]
    exact h2
  obtain ⟨a₁', ha₁', a₂', ha₂', d11, d12, d21, d22⟩ :=
    exists_dual_pair_of_inf_orthogonal_eq_bot (hs'.finrank_movedSpace hnd) hperp
  have hli' : LinearIndependent K ![a₁', a₂'] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    have e1 := congrArg (fun x => polar Qf a₁ x) hαβ
    have e2 := congrArg (fun x => polar Qf a₂ x) hαβ
    simp only [polar_add_right, polar_smul_right, d11, d12, d21, d22, smul_eq_mul, mul_one,
      mul_zero, add_zero, zero_add, polar_zero_right] at e1 e2
    exact ⟨e1, e2⟩
  have hspan' : Submodule.span K ({a₁', a₂'} : Set V) = movedSpace s' :=
    span_pair_eq_of_finrank_eq_two (hs'.finrank_movedSpace hnd) ha₁' ha₂' hli'
  obtain ⟨c, hc0, hc⟩ := exists_siegel_scalar hnd hs.isometry hli hspan hAs
  obtain ⟨c', hc'0, hc'⟩ := exists_siegel_scalar hnd hs'.isometry hli' hspan' hA's
  have hrel := siegel_pair_relation hc hc' (polar_eq_zero_of_totallySingular hAs ha₁ ha₂)
    (polar_eq_zero_of_totallySingular hA's ha₁' ha₂') d11 d12 d21 d22
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) fun f g h => LinearEquiv.ext (congrFun h)
  exact odd_orderOf_of_annihilated (s * s') (mul_ne_zero hc0 hc'0) (orderOf_pos _).ne' hrel

theorem orderOf_mul_ne_six (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {s s' : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hs' : IsLongRootElement Qf s') :
    orderOf (s * s') ≠ 6 := by
  intro h6
  rcases pow_four_eq_one_or_odd_orderOf_mul hnd hs hs' with h | h
  · have := orderOf_dvd_of_pow_eq_one h
    rw [h6] at this
    omega
  · rw [h6] at h
    exact absurd h (by decide)

end Main

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
