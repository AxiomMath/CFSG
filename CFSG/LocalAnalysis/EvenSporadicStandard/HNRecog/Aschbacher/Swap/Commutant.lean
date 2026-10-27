module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Orthogonal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Simple

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private lemma neg_eq_self_zmod_two (v : V) : -v = v := by
  rw [← neg_one_smul (ZMod 2) v, show (-1 : ZMod 2) = 1 by decide, one_smul]

private lemma add_self_eq_zero_zmod_two (v : V) : v + v = 0 := by
  have h : (2 : ZMod 2) • v = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  simpa [two_smul] using h

private lemma sub_sub_self_sub_self (a b : V) : (a - b) - (b - a) = 0 := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add_rev, neg_neg]
  simp only [neg_eq_self_zmod_two]
  exact add_self_eq_zero_zmod_two _

theorem eq_one_of_commute_of_isometry (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (hS : StdHyp σ)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hBσ : ∀ g x y, B (σ g x) (σ g y) = B x y)
    (u : V ≃ₗ[ZMod 2] V) (hu : ∀ g, u * σ g = σ g * u) (hBu : ∀ x y, B (u x) (u y) = B x y) :
    u = 1 := by
  classical
  obtain ⟨c, Fp, Fm, hE⟩ := exists_eigenData σ hS
  let α : V ≃ₗ[ZMod 2] V := σ (a₀, 1)
  let ν₁ : V ≃ₗ[ZMod 2] V := σ (n₀, 1)
  let ν₂ : V ≃ₗ[ZMod 2] V := σ (1, n₀)
  let n : V ≃ₗ[ZMod 2] V := σ (n₀, n₀)
  let γ : V →ₗ[ZMod 2] V := (α : V →ₗ[ZMod 2] V)
  let γinv : V →ₗ[ZMod 2] V := ((α⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
  have ha05 : (a₀ : A5) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one a₀
    rwa [orderOf_a₀] at h
  have hn02 : (n₀ : A5) ^ 2 = 1 := by decide +kernel
  have hα5 : α ^ 5 = 1 := by
    have hp : ((a₀, 1) : A5 × A5) ^ 5 = 1 := by
      ext <;> simp [Prod.pow_fst, Prod.pow_snd, ha05]
    have h := congrArg σ hp
    rw [map_pow, map_one] at h
    simpa [α] using h
  have hγpow : ∀ k : ℕ, γ ^ k = (↑(α ^ k) : V →ₗ[ZMod 2] V) := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, LinearEquiv.coe_toLinearMap_one]; rfl
    | succ k ih =>
        rw [pow_succ, ih]
        change (↑(α ^ k) : V →ₗ[ZMod 2] V) * (↑α : V →ₗ[ZMod 2] V)
          = (↑(α ^ (k + 1)) : V →ₗ[ZMod 2] V)
        rw [← LinearEquiv.coe_toLinearMap_mul, pow_succ]
  have hγinvpow : ∀ k : ℕ, γinv ^ k = (↑((α⁻¹) ^ k) : V →ₗ[ZMod 2] V) := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, LinearEquiv.coe_toLinearMap_one]; rfl
    | succ k ih =>
        rw [pow_succ, ih]
        change (↑((α⁻¹) ^ k) : V →ₗ[ZMod 2] V) * (↑(α⁻¹) : V →ₗ[ZMod 2] V)
          = (↑((α⁻¹) ^ (k + 1)) : V →ₗ[ZMod 2] V)
        rw [← LinearEquiv.coe_toLinearMap_mul, pow_succ]
  have hγ5 : γ ^ 5 = 1 := by
    rw [hγpow 5, hα5]
    rfl
  have hn_eq : n = ν₁ * ν₂ := by
    change σ (n₀, n₀) = σ (n₀, 1) * σ (1, n₀)
    have hp : ((n₀, 1) : A5 × A5) * (1, n₀) = (n₀, n₀) := by ext <;> simp
    rw [← hp, ← map_mul]
  have hn2 : n * n = 1 := by
    have hp : ((n₀, n₀) : A5 × A5) ^ 2 = 1 := by
      ext <;> simp [Prod.pow_fst, Prod.pow_snd, hn02]
    have h := congrArg σ hp
    rw [map_pow, map_one] at h
    simpa [n, pow_two] using h
  have hν12 : ν₁ * ν₁ = 1 := by
    have hp : ((n₀, 1) : A5 × A5) ^ 2 = 1 := by
      ext <;> simp [Prod.pow_fst, Prod.pow_snd, hn02]
    have h := congrArg σ hp
    rw [map_pow, map_one] at h
    simpa [ν₁, pow_two] using h
  have hnα : n * α * n⁻¹ = α⁻¹ := by
    have h : ((n₀, n₀) : A5 × A5) * (a₀, 1) * (n₀, n₀)⁻¹ = (a₀, 1)⁻¹ := by
      ext <;> simp [n₀_mul_a₀_mul_inv]
    have hh := congrArg σ h
    rw [map_mul, map_mul, map_inv, map_inv] at hh
    simpa [n, α] using hh
  have hnαi : ∀ i : ℕ, n * α ^ i = (α⁻¹) ^ i * n := by
    intro i
    have hconj : n * α ^ i * n⁻¹ = (α⁻¹) ^ i := by
      rw [← hnα, conj_pow]
    rw [← hconj]
    group
  have hn_apply : ∀ (i : ℕ) (z : V), n ((α ^ i) z) = ((α⁻¹) ^ i) (n z) := by
    intro i z
    have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e z) (hnαi i)
    simpa only [LinearEquiv.mul_apply] using h
  have hnn : ∀ z : V, n (n z) = z := by
    intro z
    have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e z) hn2
    rw [LinearEquiv.mul_apply] at h
    simpa only [LinearEquiv.one_eq_refl, LinearEquiv.refl_apply] using h
  have hnFp : ∀ x ∈ Fp, n x ∈ Fp := by
    intro x hx
    have h2 : ν₂ x ∈ Fm := (hE.nu₂_mem).1 x hx
    have h1 : ν₁ (ν₂ x) ∈ Fp := (hE.nu₁_mem).2 (ν₂ x) h2
    rwa [hn_eq, LinearEquiv.mul_apply]
  have huFp : ∀ x ∈ Fp, u x ∈ Fp := by
    intro x hx
    rw [hE.mem_plus] at hx ⊢
    change (σ (a₀ ^ (5 - c), a₀)) (u x) = u x
    have happ := congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) (hu (a₀ ^ (5 - c), a₀))
    simp only [LinearEquiv.mul_apply] at happ
    rw [← happ, hx]
  have h_comm_lm : (↑u : V →ₗ[ZMod 2] V) * γ = γ * (↑u : V →ₗ[ZMod 2] V) := by
    change (↑u : V →ₗ[ZMod 2] V) * (↑α : V →ₗ[ZMod 2] V)
      = (↑α : V →ₗ[ZMod 2] V) * (↑u : V →ₗ[ZMod 2] V)
    rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hu (a₀, 1)]
  have hαFp : ∀ x ∈ Fp, γ x ∈ Fp := by
    simpa [γ, α] using hE.alpha_mem.1
  have hfixFp : ∀ x ∈ Fp, γ x = x → x = 0 := by
    intro x hx hxy
    exact StdHyp.fixedFree_left hS orderOf_a₀ x (by simpa [γ, α] using hxy)
  obtain ⟨cf, hcf⟩ :=
    exists_coeffs γ (↑u : V →ₗ[ZMod 2] V) hγ5 h_comm_lm Fp hαFp hfixFp hE.finrank_plus huFp
  let pfun : V →ₗ[ZMod 2] V := ∑ i : Fin 5, cf i • (γ ^ (i : ℕ))
  let ptilde : V →ₗ[ZMod 2] V := ∑ i : Fin 5, cf i • (γinv ^ (i : ℕ))
  have hpfun_apply : ∀ z : V, pfun z = ∑ i : Fin 5, cf i • (γ ^ (i : ℕ)) z := by
    intro z
    simp only [pfun, LinearMap.sum_apply, LinearMap.smul_apply]
  have hptilde_apply : ∀ z : V, ptilde z = ∑ i : Fin 5, cf i • (γinv ^ (i : ℕ)) z := by
    intro z
    simp only [ptilde, LinearMap.sum_apply, LinearMap.smul_apply]
  have hpfun_apply_α : ∀ z : V, pfun z = ∑ i : Fin 5, cf i • (α ^ (i : ℕ)) z := by
    intro z
    rw [hpfun_apply z]
    apply Finset.sum_congr rfl
    intro i _
    rw [hγpow (i : ℕ)]
    rfl
  have hptilde_apply_α : ∀ z : V, ptilde z = ∑ i : Fin 5, cf i • ((α⁻¹) ^ (i : ℕ)) z := by
    intro z
    rw [hptilde_apply z]
    apply Finset.sum_congr rfl
    intro i _
    rw [hγinvpow (i : ℕ)]
    rfl
  have hcf' : ∀ x ∈ Fp, u x = pfun x := by
    intro x hx
    change (↑u : V →ₗ[ZMod 2] V) x = pfun x
    rw [hcf x hx, hpfun_apply x]
  have adj : ∀ g x y, B (σ g x) y = B x ((σ g)⁻¹ y) := by
    intro g x y
    have h := hBσ g x ((σ g)⁻¹ y)
    simpa using h
  have hadjbase : ∀ z y, B (γ z) y = B z (γinv y) := by
    intro z y
    have h := adj (a₀, 1) z y
    simpa [γ, γinv, α] using h
  have hadjpow : ∀ (i : ℕ) (x y : V), B ((γ ^ i) x) y = B x ((γinv ^ i) y) := by
    intro i
    induction i with
    | zero => intro x y; simp
    | succ i ih =>
        intro x y
        rw [pow_succ', Module.End.mul_apply, hadjbase, ih, pow_succ, Module.End.mul_apply]
  have hadjp : ∀ x y : V, B (pfun x) y = B x (ptilde y) := by
    intro x y
    rw [hpfun_apply x, hptilde_apply y]
    have hL : B (∑ i : Fin 5, cf i • (γ ^ (i : ℕ)) x) y
        = ∑ i : Fin 5, cf i • B ((γ ^ (i : ℕ)) x) y := by
      rw [map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, LinearMap.smul_apply]
    have hR : B x (∑ i : Fin 5, cf i • (γinv ^ (i : ℕ)) y)
        = ∑ i : Fin 5, cf i • B x ((γinv ^ (i : ℕ)) y) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
    rw [hL, hR]
    apply Finset.sum_congr rfl
    intro i _
    rw [hadjpow (i : ℕ) x y]
  have hpn_apply : ∀ z : V, n (pfun z) = ptilde (n z) := by
    intro z
    rw [hpfun_apply_α z, hptilde_apply_α (n z)]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hn_apply (i : ℕ) z]
  have hpn_eq : ∀ x ∈ Fp, pfun (n x) = ptilde (n x) := by
    intro x hx
    have hnx : n x ∈ Fp := hnFp x hx
    have hu_nx : u (n x) = n (u x) := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e x) (hu (n₀, n₀))
      simpa only [LinearEquiv.mul_apply] using h
    calc pfun (n x) = u (n x) := (hcf' (n x) hnx).symm
      _ = n (u x) := hu_nx
      _ = n (pfun x) := by rw [hcf' x hx]
      _ = ptilde (n x) := hpn_apply x
  have hp_eq : ∀ y ∈ Fp, pfun y = ptilde y := by
    intro y hy
    have hny : n y ∈ Fp := hnFp y hy
    have h := hpn_eq (n y) hny
    rwa [hnn y] at h
  have hstep3 : ∀ x ∈ Fp, ∀ y ∈ Fp, B x (u (u y)) = B x y := by
    intro x hx y hy
    have huy : u y ∈ Fp := huFp y hy
    have hchain : B x y = B x (u (u y)) := by
      calc B x y = B (u x) (u y) := (hBu x y).symm
        _ = B (pfun x) (u y) := by rw [hcf' x hx]
        _ = B x (ptilde (u y)) := hadjp x (u y)
        _ = B x (pfun (u y)) := by rw [← hp_eq (u y) huy]
        _ = B x (u (u y)) := by rw [hcf' (u y) huy]
    exact hchain.symm
  have horth : ∀ x ∈ Fp, ∀ y ∈ Fp, B x (u (u y) - y) = 0 := by
    intro x hx y hy
    have h := hstep3 x hx y hy
    rw [map_sub, h, sub_self]
  have huu : ∀ y ∈ Fp, u (u y) = y := by
    intro y hy
    have hmem : u (u y) - y ∈ Fp := Fp.sub_mem (huFp (u y) (huFp y hy)) hy
    have hz := EigenData.bilin_right_nondegenerate_plus hS hE B hB hBσ (u (u y) - y) hmem
    exact sub_eq_zero.mp (hz (fun x hx => horth x hx y hy))
  let N : V →ₗ[ZMod 2] V := (↑u : V →ₗ[ZMod 2] V) - 1
  have hNU : ∀ v ∈ Fp, N v ∈ Fp := by
    intro v hv
    have hv' : N v = (↑u : V →ₗ[ZMod 2] V) v - v := by simp [N]
    rw [hv']
    exact Fp.sub_mem (huFp v hv) hv
  have hcN : ∀ v ∈ Fp, N (γ v) = γ (N v) := by
    intro v _
    have hcomm := congrArg (fun f : V →ₗ[ZMod 2] V => f v) h_comm_lm
    simp only [Module.End.mul_apply] at hcomm
    simp only [N, LinearMap.sub_apply, Module.End.one_apply]
    rw [hcomm, map_sub]
  have hN2 : ∀ v ∈ Fp, N (N v) = 0 := by
    intro v hv
    have hvv : u (u v) = v := huu v hv
    simp only [N, LinearMap.sub_apply, Module.End.one_apply]
    change u (u v - v) - (u v - v) = 0
    rw [map_sub, hvv]
    exact sub_sub_self_sub_self v (u v)
  have hNzero : ∀ v ∈ Fp, N v = 0 :=
    eq_zero_of_sq_eq_zero γ N hγ5 Fp hαFp hfixFp hE.finrank_plus hNU hcN hN2
  have huFp_id : ∀ v ∈ Fp, u v = v := by
    intro v hv
    have h := hNzero v hv
    have h2 : (↑u : V →ₗ[ZMod 2] V) v - v = 0 := by
      simpa only [N, LinearMap.sub_apply, Module.End.one_apply] using h
    exact sub_eq_zero.mp h2
  have huFm_id : ∀ y ∈ Fm, u y = y := by
    intro y hy
    have hνy : ν₁ y ∈ Fp := (hE.nu₁_mem).2 y hy
    have hν2 : ν₁ (ν₁ y) = y := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e y) hν12
      rw [LinearEquiv.mul_apply] at h
      simpa only [LinearEquiv.one_eq_refl, LinearEquiv.refl_apply] using h
    have huν : u (ν₁ y) = ν₁ (u y) := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e y) (hu (n₀, 1))
      simpa only [LinearEquiv.mul_apply, ν₁] using h
    have hfix : ν₁ (u y) = ν₁ y := by
      rw [← huν, huFp_id (ν₁ y) hνy]
    exact ν₁.injective hfix
  have hu_id : (↑u : V →ₗ[ZMod 2] V) = 1 := by
    ext y
    have hy : y ∈ Fp ⊔ Fm := by
      rw [hE.isCompl.sup_eq_top]
      exact Submodule.mem_top
    rw [Submodule.mem_sup] at hy
    obtain ⟨a, ha, b, hb, hab⟩ := hy
    rw [← hab]
    change u (a + b) = a + b
    rw [map_add, huFp_id a ha, huFm_id b hb]
  refine LinearEquiv.ext fun y => ?_
  have h := congrArg (fun f : V →ₗ[ZMod 2] V => f y) hu_id
  simpa using h

end CFSG.EvenSporadicStandard.HNRecog.Swap
