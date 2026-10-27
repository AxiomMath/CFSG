module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Module Submodule

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem one_add_pow_of_sq_eq_zero {R : Type*} [Ring R] (N : R) (hN : N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + n • N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_smul, one_smul]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, hN, smul_zero]
    abel

theorem finrank_ge_of_minimal [Finite k] [Module.Finite k V] {p : ℕ} [Fact p.Prime]
    (hp : (p : k) ≠ 0) {G : Type*} [Group G] (ρ : G →* Module.End k V) {a b c : G}
    (hcc : ∀ g : G, c * g = g * c) (hrel : c * (b * a) = a * b) (hcp : c ^ p = 1)
    (hmin : ∀ W : Submodule k V, (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) → (∃ v ∈ W, ρ c v ≠ v) →
      W = ⊤)
    (hρc : ∃ v : V, ρ c v ≠ v) : p ≤ finrank k V := by
  classical
  haveI : Finite V := Module.finite_of_finite k
  obtain ⟨v₀, hv₀⟩ := hρc
  haveI : Nontrivial V := ⟨⟨v₀, 0, fun h => hv₀ (by rw [h, map_zero])⟩⟩
  let K : Subalgebra k (Module.End k V) := Algebra.adjoin k {ρ c}
  have hKcomm : ∀ T ∈ K, ∀ g : G, T * ρ g = ρ g * T := by
    intro T hT g
    induction hT using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [← map_mul, ← map_mul, hcc]
    | algebraMap r => exact Algebra.commutes r (ρ g)
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  have hinj : ∀ T ∈ K, T ≠ 0 → Function.Injective T := by
    intro T hT hT0
    by_contra hni
    have hker_top : LinearMap.ker T ≠ ⊤ := fun h => hT0 (LinearMap.ker_eq_top.mp h)
    have hker_inv : ∀ g : G, ∀ v ∈ LinearMap.ker T, ρ g v ∈ LinearMap.ker T := by
      intro g v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have := congrArg (fun S : Module.End k V => S v) (hKcomm T hT g)
      simp only [Module.End.mul_apply] at this
      rw [this, hv, map_zero]
    have hker_c : ∀ v ∈ LinearMap.ker T, ρ c v = v := by
      by_contra h
      push Not at h
      exact hker_top (hmin _ hker_inv h)
    have hrange_top : LinearMap.range T ≠ ⊤ := by
      intro h
      exact hni ((LinearMap.injective_iff_surjective).mpr (LinearMap.range_eq_top.mp h))
    have hrange_inv : ∀ g : G, ∀ v ∈ LinearMap.range T, ρ g v ∈ LinearMap.range T := by
      rintro g _ ⟨u, rfl⟩
      refine ⟨ρ g u, ?_⟩
      have := congrArg (fun S : Module.End k V => S u) (hKcomm T hT g)
      simpa only [Module.End.mul_apply] using this
    have hrange_c : ∀ v ∈ LinearMap.range T, ρ c v = v := by
      by_contra h
      push Not at h
      exact hrange_top (hmin _ hrange_inv h)
    set N : Module.End k V := ρ c - 1 with hNdef
    have hNapply : ∀ v, N v = ρ c v - v := fun v => by simp [hNdef]
    have hNN : N * N = 0 := by
      ext v
      have h1 : T (N v) = N (T v) := by
        have := congrArg (fun S : Module.End k V => S v) (hKcomm T hT c)
        simp only [Module.End.mul_apply] at this
        rw [hNapply, hNapply, map_sub, this]
      have h2 : N (T v) = 0 := by
        rw [hNapply, hrange_c (T v) ⟨v, rfl⟩, sub_self]
      have h3 : N v ∈ LinearMap.ker T := by
        rw [LinearMap.mem_ker, h1, h2]
      simp only [Module.End.mul_apply, LinearMap.zero_apply]
      rw [hNapply (N v), hker_c _ h3, sub_self]
    have hpow : (1 + N) ^ p = 1 + p • N := one_add_pow_of_sq_eq_zero N hNN p
    have h1N : (1 + N) = ρ c := by simp [hNdef]
    rw [h1N, ← map_pow, hcp, map_one] at hpow
    have hpN : p • N = 0 := by simpa using hpow
    have hN0 : N = 0 := by
      have : (p : k) • N = 0 := by rwa [Nat.cast_smul_eq_nsmul]
      exact (smul_eq_zero.mp this).resolve_left hp
    exact hv₀ (by
      have := congrArg (fun S : Module.End k V => S v₀) (sub_eq_zero.mp hN0)
      simpa using this)
  haveI : Finite (Module.End k V) :=
    Finite.of_injective (fun f : Module.End k V => (f : V → V)) DFunLike.coe_injective
  haveI : Finite K := Finite.of_injective (fun T : K => (T : Module.End k V)) Subtype.val_injective
  letI : CommRing K := Algebra.adjoinCommRingOfComm k (by simp [Set.Pairwise])
  haveI : NoZeroDivisors K := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨hx, hy⟩ := h
    have hx' : (x : Module.End k V) ≠ 0 := fun h => hx (Subtype.ext h)
    have hinjx := hinj x x.2 hx'
    have hxy' : (x : Module.End k V) * (y : Module.End k V) = 0 := congrArg Subtype.val hxy
    have : (y : Module.End k V) = 0 := by
      ext v
      apply hinjx
      have := congrArg (fun S : Module.End k V => S v) hxy'
      simpa using this
    exact hy (Subtype.ext this)⟩
  haveI : IsDomain K := NoZeroDivisors.to_isDomain K
  haveI : Fintype K := Fintype.ofFinite K
  letI : Field K := Fintype.fieldOfDomain K
  let gK : G → (V →ₗ[K] V) := fun g =>
    { toFun := fun v => ρ g v
      map_add' := fun u v => map_add (ρ g) u v
      map_smul' := fun T v => by
        have := congrArg (fun S : Module.End k V => S v) (hKcomm T T.2 g)
        simp only [Module.End.mul_apply] at this
        exact this.symm }
  have hgapply : ∀ g v, gK g v = ρ g v := fun g v => rfl
  have hgmul : ∀ g h, gK (g * h) = gK g ∘ₗ gK h := fun g h => by
    ext v
    simp only [hgapply, map_mul, Module.End.mul_apply, LinearMap.comp_apply]
  have hgone : gK 1 = LinearMap.id := by
    ext v
    simp [hgapply]
  have hdet_ne : ∀ g, LinearMap.det (gK g) ≠ 0 := fun g h => by
    have h1 := LinearMap.det_comp (gK g) (gK g⁻¹)
    rw [← hgmul, mul_inv_cancel, hgone, LinearMap.det_id, h, zero_mul] at h1
    exact one_ne_zero h1
  have hrelK : gK c ∘ₗ (gK b ∘ₗ gK a) = gK a ∘ₗ gK b := by
    rw [← hgmul, ← hgmul, ← hgmul, hrel]
  let γ : K := ⟨ρ c, Algebra.subset_adjoin rfl⟩
  have hγ : gK c = γ • (LinearMap.id : V →ₗ[K] V) := by
    ext v
    rfl
  have hdet1 : LinearMap.det (gK c) = 1 := by
    have h1 := congrArg LinearMap.det hrelK
    rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_comp] at h1
    have h2 : LinearMap.det (gK a) * LinearMap.det (gK b) ≠ 0 :=
      mul_ne_zero (hdet_ne a) (hdet_ne b)
    apply mul_right_cancel₀ h2
    calc LinearMap.det (gK c) * (LinearMap.det (gK a) * LinearMap.det (gK b))
        = LinearMap.det (gK c) * (LinearMap.det (gK b) * LinearMap.det (gK a)) := by ring
      _ = LinearMap.det (gK a) * LinearMap.det (gK b) := h1
      _ = 1 * (LinearMap.det (gK a) * LinearMap.det (gK b)) := (one_mul _).symm
  have hγn : γ ^ finrank K V = 1 := by
    have h := hdet1
    rw [hγ, LinearMap.det_smul, LinearMap.det_id, mul_one] at h
    exact h
  have hγp : γ ^ p = 1 := by
    apply Subtype.ext
    simp [γ, ← map_pow, hcp]
  have hγ1 : γ ≠ 1 := fun h => hv₀ (by
    have := congrArg (fun T : K => (T : Module.End k V) v₀) h
    simpa [γ] using this)
  have hord : orderOf γ = p := orderOf_eq_prime hγp hγ1
  have hdvd : p ∣ finrank K V := hord ▸ orderOf_dvd_of_pow_eq_one hγn
  have hpos : 0 < finrank K V := Module.finrank_pos
  have hle : p ≤ finrank K V := Nat.le_of_dvd hpos hdvd
  have htower := Module.finrank_mul_finrank k K V
  have hkpos : 0 < finrank k K := Module.finrank_pos
  calc p ≤ finrank K V := hle
    _ ≤ finrank k K * finrank K V := Nat.le_mul_of_pos_left _ hkpos
    _ = finrank k V := htower

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
