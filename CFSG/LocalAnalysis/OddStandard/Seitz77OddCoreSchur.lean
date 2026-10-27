module

public import Mathlib.LinearAlgebra.Determinant

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.OddStandard.Seitz77

open Polynomial

theorem oddCore_irreducible_X_sq_add_X_add_one : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have h2 : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    rw [h2]
    decide
  · have key : ∀ x : ZMod 2, x ^ 2 + x + 1 ≠ 0 := by decide
    intro x hx
    apply key x
    simpa [IsRoot] using hx

theorem oddCore_commute_of_mem_adjoin {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (m t : Module.End (ZMod 2) U) (hmt : m * t = t * m)
    (a : Module.End (ZMod 2) U) (ha : a ∈ Algebra.adjoin (ZMod 2) {m}) : a * t = t * a := by
  have hle : Algebra.adjoin (ZMod 2) {m} ≤ Subalgebra.centralizer (ZMod 2) {t} := by
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hmt.symm
  exact ((Subalgebra.mem_centralizer_iff (ZMod 2)).mp (hle ha) t rfl).symm

theorem oddCore_injective_of_mem_adjoin_of_irreducible {U : Type*} [AddCommGroup U]
    [Module (ZMod 2) U] (m t : Module.End (ZMod 2) U) (hmt : m * t = t * m)
    (hirr : ∀ Y : Submodule (ZMod 2) U, (∀ y ∈ Y, t y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (a : Module.End (ZMod 2) U) (ha : a ∈ Algebra.adjoin (ZMod 2) {m}) (ha0 : a ≠ 0) :
    Function.Injective a := by
  have hat := oddCore_commute_of_mem_adjoin m t hmt a ha
  have hinv : ∀ y ∈ LinearMap.ker a, t y ∈ LinearMap.ker a := by
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    have := congrArg (fun f : Module.End (ZMod 2) U => f y) hat
    simp only [Module.End.mul_apply] at this
    rw [this, hy, map_zero]
  rcases hirr _ hinv with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact absurd (LinearMap.ker_eq_top.mp h) ha0

theorem oddCore_injective_of_mem_adjoin_of_aeval {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (m : Module.End (ZMod 2) U) (f : (ZMod 2)[X]) (hf : Irreducible f) (hroot : aeval m f = 0)
    (a : Module.End (ZMod 2) U) (ha : a ∈ Algebra.adjoin (ZMod 2) {m}) (ha0 : a ≠ 0) :
    Function.Injective a := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨q, rfl⟩ := ha
  have hfq : ¬ f ∣ q := by
    rintro ⟨r, rfl⟩
    apply ha0
    simp [hroot]
  obtain ⟨u, v, huv⟩ := (hf.coprime_iff_not_dvd.mpr hfq)
  have h1 : aeval m v * aeval m q = 1 := by
    have := congrArg (aeval m) huv
    simpa [hroot] using this
  exact Function.LeftInverse.injective (g := fun x => aeval m v x) (fun x => by
    have := congrArg (fun f : Module.End (ZMod 2) U => f x) h1
    simpa using this)

theorem oddCore_exists_pow_eq_one_of_central {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Finite U] [Nontrivial U] {G : Type*} [Group G] (θ : G →* Module.End (ZMod 2) U)
    (hperf : commutator G = ⊤) (μ : G) (hμ : ∀ g, g * μ = μ * g)
    (hdom : ∀ a ∈ Algebra.adjoin (ZMod 2) {θ μ}, a ≠ 0 → Function.Injective a) :
    ∃ e k : ℕ, e * k = Module.finrank (ZMod 2) U ∧ θ μ ^ k = 1 := by
  classical
  set m := θ μ with hm
  set A := Algebra.adjoin (ZMod 2) {m} with hA
  have hcomm : IsMulCommutative A := Algebra.isMulCommutative_adjoin (ZMod 2) (by simp)
  have hfin : Finite (Module.End (ZMod 2) U) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) U => (f : U → U)) DFunLike.coe_injective
  have hfinA : Finite A := inferInstance
  have hnt : Nontrivial A := inferInstance
  have hnzd : NoZeroDivisors A := by
    refine ⟨fun {a b} hab => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      have hinj : Function.Injective (a : Module.End (ZMod 2) U) :=
        hdom a a.2 (fun h => ha (Subtype.ext h))
      apply Subtype.ext
      ext u
      apply hinj
      have := congrArg (fun x : A => (x : Module.End (ZMod 2) U) u) hab
      simpa using this
  have : IsDomain A := NoZeroDivisors.to_isDomain A
  have hfield : IsField A := Finite.isDomain_to_isField A
  let _ : Field A := hfield.toField
  have hcent : ∀ g : G, ∀ a : A, (a : Module.End (ZMod 2) U) * θ g = θ g * a := by
    intro g a
    have hle : A ≤ Subalgebra.centralizer (ZMod 2) {θ g} := by
      apply Algebra.adjoin_le
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [← map_mul, ← map_mul, hμ]
    have := (Subalgebra.mem_centralizer_iff (ZMod 2)).mp (hle a.2) (θ g) rfl
    exact this.symm
  let Φ : G →* (U →ₗ[A] U) :=
    { toFun := fun g =>
        { toFun := fun u => θ g u
          map_add' := fun u v => map_add _ u v
          map_smul' := fun a u => by
            have := congrArg (fun f : Module.End (ZMod 2) U => f u) (hcent g a)
            simp only [Module.End.mul_apply] at this
            exact this.symm }
      map_one' := by ext u; simp
      map_mul' := fun g h => by ext u; simp }
  let δ : G →* Aˣ := (LinearMap.det.comp Φ).toHomUnits
  have hδ : ∀ g : G, δ g = 1 := by
    intro g
    have h1 : commutator G ≤ δ.ker := Abelianization.commutator_subset_ker δ
    rw [hperf] at h1
    exact h1 (Subgroup.mem_top g)
  have hdet : LinearMap.det (Φ μ) = 1 := by
    have := congrArg Units.val (hδ μ)
    simpa [δ] using this
  let c : A := ⟨m, Algebra.subset_adjoin rfl⟩
  have hΦμ : Φ μ = c • (LinearMap.id : U →ₗ[A] U) := by
    ext u
    rfl
  rw [hΦμ, LinearMap.det_smul, LinearMap.det_id, mul_one] at hdet
  refine ⟨Module.finrank (ZMod 2) A, Module.finrank A U,
    Module.finrank_mul_finrank (ZMod 2) A U, ?_⟩
  have hpow : ∀ n : ℕ, ∀ u : U, (m ^ n) u = (c ^ n) • u := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ, Module.End.mul_apply, pow_succ, mul_smul, ← ih]
      rfl
  ext u
  rw [hpow, hdet, one_smul]
  simp

theorem oddCore_eq_one_of_central_odd {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    [Nontrivial U] {G : Type*} [Group G] (θ : G →* Module.End (ZMod 2) U)
    (hperf : commutator G = ⊤) (μ : G) (hμ : ∀ g, g * μ = μ * g)
    (hdom : ∀ a ∈ Algebra.adjoin (ZMod 2) {θ μ}, a ≠ 0 → Function.Injective a)
    (j : ℕ) (hj : Module.finrank (ZMod 2) U = 2 ^ j) (hodd : Odd (orderOf μ)) : θ μ = 1 := by
  obtain ⟨e, k, hek, hk⟩ := oddCore_exists_pow_eq_one_of_central θ hperf μ hμ hdom
  have hkd : k ∣ 2 ^ j := ⟨e, by rw [← hj, ← hek, mul_comm]⟩
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hkd
  have h1 : orderOf (θ μ) ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (θ μ) ∣ orderOf μ := orderOf_map_dvd θ μ
  have hcop : Nat.Coprime (orderOf μ) (2 ^ i) :=
    Nat.Coprime.pow_right i hodd.coprime_two_right
  have h3 : orderOf (θ μ) ∣ Nat.gcd (orderOf μ) (2 ^ i) := Nat.dvd_gcd h2 h1
  rw [hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

end CFSG.OddStandard.Seitz77
