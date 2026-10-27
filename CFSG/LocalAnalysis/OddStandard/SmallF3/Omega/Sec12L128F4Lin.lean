module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Polynomial

theorem sec128_F4_central_three
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (hW : Nat.card W = 2 ^ 8)
    {Z : Type} [Group Z] (hZ : _root_.commutator Z = ⊤) (ρ : Z →* (W ≃ₗ[ZMod 2] W))
    (c : Z) (hcen : ∀ z : Z, z * c = c * z) (hc3 : ρ c ^ 3 = 1) (hc1 : ρ c ≠ 1)
    (hfpf : ∀ w : W, ρ c w = w → w = 0) : False := by
  classical
  have h3 : (ρ c) * (ρ c) * (ρ c) = 1 := by
    simpa [pow_succ, pow_one] using hc3
  have hfun : ∀ w : W, ρ c (ρ c (ρ c w)) = w := by
    intro w
    have h := congrArg (fun e : W ≃ₗ[ZMod 2] W => e w) h3
    simpa [LinearEquiv.mul_apply] using h
  have hq : ∀ w : W, ρ c (ρ c w) + ρ c w + w = 0 := by
    intro w
    exact hfpf _ (by simp only [map_add, hfun]; abel)
  let p : (ZMod 2)[X] := X ^ 2 + X + 1
  have hp_natDegree : p.natDegree = 2 := by
    change (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2
    compute_degree!
  have hp_irred : Irreducible p := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [hp_natDegree]; decide
    · intro x
      simp only [p, IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
      revert x
      decide
  haveI : Fact (Irreducible p) := ⟨hp_irred⟩
  have hp_ne : p ≠ 0 := hp_irred.ne_zero
  let K := AdjoinRoot p
  have hK_finrank : Module.finrank (ZMod 2) K = 2 := by
    change Module.finrank (ZMod 2) (AdjoinRoot p) = 2
    rw [(AdjoinRoot.powerBasis hp_ne).finrank, AdjoinRoot.powerBasis_dim hp_ne, hp_natDegree]
  have hK_card : Nat.card K = 4 := by
    haveI : Module.Finite (ZMod 2) K := (AdjoinRoot.powerBasis hp_ne).finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K), Nat.card_zmod, hK_finrank]
    decide
  let A := Module.End (ZMod 2) W
  let x : A := (ρ c : W →ₗ[ZMod 2] W)
  let i : ZMod 2 →+* A := algebraMap (ZMod 2) A
  have hφ : p.eval₂ i x = 0 := by
    have hval : p.eval₂ i x = x ^ 2 + x + 1 := by
      simp only [p, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one]
    rw [hval]
    ext w
    simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply]
    exact hq w
  have haeval : aeval x p = 0 := by
    rw [Polynomial.aeval_def]
    exact hφ
  let φ : K →+* A := Ideal.Quotient.lift (Ideal.span {p}) (aeval x).toRingHom (by
    intro g hg
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    rw [map_mul]
    change aeval x q * aeval x p = 0
    rw [haeval, mul_zero])
  letI : Module K W := Module.compHom W φ
  have hφ_mk : ∀ g : (ZMod 2)[X], φ (AdjoinRoot.mk p g) = g.eval₂ i x := by
    intro g
    rfl
  have hφ_root : φ (AdjoinRoot.root p) = x := by
    change φ (AdjoinRoot.mk p X) = x
    rw [hφ_mk, Polynomial.eval₂_X]
  have hω : ∀ w : W, (AdjoinRoot.root p : K) • w = x w := by
    intro w
    change φ (AdjoinRoot.root p) w = x w
    rw [hφ_root]
  have hWfin : Module.finrank K W = 4 := by
    have h1 : Nat.card W = Nat.card K ^ Module.finrank K W := Module.natCard_eq_pow_finrank
    rw [hW, hK_card] at h1
    rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul] at h1
    have h2 : (8 : ℕ) = 2 * Module.finrank K W :=
      Nat.pow_right_injective (show 2 ≤ (2 : ℕ) by decide) h1
    have h3 : 2 * Module.finrank K W = 2 * 4 := by rw [← h2]
    exact Nat.mul_left_cancel (show 0 < (2 : ℕ) by decide) h3
  have hx_comm : ∀ z : Z, Commute x (ρ z : A) := by
    intro z
    have h : (ρ z : A) * x = x * (ρ z : A) := by
      have h' : (ρ z : W ≃ₗ[ZMod 2] W) * ρ c = ρ c * (ρ z : W ≃ₗ[ZMod 2] W) := by
        simpa using congrArg ρ (hcen z)
      simpa [x] using congrArg (fun e : W ≃ₗ[ZMod 2] W => (e : A)) h'
    exact h.symm
  have hcomm : ∀ z : Z, ∀ k : K, φ k * (ρ z : A) = (ρ z : A) * φ k := by
    intro z k
    have key : ∀ g : (ZMod 2)[X], g.eval₂ i x * (ρ z : A) = (ρ z : A) * g.eval₂ i x := by
      intro g
      induction g using Polynomial.induction_on' with
      | add p q hp hq =>
        simp only [Polynomial.eval₂_add, add_mul, mul_add, hp, hq]
      | monomial n a =>
        rw [Polynomial.eval₂_monomial]
        exact (Algebra.commute_algebraMap_left a (ρ z : A)).mul_left
          ((hx_comm z).pow_left n)
    induction k using AdjoinRoot.induction_on with
    | ih g =>
      rw [hφ_mk g]
      exact key g
  have hlin : ∀ z : Z, ∀ (k : K) (w : W), ρ z (k • w) = k • (ρ z w) := by
    intro z k w
    change (ρ z : A) (φ k w) = φ k ((ρ z : A) w)
    have h := congrArg (fun f : A => f w) (hcomm z k)
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    exact h.symm
  let lin (z : Z) : W →ₗ[K] W :=
    { toFun := fun w => ρ z w
      map_add' := fun a b => (ρ z).map_add a b
      map_smul' := fun k w => hlin z k w }
  let ρ' : Z →* (W ≃ₗ[K] W) :=
    { toFun := fun z =>
        LinearEquiv.mk (lin z) (fun w => (ρ z).symm w)
          (fun w => (ρ z).left_inv w) (fun w => (ρ z).right_inv w)
      map_one' := by
        apply LinearEquiv.ext
        intro w
        change ρ 1 w = w
        rw [map_one]
        rfl
      map_mul' := by
        intro a b
        apply LinearEquiv.ext
        intro w
        change ρ (a * b) w = ρ a (ρ b w)
        rw [map_mul]
        rfl }
  let δ : Z →* Kˣ := (LinearEquiv.det : (W ≃ₗ[K] W) →* Kˣ).comp ρ'
  have hker : _root_.commutator Z ≤ δ.ker := Abelianization.commutator_subset_ker δ
  have hδc : δ c = 1 := by
    have hmem : c ∈ δ.ker := by
      have : (⊤ : Subgroup Z) ≤ δ.ker := hZ ▸ hker
      exact this (Subgroup.mem_top c)
    simpa using hmem
  have hδc' : LinearEquiv.det (ρ' c) = 1 := by
    simpa [δ] using hδc
  have hdet : LinearMap.det (ρ' c : W →ₗ[K] W) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hδc'
    simpa [LinearEquiv.coe_det] using this
  have hρ'c_eq : (ρ' c : W →ₗ[K] W) =
      (AdjoinRoot.root p : K) • (LinearMap.id : W →ₗ[K] W) := by
    ext w
    rw [LinearMap.smul_apply, LinearMap.id_apply, hω w]
    rfl
  have hroot4 : (AdjoinRoot.root p : K) ^ 4 = 1 := by
    have h := hdet
    rw [hρ'c_eq, LinearMap.det_smul, LinearMap.det_id, mul_one, hWfin] at h
    exact h
  have hroot_sq : (AdjoinRoot.root p : K) ^ 2 + AdjoinRoot.root p + 1 = 0 := by
    have := AdjoinRoot.eval₂_root p
    simpa [p, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_one] using this
  have hroot3 : (AdjoinRoot.root p : K) ^ 3 = 1 := by
    have hfac : (AdjoinRoot.root p : K) ^ 3 - 1 = 0 := by
      have h : (AdjoinRoot.root p : K) ^ 3 - 1 =
          ((AdjoinRoot.root p : K) - 1) *
            ((AdjoinRoot.root p : K) ^ 2 + AdjoinRoot.root p + 1) := by
        ring
      rw [h, hroot_sq, mul_zero]
    exact sub_eq_zero.mp hfac
  have hroot_eq : (AdjoinRoot.root p : K) = 1 := by
    have h : (AdjoinRoot.root p : K) ^ 4 =
        (AdjoinRoot.root p : K) ^ 3 * AdjoinRoot.root p := by
      ring
    rw [h, hroot3, one_mul] at hroot4
    exact hroot4
  have hρc_one : ρ c = 1 := by
    have h : (ρ c : A) = 1 := by
      change x = 1
      rw [← hφ_root, hroot_eq, map_one]
    apply LinearEquiv.ext
    intro w
    have h' := congrArg (fun f : A => f w) h
    rw [Module.End.one_apply] at h'
    exact h'
  exact hc1 hρc_one

end CFSG.OddStandard.SmallF3.Omega
