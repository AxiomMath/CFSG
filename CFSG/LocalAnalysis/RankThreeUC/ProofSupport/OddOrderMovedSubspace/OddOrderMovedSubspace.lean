module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddOrderMovedSubspace

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

abbrev dd (t : W ≃ₗ[F] W) : W →ₗ[F] W := t.toLinearMap - LinearMap.id

abbrev moved (t : W ≃ₗ[F] W) : Submodule F W :=
  LinearMap.range (t.toLinearMap - LinearMap.id)

abbrev fixed (t : W ≃ₗ[F] W) : Submodule F W :=
  LinearMap.ker (t.toLinearMap - LinearMap.id)

private lemma toLM_pow (t : W ≃ₗ[F] W) (r : ℕ) (ht : t ^ r = 1) :
    (t.toLinearMap) ^ r = 1 := by
  have := map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := W)) t r
  rw [ht, map_one] at this
  exact this.symm

private lemma pow_sub_one_apply (t : W ≃ₗ[F] W) (i : ℕ) (x : W) :
    ((t.toLinearMap) ^ i) x - x =
      dd t (∑ j ∈ Finset.range i, ((t.toLinearMap) ^ j) x) := by
  have h := mul_geom_sum (t.toLinearMap) i
  have := congrArg (fun f : W →ₗ[F] W => f x) h
  simpa [LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply,
    Module.End.one_eq_id] using this.symm

theorem complementary {r : ℕ} (hr : Odd r) (hrF : (r : F) ≠ 0) (t : W ≃ₗ[F] W)
    (ht : t ^ r = 1) : IsCompl (fixed t) (moved t) := by
  have hT := toLM_pow t r ht
  set T := t.toLinearMap with hTdef
  set S : W →ₗ[F] W := ∑ i ∈ Finset.range r, T ^ i with hS
  have h1 : S * dd t = 0 := by
    have := geom_sum_mul T r
    rw [hT] at this
    simpa [Module.End.one_eq_id] using this
  have h2 : dd t * S = 0 := by
    have := mul_geom_sum T r
    rw [hT] at this
    simpa [Module.End.one_eq_id] using this
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxC hxM
    obtain ⟨w, rfl⟩ := hxM
    have hfix : ∀ i : ℕ, (T ^ i) (dd t w) = dd t w := by
      intro i
      induction i with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        have h3 := LinearMap.mem_ker.mp hxC
        have h4 : t (t w) - t w = t w - w := by simpa [sub_eq_zero] using h3
        show t (t w - w) = t w - w
        rw [map_sub]
        exact h4
    have hSx : S (dd t w) = (r : F) • dd t w := by
      rw [hS, LinearMap.sum_apply]
      simp only [hfix, Finset.sum_const, Finset.card_range]
      rw [Nat.cast_smul_eq_nsmul]
    have h0 : S (dd t w) = 0 := by
      have := congrArg (fun f : W →ₗ[F] W => f w) h1
      simpa [Module.End.mul_apply] using this
    rw [h0] at hSx
    exact (smul_eq_zero.mp hSx.symm).resolve_left hrF
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = ((r : F)⁻¹ • S x) + (r : F)⁻¹ • ((r : F) • x - S x) := by
      rw [smul_sub, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hrF, one_smul]
      abel
    rw [hx]
    refine Submodule.add_mem_sup ?_ ?_
    · refine Submodule.smul_mem _ _ ?_
      rw [LinearMap.mem_ker]
      have := congrArg (fun f : W →ₗ[F] W => f x) h2
      simpa [Module.End.mul_apply] using this
    · refine Submodule.smul_mem _ _ ?_
      have : (r : F) • x - S x = ∑ i ∈ Finset.range r, (x - (T ^ i) x) := by
        rw [hS, LinearMap.sum_apply, Finset.sum_sub_distrib]
        simp [Nat.cast_smul_eq_nsmul]
      rw [this]
      refine Submodule.sum_mem _ fun i _ => ?_
      have := pow_sub_one_apply t i x
      rw [← neg_sub, this, ← map_neg]
      exact ⟨_, rfl⟩

theorem diff_inverse_injective_on_moved {r : ℕ} (hr : Odd r) (hrF : (r : F) ≠ 0)
    (t : W ≃ₗ[F] W) (ht : t ^ r = 1) :
    Function.Injective (fun x : moved t => t x - t.symm x) := by
  have hc := complementary hr hrF t ht
  intro x y hxy
  have hz : t ((x - y : moved t) : W) - t.symm ((x - y : moved t) : W) = 0 := by
    have := sub_eq_zero.mpr hxy
    simp only [Submodule.coe_sub, map_sub] at this ⊢
    rw [← this]
    abel
  set z : W := ((x - y : moved t) : W) with hzdef
  have hzM : z ∈ moved t := (x - y : moved t).2
  have h2 : t (t z) = z := by
    have : t z = t.symm z := sub_eq_zero.mp hz
    rw [this]; simp
  have hk : ∀ k : ℕ, (t ^ (2 * k)) z = z := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have : t ^ (2 * (n + 1)) = t ^ (2 * n) * (t * t) := by
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pow_succ, pow_succ, mul_assoc]
      rw [this, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h2, ih]
  obtain ⟨k, hk'⟩ := hr
  have htz : t z = z := by
    have h := hk k
    have : t ^ r = t * t ^ (2 * k) := by rw [hk', pow_succ']
    have h5 : (t ^ r) z = z := by rw [ht]; rfl
    rw [this, LinearEquiv.mul_apply, h] at h5
    exact h5
  have hzC : z ∈ fixed t := by
    rw [LinearMap.mem_ker]
    simp [htz]
  have := (Submodule.disjoint_def.mp hc.disjoint) z hzC hzM
  exact sub_eq_zero.mp (Subtype.ext this) |> fun h => h

theorem diff_mem_moved (t : W ≃ₗ[F] W) (x : moved t) : t x - t.symm x ∈ moved t := by
  refine ⟨(x : W) + t.symm x, ?_⟩
  show (t (x + t.symm x) - (x + t.symm x)) = _
  simp only [map_add, LinearEquiv.apply_symm_apply]
  abel

@[expose] def differenceEnd (t : W ≃ₗ[F] W) : moved t →ₗ[F] moved t where
  toFun x := ⟨t x - t.symm x, diff_mem_moved t x⟩
  map_add' x y := by ext; simp only [Submodule.coe_add, map_add]; abel
  map_smul' c x := by ext; simp [smul_sub]

@[expose] noncomputable def differenceAut {r : ℕ} (hr : Odd r) (hrF : (r : F) ≠ 0) (t : W ≃ₗ[F] W)
    (ht : t ^ r = 1) : moved t ≃ₗ[F] moved t :=
  LinearEquiv.ofInjectiveEndo (differenceEnd t) fun x y h =>
    diff_inverse_injective_on_moved hr hrF t ht (congrArg Subtype.val h)

theorem differenceAut_apply {r : ℕ} (hr : Odd r) (hrF : (r : F) ≠ 0) (t : W ≃ₗ[F] W)
    (ht : t ^ r = 1) (x : moved t) :
    ((differenceAut hr hrF t ht x : moved t) : W) = t x - t.symm x := rfl

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddOrderMovedSubspace
