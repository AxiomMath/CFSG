module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Module

variable {K : Type*} [Field K]

section Hom

variable {W₁ W₂ W₃ : Type*} [AddCommGroup W₁] [Module K W₁] [AddCommGroup W₂] [Module K W₂]
  [AddCommGroup W₃] [Module K W₃]

@[expose] def homN (N₁ : Module.End K W₁) (N₂ : Module.End K W₂) :
    Submodule K (W₁ →ₗ[K] W₂) where
  carrier := {φ | φ ∘ₗ N₁ = N₂ ∘ₗ φ}
  add_mem' {φ ψ} hφ hψ := by
    change (φ + ψ) ∘ₗ N₁ = N₂ ∘ₗ (φ + ψ)
    rw [LinearMap.add_comp, LinearMap.comp_add, show φ ∘ₗ N₁ = N₂ ∘ₗ φ from hφ,
      show ψ ∘ₗ N₁ = N₂ ∘ₗ ψ from hψ]
  zero_mem' := by
    change (0 : W₁ →ₗ[K] W₂) ∘ₗ N₁ = N₂ ∘ₗ 0
    rw [LinearMap.zero_comp, LinearMap.comp_zero]
  smul_mem' a φ hφ := by
    change (a • φ) ∘ₗ N₁ = N₂ ∘ₗ (a • φ)
    rw [LinearMap.smul_comp, LinearMap.comp_smul, show φ ∘ₗ N₁ = N₂ ∘ₗ φ from hφ]

theorem mem_homN {N₁ : Module.End K W₁} {N₂ : Module.End K W₂} {φ : W₁ →ₗ[K] W₂} :
    φ ∈ homN N₁ N₂ ↔ φ ∘ₗ N₁ = N₂ ∘ₗ φ :=
  Iff.rfl

@[expose] def rkPow (N : Module.End K W₁) (j : ℕ) : ℕ :=
  finrank K (LinearMap.range (N ^ j))

theorem rkPow_succ_le [FiniteDimensional K W₁] (N : Module.End K W₁) (j : ℕ) :
    rkPow N (j + 1) ≤ rkPow N j := by
  refine Submodule.finrank_mono ?_
  rw [pow_succ, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range N (N ^ j)

theorem rkPow_antitone [FiniteDimensional K W₁] (N : Module.End K W₁) : Antitone (rkPow N) :=
  antitone_nat_of_succ_le (rkPow_succ_le N)

theorem rkPow_zero [FiniteDimensional K W₁] (N : Module.End K W₁) :
    rkPow N 0 = finrank K W₁ := by
  rw [rkPow, pow_zero, Module.End.one_eq_id, LinearMap.range_id, finrank_top]

theorem rkPow_eq_zero_of_pow_eq_zero {N : Module.End K W₁} {j : ℕ} (h : N ^ j = 0) :
    rkPow N j = 0 := by
  rw [rkPow, h, LinearMap.range_zero, finrank_bot]

theorem pow_comp_eq_of_comp_eq {N₁ : Module.End K W₁} {N₂ : Module.End K W₂}
    {φ : W₁ →ₗ[K] W₂} (h : φ ∘ₗ N₁ = N₂ ∘ₗ φ) (j : ℕ) : φ ∘ₗ (N₁ ^ j) = (N₂ ^ j) ∘ₗ φ := by
  induction j with
  | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, Module.End.one_eq_id,
      LinearMap.comp_id, LinearMap.id_comp]
  | succ j ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc,
      ih, LinearMap.comp_assoc, h, ← LinearMap.comp_assoc]

theorem rkPow_eq_of_equiv [FiniteDimensional K W₁] [FiniteDimensional K W₂]
    {N₁ : Module.End K W₁} {N₂ : Module.End K W₂} (e : W₁ ≃ₗ[K] W₂)
    (h : e.toLinearMap ∘ₗ N₁ = N₂ ∘ₗ e.toLinearMap) (j : ℕ) : rkPow N₁ j = rkPow N₂ j := by
  have hj := pow_comp_eq_of_comp_eq h j
  have hr : LinearMap.range (N₂ ^ j) = (LinearMap.range (N₁ ^ j)).map e.toLinearMap := by
    rw [← LinearMap.range_comp, hj, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [rkPow, rkPow, hr, LinearEquiv.finrank_map_eq]

theorem finrank_homN_le_of_equiv [FiniteDimensional K W₁] [FiniteDimensional K W₂]
    {N₁ : Module.End K W₁} {N₂ : Module.End K W₂} (e : W₁ ≃ₗ[K] W₂)
    (h : e.toLinearMap ∘ₗ N₁ = N₂ ∘ₗ e.toLinearMap) :
    finrank K (homN N₂ N₂) ≤ finrank K (homN N₁ N₁) := by
  have h' : e.symm.toLinearMap ∘ₗ N₂ = N₁ ∘ₗ e.symm.toLinearMap := by
    ext v
    have := congrArg (fun f : W₁ →ₗ[K] W₂ => e.symm (f (e.symm v))) h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply] at this
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← this]
  have he : ∀ v, e (N₁ v) = N₂ (e v) := fun v => congrArg (fun f => f v) h
  have he' : ∀ u, e.symm (N₂ u) = N₁ (e.symm u) := fun u => congrArg (fun f => f u) h'
  let F : homN N₂ N₂ →ₗ[K] homN N₁ N₁ :=
    { toFun := fun φ => ⟨e.symm.toLinearMap ∘ₗ φ.1 ∘ₗ e.toLinearMap, by
        have hφ : ∀ u, φ.1 (N₂ u) = N₂ (φ.1 u) := fun u => congrArg (fun f => f u) φ.2
        rw [mem_homN]
        ext v
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [he, hφ, he']⟩
      map_add' := fun φ ψ => by
        ext v
        simp
      map_smul' := fun a φ => by
        ext v
        simp }
  refine LinearMap.finrank_le_finrank_of_injective (f := F) fun φ ψ hφψ => ?_
  apply Subtype.ext
  ext v
  have := congrArg (fun χ : homN N₁ N₁ => e (χ.1 (e.symm v))) hφψ
  simpa [F] using this

end Hom

section Prod

variable {W₁ W₂ : Type*} [AddCommGroup W₁] [Module K W₁] [AddCommGroup W₂] [Module K W₂]

theorem prodMap_pow (N₁ : Module.End K W₁) (N₂ : Module.End K W₂) (j : ℕ) :
    (N₁.prodMap N₂) ^ j = (N₁ ^ j).prodMap (N₂ ^ j) := by
  induction j with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero, Module.End.one_eq_id, Module.End.one_eq_id,
      Module.End.one_eq_id, LinearMap.prodMap_id]
  | succ j ih => rw [pow_succ, pow_succ, pow_succ, ih, LinearMap.prodMap_mul]

theorem rkPow_prodMap [FiniteDimensional K W₁] [FiniteDimensional K W₂] (N₁ : Module.End K W₁)
    (N₂ : Module.End K W₂) (j : ℕ) :
    rkPow (N₁.prodMap N₂) j = rkPow N₁ j + rkPow N₂ j := by
  rw [rkPow, prodMap_pow, LinearMap.range_prodMap,
    LinearEquiv.finrank_eq (Submodule.prodEquiv _ _), finrank_prod]
  rfl

@[expose] def blockEnd (a : W₁ →ₗ[K] W₁) (b : W₂ →ₗ[K] W₂) (c : W₁ →ₗ[K] W₂)
    (d : W₂ →ₗ[K] W₁) : Module.End K (W₁ × W₂) :=
  (a.coprod d).prod (c.coprod b)

theorem blockEnd_apply (a : W₁ →ₗ[K] W₁) (b : W₂ →ₗ[K] W₂) (c : W₁ →ₗ[K] W₂)
    (d : W₂ →ₗ[K] W₁) (v : W₁ × W₂) :
    blockEnd a b c d v = (a v.1 + d v.2, c v.1 + b v.2) :=
  rfl

theorem finrank_homN_prodMap [FiniteDimensional K W₁] [FiniteDimensional K W₂]
    (N₁ : Module.End K W₁) (N₂ : Module.End K W₂) :
    finrank K (homN N₁ N₁) + finrank K (homN N₂ N₂) + finrank K (homN N₁ N₂) +
        finrank K (homN N₂ N₁) ≤ finrank K (homN (N₁.prodMap N₂) (N₁.prodMap N₂)) := by
  let F : ((homN N₁ N₁ × homN N₂ N₂) × homN N₁ N₂) × homN N₂ N₁ →ₗ[K]
      homN (N₁.prodMap N₂) (N₁.prodMap N₂) :=
    { toFun := fun x => ⟨blockEnd x.1.1.1.1 x.1.1.2.1 x.1.2.1 x.2.1, by
        have ha : ∀ u, x.1.1.1.1 (N₁ u) = N₁ (x.1.1.1.1 u) := fun u =>
          congrArg (fun f => f u) x.1.1.1.2
        have hb : ∀ u, x.1.1.2.1 (N₂ u) = N₂ (x.1.1.2.1 u) := fun u =>
          congrArg (fun f => f u) x.1.1.2.2
        have hc : ∀ u, x.1.2.1 (N₁ u) = N₂ (x.1.2.1 u) := fun u =>
          congrArg (fun f => f u) x.1.2.2
        have hd : ∀ u, x.2.1 (N₂ u) = N₁ (x.2.1 u) := fun u =>
          congrArg (fun f => f u) x.2.2
        rw [mem_homN]
        refine LinearMap.ext fun v => Prod.ext ?_ ?_
        · simp only [LinearMap.comp_apply, blockEnd_apply, LinearMap.prodMap_apply, map_add,
            ha, hd]
        · simp only [LinearMap.comp_apply, blockEnd_apply, LinearMap.prodMap_apply, map_add,
            hb, hc]⟩
      map_add' := fun x y => by
        apply Subtype.ext
        refine LinearMap.ext fun v => Prod.ext ?_ ?_ <;> simp [blockEnd_apply] <;> abel
      map_smul' := fun a x => by
        apply Subtype.ext
        refine LinearMap.ext fun v => Prod.ext ?_ ?_ <;> simp [blockEnd_apply] }
  have hF : Function.Injective F := by
    intro x y hxy
    have h1 : ∀ v : W₁ × W₂, blockEnd x.1.1.1.1 x.1.1.2.1 x.1.2.1 x.2.1 v =
        blockEnd y.1.1.1.1 y.1.1.2.1 y.1.2.1 y.2.1 v := fun v =>
      congrArg (fun χ : homN (N₁.prodMap N₂) (N₁.prodMap N₂) => χ.1 v) hxy
    have ha : x.1.1.1 = y.1.1.1 := Subtype.ext (LinearMap.ext fun v => by
      simpa [blockEnd_apply] using congrArg Prod.fst (h1 (v, 0)))
    have hb : x.1.1.2 = y.1.1.2 := Subtype.ext (LinearMap.ext fun v => by
      simpa [blockEnd_apply] using congrArg Prod.snd (h1 (0, v)))
    have hc : x.1.2 = y.1.2 := Subtype.ext (LinearMap.ext fun v => by
      simpa [blockEnd_apply] using congrArg Prod.snd (h1 (v, 0)))
    have hd : x.2 = y.2 := Subtype.ext (LinearMap.ext fun v => by
      simpa [blockEnd_apply] using congrArg Prod.fst (h1 (0, v)))
    exact Prod.ext (Prod.ext (Prod.ext ha hb) hc) hd
  have := LinearMap.finrank_le_finrank_of_injective hF
  simpa only [finrank_prod] using this

end Prod

section Shift

@[expose] def shiftOp (r : ℕ) : Module.End K (Fin r → K) where
  toFun c i := if h : (i : ℕ) = 0 then 0 else c ⟨(i : ℕ) - 1, by omega⟩
  map_add' c d := by
    funext i
    by_cases h : (i : ℕ) = 0 <;> simp [h]
  map_smul' a c := by
    funext i
    by_cases h : (i : ℕ) = 0 <;> simp [h]

theorem shiftOp_apply (r : ℕ) (c : Fin r → K) (i : Fin r) :
    shiftOp r c i = if h : (i : ℕ) = 0 then 0 else c ⟨(i : ℕ) - 1, by omega⟩ :=
  rfl

theorem shiftOp_pow_apply (r j : ℕ) (c : Fin r → K) (i : Fin r) :
    (shiftOp r ^ j) c i = if h : j ≤ (i : ℕ) then c ⟨(i : ℕ) - j, by omega⟩ else 0 := by
  induction j generalizing i with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, shiftOp_apply]
    by_cases h0 : (i : ℕ) = 0
    · rw [dite_eq_left h0, dite_eq_right (by omega)]
    · rw [dite_eq_right h0, ih]
      by_cases hj : j + 1 ≤ (i : ℕ)
      · rw [dite_eq_left (show j ≤ (i : ℕ) - 1 by omega), dite_eq_left hj]
        congr 1
        ext
        simp only
        omega
      · rw [dite_eq_right (show ¬ j ≤ (i : ℕ) - 1 by omega), dite_eq_right hj]

theorem shiftOp_pow_single (r : ℕ) (hr : 0 < r) (i : Fin r) :
    (shiftOp r ^ (i : ℕ)) (Pi.single ⟨0, hr⟩ (1 : K)) = Pi.single i 1 := by
  funext l
  rw [shiftOp_pow_apply]
  by_cases hil : (i : ℕ) ≤ (l : ℕ)
  · rw [dite_eq_left hil]
    by_cases h : l = i
    · subst h
      simp
    · rw [Pi.single_apply, ite_eq_right (fun h' => by
          have := congrArg Fin.val h'
          simp only at this
          omega), Pi.single_apply, ite_eq_right h]
  · rw [dite_eq_right hil, Pi.single_apply, ite_eq_right (fun h => hil (by rw [h]))]

theorem rkPow_shiftOp (r j : ℕ) : rkPow (shiftOp r : Module.End K (Fin r → K)) j = r - j := by
  let ψ : (Fin (r - j) → K) →ₗ[K] (Fin r → K) :=
    { toFun := fun u i => if h : j ≤ (i : ℕ) then u ⟨(i : ℕ) - j, by omega⟩ else 0
      map_add' := fun u v => by
        funext i
        by_cases h : j ≤ (i : ℕ) <;> simp [h]
      map_smul' := fun a u => by
        funext i
        by_cases h : j ≤ (i : ℕ) <;> simp [h] }
  let τ : (Fin r → K) →ₗ[K] (Fin (r - j) → K) :=
    { toFun := fun c k => c ⟨(k : ℕ), by omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hS : (shiftOp r : Module.End K (Fin r → K)) ^ j = ψ ∘ₗ τ := by
    refine LinearMap.ext fun c => funext fun i => ?_
    rw [shiftOp_pow_apply]
    rfl
  have hτ : LinearMap.range τ = ⊤ := by
    refine LinearMap.range_eq_top.2 fun u => ⟨fun i => if h : (i : ℕ) < r - j then
      u ⟨(i : ℕ), h⟩ else 0, ?_⟩
    funext k
    change (if h : ((⟨(k : ℕ), _⟩ : Fin r) : ℕ) < r - j then u ⟨_, h⟩ else 0) = u k
    rw [dite_eq_left k.2]
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext k
    have := congrFun hu ⟨(k : ℕ) + j, by omega⟩
    change (if h : j ≤ (k : ℕ) + j then u ⟨(k : ℕ) + j - j, _⟩ else 0) = 0 at this
    rw [dite_eq_left (by omega)] at this
    simpa using this
  rw [rkPow, hS, LinearMap.range_comp_of_range_eq_top _ hτ, LinearMap.finrank_range_of_inj hψ,
    finrank_fin_fun]

theorem le_finrank_homN_shiftOp (r : ℕ) :
    r ≤ finrank K (homN (shiftOp r : Module.End K (Fin r → K)) (shiftOp r)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Nat.zero_le _
  let F : (Fin r → K) →ₗ[K] homN (shiftOp r : Module.End K (Fin r → K)) (shiftOp r) :=
    { toFun := fun c => ⟨∑ i, c i • (shiftOp r) ^ (i : ℕ), by
        rw [mem_homN, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, Finset.sum_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, mul_smul_comm, ← pow_succ, ← pow_succ']⟩
      map_add' := fun c d => by
        apply Subtype.ext
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        apply Subtype.ext
        simp [Finset.smul_sum, smul_smul] }
  have hF : Function.Injective F := by
    intro c d hcd
    have h1 := congrArg (fun χ : homN (shiftOp r : Module.End K (Fin r → K)) (shiftOp r) =>
      χ.1 (Pi.single ⟨0, hr⟩ 1)) hcd
    simp only [F, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply,
      LinearMap.smul_apply, shiftOp_pow_single r hr] at h1
    funext l
    have h2 := congrFun h1 l
    simpa [Finset.sum_apply, Pi.single_apply] using h2
  simpa using LinearMap.finrank_le_finrank_of_injective hF

variable {W' : Type*} [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']

theorem finrank_le_finrank_homN_shiftOp_left {r : ℕ} (hr : 0 < r) (N' : Module.End K W')
    (hN : N' ^ r = 0) : finrank K W' ≤ finrank K (homN (shiftOp r) N') := by
  have hsum : ∀ (w : W') (c : Fin r → K), ∑ i, (shiftOp r c) i • (N' ^ (i : ℕ)) w =
      N' (∑ i, c i • (N' ^ (i : ℕ)) w) := by
    intro w c
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Fin.sum_univ_succ, map_sum, Fin.sum_univ_castSucc]
    have hlast : N' (c (Fin.last r') • (N' ^ ((Fin.last r' : Fin (r' + 1)) : ℕ)) w) = 0 := by
      rw [map_smul, ← Module.End.mul_apply, ← pow_succ', Fin.val_last, hN, LinearMap.zero_apply,
        smul_zero]
    have h0 : shiftOp (r' + 1) c 0 = 0 := by
      rw [shiftOp_apply, dite_eq_left (by simp)]
    rw [hlast, add_zero, h0, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : shiftOp (r' + 1) c k.succ = c k.castSucc := by
      rw [shiftOp_apply, dite_eq_right (by simp)]
      congr 1
    rw [hk, map_smul, ← Module.End.mul_apply, ← pow_succ', Fin.val_succ, Fin.val_castSucc]
  let B : W' →ₗ[K] homN (shiftOp r) N' :=
    { toFun := fun w => ⟨{ toFun := fun c => ∑ i, c i • (N' ^ (i : ℕ)) w
                           map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
                           map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }, by
        rw [mem_homN]
        exact LinearMap.ext fun c => hsum w c⟩
      map_add' := fun w w' => by
        apply Subtype.ext
        refine LinearMap.ext fun c => ?_
        simp [Finset.sum_add_distrib]
      map_smul' := fun a w => by
        apply Subtype.ext
        refine LinearMap.ext fun c => ?_
        simp [Finset.smul_sum, smul_comm a] }
  have hB : Function.Injective B := by
    intro w w' hww
    have h1 := congrArg (fun χ : homN (shiftOp r) N' => χ.1 (Pi.single ⟨0, hr⟩ 1)) hww
    simp only [B, LinearMap.coe_mk, AddHom.coe_mk] at h1
    rw [Fintype.sum_eq_single ⟨0, hr⟩ (fun i hi => by rw [Pi.single_eq_of_ne hi, zero_smul]),
      Fintype.sum_eq_single ⟨0, hr⟩ (fun i hi => by rw [Pi.single_eq_of_ne hi, zero_smul])] at h1
    simpa using h1
  exact LinearMap.finrank_le_finrank_of_injective hB

theorem finrank_le_finrank_homN_shiftOp_right {r : ℕ} (hr : 0 < r) (N' : Module.End K W')
    (hN : N' ^ r = 0) : finrank K W' ≤ finrank K (homN N' (shiftOp r)) := by
  let A : Module.Dual K W' →ₗ[K] homN N' (shiftOp r) :=
    { toFun := fun g => ⟨LinearMap.pi fun i : Fin r => g ∘ₗ N' ^ (r - 1 - (i : ℕ)), by
        rw [mem_homN]
        ext v i
        simp only [LinearMap.comp_apply, LinearMap.pi_apply]
        rw [shiftOp_apply]
        by_cases hi : (i : ℕ) = 0
        · rw [dite_eq_left hi, hi, ← Module.End.mul_apply, ← pow_succ, show r - 1 - 0 + 1 = r by
            omega, hN, LinearMap.zero_apply, map_zero]
        · rw [dite_eq_right hi, LinearMap.pi_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
            ← pow_succ, show r - 1 - (i : ℕ) + 1 = r - 1 - ((i : ℕ) - 1) by omega]⟩
      map_add' := fun g h => by
        apply Subtype.ext
        ext v i
        simp
      map_smul' := fun a g => by
        apply Subtype.ext
        ext v i
        simp }
  have hA : Function.Injective A := by
    intro g h hgh
    ext v
    have h1 := congrArg (fun χ : homN N' (shiftOp r) => χ.1 v ⟨r - 1, by omega⟩) hgh
    simpa [A] using h1
  have := LinearMap.finrank_le_finrank_of_injective hA
  rwa [Subspace.dual_finrank_eq] at this

end Shift

section Split

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_equiv_shift_prod (N : Module.End K W) {r : ℕ} (hr : 0 < r) (hN : N ^ r = 0)
    (hN' : N ^ (r - 1) ≠ 0) :
    ∃ (W' : Submodule K W) (N' : Module.End K W') (Φ : W ≃ₗ[K] (Fin r → K) × W'),
      N' ^ r = 0 ∧ Φ.toLinearMap ∘ₗ N = ((shiftOp r).prodMap N') ∘ₗ Φ.toLinearMap := by
  classical
  obtain ⟨w, hw⟩ : ∃ w, (N ^ (r - 1)) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hN' (LinearMap.ext h)
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : Module.Dual K W, f₀ ((N ^ (r - 1)) w) ≠ 0 := by
    by_contra h
    push Not at h
    exact hw ((Module.forall_dual_apply_eq_zero_iff K _).1 h)
  set f : Module.Dual K W := (f₀ ((N ^ (r - 1)) w))⁻¹ • f₀ with hfdef
  have hf : f ((N ^ (r - 1)) w) = 1 := by
    rw [hfdef, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]
  let α : W →ₗ[K] (Fin r → K) := LinearMap.pi fun i : Fin r => f ∘ₗ N ^ (r - 1 - (i : ℕ))
  let β : (Fin r → K) →ₗ[K] W :=
    { toFun := fun c => ∑ i, c i • (N ^ (i : ℕ)) w
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  have hα : α ∘ₗ N = shiftOp r ∘ₗ α := by
    ext v i
    simp only [α, LinearMap.comp_apply, LinearMap.pi_apply]
    rw [shiftOp_apply]
    by_cases hi : (i : ℕ) = 0
    · rw [dite_eq_left hi, hi, ← Module.End.mul_apply, ← pow_succ, show r - 1 - 0 + 1 = r by
        omega, hN, LinearMap.zero_apply, map_zero]
    · rw [dite_eq_right hi, LinearMap.pi_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
        ← pow_succ, show r - 1 - (i : ℕ) + 1 = r - 1 - ((i : ℕ) - 1) by omega]
  have hβ : β ∘ₗ shiftOp r = N ∘ₗ β := by
    refine LinearMap.ext fun c => ?_
    simp only [β, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Fin.sum_univ_succ, map_sum, Fin.sum_univ_castSucc]
    have hlast : N (c (Fin.last r') • (N ^ ((Fin.last r' : Fin (r' + 1)) : ℕ)) w) = 0 := by
      rw [map_smul, ← Module.End.mul_apply, ← pow_succ', Fin.val_last, hN, LinearMap.zero_apply,
        smul_zero]
    have h0 : shiftOp (r' + 1) c 0 = 0 := by
      rw [shiftOp_apply, dite_eq_left (by simp)]
    rw [hlast, add_zero, h0, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : shiftOp (r' + 1) c k.succ = c k.castSucc := by
      rw [shiftOp_apply, dite_eq_right (by simp)]
      congr 1
    rw [hk, map_smul, ← Module.End.mul_apply, ← pow_succ', Fin.val_succ, Fin.val_castSucc]
  have hγ : Function.Injective (α ∘ₗ β) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hne
    have hex : ∃ i, c i ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    let s := Nat.find (p := fun n => ∃ i : Fin r, (i : ℕ) = n ∧ c i ≠ 0)
      (by obtain ⟨i, hi⟩ := hex; exact ⟨i, i, rfl, hi⟩)
    obtain ⟨i₀, hi₀s, hi₀⟩ := Nat.find_spec (p := fun n => ∃ i : Fin r, (i : ℕ) = n ∧ c i ≠ 0)
      (by obtain ⟨i, hi⟩ := hex; exact ⟨i, i, rfl, hi⟩)
    have hmin : ∀ i : Fin r, (i : ℕ) < i₀ → c i = 0 := by
      intro i hi
      by_contra hci
      exact Nat.find_min (p := fun n => ∃ i : Fin r, (i : ℕ) = n ∧ c i ≠ 0)
        (by obtain ⟨i, hi⟩ := hex; exact ⟨i, i, rfl, hi⟩) (hi₀s ▸ hi) ⟨i, rfl, hci⟩
    have h1 := congrFun hc i₀
    simp only [α, β, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.coe_mk, AddHom.coe_mk,
      map_sum, map_smul, smul_eq_mul, Pi.zero_apply] at h1
    rw [Finset.sum_eq_single i₀] at h1
    · rw [← Module.End.mul_apply, ← pow_add, show r - 1 - (i₀ : ℕ) + (i₀ : ℕ) = r - 1 by omega,
        hf, mul_one] at h1
      exact hi₀ h1
    · intro i _ hi
      rcases lt_or_gt_of_ne (fun h => hi (Fin.ext h)) with hlt | hgt
      · rw [hmin i hlt, zero_mul]
      · rw [← Module.End.mul_apply, ← pow_add, show r - 1 - (i₀ : ℕ) + (i : ℕ) = r +
          ((i : ℕ) - (i₀ : ℕ) - 1) by omega, pow_add, hN, zero_mul, LinearMap.zero_apply,
          map_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set γ := LinearEquiv.ofInjectiveEndo (α ∘ₗ β) hγ with hγdef
  have hγS : γ.symm.toLinearMap ∘ₗ shiftOp r = shiftOp r ∘ₗ γ.symm.toLinearMap := by
    have h1 : (α ∘ₗ β) ∘ₗ shiftOp r = shiftOp r ∘ₗ (α ∘ₗ β) := by
      rw [LinearMap.comp_assoc, hβ, ← LinearMap.comp_assoc, hα, LinearMap.comp_assoc]
    refine LinearMap.ext fun c => ?_
    apply γ.injective
    have h2 := congrArg (fun φ => φ (γ.symm c)) h1
    simp only [LinearMap.comp_apply] at h2
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    change shiftOp r c = (α ∘ₗ β) (shiftOp r (γ.symm c))
    rw [LinearMap.comp_apply, h2]
    change shiftOp r c = shiftOp r (γ (γ.symm c))
    rw [LinearEquiv.apply_symm_apply]
  set W' := LinearMap.ker α with hW'
  have hW'N : ∀ x ∈ W', N x ∈ W' := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    have := congrArg (fun φ => φ x) hα
    simp only [LinearMap.comp_apply] at this
    rw [this, hx, map_zero]
  set N' := N.restrict hW'N
  set π₀ : Module.End K W := β ∘ₗ γ.symm.toLinearMap ∘ₗ α
  have hαβγ : ∀ c, α (β (γ.symm c)) = c := fun c => by
    change γ (γ.symm c) = c
    exact LinearEquiv.apply_symm_apply γ c
  have hπ₀ : ∀ v, v - π₀ v ∈ W' := fun v => by
    rw [LinearMap.mem_ker, map_sub]
    change α v - α (β (γ.symm (α v))) = 0
    rw [hαβγ, sub_self]
  let Φ₁ : W →ₗ[K] (Fin r → K) × W' :=
    LinearMap.prod α (LinearMap.codRestrict W' (LinearMap.id - π₀) fun v => hπ₀ v)
  let Ψ : (Fin r → K) × W' →ₗ[K] W := (β ∘ₗ γ.symm.toLinearMap).coprod W'.subtype
  have hΨΦ : ∀ v, Ψ (Φ₁ v) = v := fun v => by
    change β (γ.symm (α v)) + (v - β (γ.symm (α v))) = v
    abel
  have hΦΨ : ∀ x, Φ₁ (Ψ x) = x := fun x => by
    obtain ⟨c, k⟩ := x
    have hk : α k = 0 := k.2
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change α (β (γ.symm c) + k) = c
      rw [map_add, hαβγ, hk, add_zero]
    · change β (γ.symm c) + k - β (γ.symm (α (β (γ.symm c) + (k : W)))) = k
      rw [map_add, hαβγ, hk, add_zero]
      abel
  let Φ : W ≃ₗ[K] (Fin r → K) × W' := LinearEquiv.ofLinearMap Φ₁ Ψ
    (LinearMap.ext fun x => hΦΨ x) (LinearMap.ext fun v => hΨΦ v)
  refine ⟨W', N', Φ, ?_, ?_⟩
  · exact Module.End.submodule_pow_eq_zero_of_pow_eq_zero (LinearMap.ext fun x => rfl) hN
  · have hπN : ∀ v, π₀ (N v) = N (π₀ v) := fun v => by
      change β (γ.symm (α (N v))) = N (β (γ.symm (α v)))
      have e1 := congrArg (fun φ => φ v) hα
      have e2 := congrArg (fun φ => φ (α v)) hγS
      have e3 := congrArg (fun φ => φ (γ.symm (α v))) hβ
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at e1 e2 e3
      rw [e1, e2, e3]
    refine LinearMap.ext fun v => Prod.ext ?_ (Subtype.ext ?_)
    · change α (N v) = shiftOp r (α v)
      exact congrArg (fun φ => φ v) hα
    · change N v - π₀ (N v) = N (v - π₀ v)
      rw [map_sub, hπN]

end Split

section Main

universe u

variable {W₀ : Type*} [AddCommGroup W₀] [Module K W₀]

theorem sum_range_sub_of_antitone {a : ℕ → ℕ} (ha : Antitone a) (L : ℕ) :
    ∑ j ∈ Finset.range L, (a j - a (j + 1)) = a 0 - a L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 := ha (Nat.zero_le L)
    have h2 : a (L + 1) ≤ a L := ha (Nat.le_add_right L 1)
    omega

theorem sum_range_sub_rkPow [FiniteDimensional K W₀] (N : Module.End K W₀) {L : ℕ}
    (hL : N ^ L = 0) :
    ∑ j ∈ Finset.range L, (rkPow N j - rkPow N (j + 1)) = finrank K W₀ := by
  rw [sum_range_sub_of_antitone (rkPow_antitone N), rkPow_zero, rkPow_eq_zero_of_pow_eq_zero hL,
    Nat.sub_zero]

theorem sum_sq_le_finrank_homN_aux (d : ℕ) : ∀ (W : Type u) [AddCommGroup W] [Module K W]
    [FiniteDimensional K W], finrank K W = d → ∀ (N : Module.End K W) (L : ℕ), N ^ L = 0 →
    ∑ j ∈ Finset.range L, (rkPow N j - rkPow N (j + 1)) ^ 2 ≤ finrank K (homN N N) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W _ _ _ hd N L hL
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · refine (Finset.sum_eq_zero fun j _ => ?_).le.trans (Nat.zero_le _)
    have h1 : rkPow N j = 0 := Nat.eq_zero_of_le_zero
      ((Submodule.finrank_le _).trans hd.le)
    rw [h1, Nat.zero_sub, zero_pow two_ne_zero]
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hex : ∃ k, N ^ k = 0 := ⟨L, hL⟩
  set r := Nat.find hex with hrdef
  have hNr : N ^ r = 0 := Nat.find_spec hex
  have hrL : r ≤ L := Nat.find_min' hex hL
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, pow_zero] at hNr
      exact absurd hNr one_ne_zero
    · exact h
  have hNr1 : N ^ (r - 1) ≠ 0 := Nat.find_min hex (by omega)
  have hsum : ∑ j ∈ Finset.range L, (rkPow N j - rkPow N (j + 1)) ^ 2 =
      ∑ j ∈ Finset.range r, (rkPow N j - rkPow N (j + 1)) ^ 2 := by
    refine (Finset.sum_subset (Finset.range_subset_range.2 hrL) fun j _ hj => ?_).symm
    have hjr : r ≤ j := by simpa using hj
    have h0 : N ^ j = 0 := by
      rw [show j = r + (j - r) by omega, pow_add, hNr, zero_mul]
    rw [rkPow_eq_zero_of_pow_eq_zero h0, Nat.zero_sub, zero_pow two_ne_zero]
  obtain ⟨W', N', Φ, hN'r, hΦ⟩ := exists_equiv_shift_prod N hr hNr hNr1
  have hrk : ∀ j, rkPow N j = (r - j) + rkPow N' j := fun j => by
    rw [rkPow_eq_of_equiv Φ hΦ, rkPow_prodMap, rkPow_shiftOp]
  have hdim : d = r + finrank K W' := by
    rw [← hd, LinearEquiv.finrank_eq Φ, finrank_prod, finrank_fin_fun]
  have hIH := ih (finrank K W') (by omega) W' rfl N' r hN'r
  have hC := (finrank_homN_prodMap (shiftOp r) N').trans (finrank_homN_le_of_equiv Φ hΦ)
  have hS := le_finrank_homN_shiftOp (K := K) r
  have hL₁ := finrank_le_finrank_homN_shiftOp_left hr N' hN'r
  have hL₂ := finrank_le_finrank_homN_shiftOp_right hr N' hN'r
  have hterm : ∀ j ∈ Finset.range r, (rkPow N j - rkPow N (j + 1)) ^ 2 =
      1 + 2 * (rkPow N' j - rkPow N' (j + 1)) + (rkPow N' j - rkPow N' (j + 1)) ^ 2 := by
    intro j hj
    have hjr : j < r := by simpa using hj
    have hmono := rkPow_succ_le N' j
    rw [hrk, hrk]
    have : r - j + rkPow N' j - (r - (j + 1) + rkPow N' (j + 1)) =
        1 + (rkPow N' j - rkPow N' (j + 1)) := by omega
    rw [this]
    ring
  have htel := sum_range_sub_rkPow N' hN'r
  rw [hsum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, htel, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  omega

theorem sum_sq_le_finrank_homN {W : Type u} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (N : Module.End K W) {L : ℕ} (hL : N ^ L = 0) :
    ∑ j ∈ Finset.range L, (rkPow N j - rkPow N (j + 1)) ^ 2 ≤ finrank K (homN N N) :=
  sum_sq_le_finrank_homN_aux _ W rfl N L hL

end Main

theorem pow_ne_zero_of_finrank_homN_le {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (N : Module.End K W) {P : ℕ} (hP : 2 ≤ P) (hd : 2 ≤ finrank K W)
    (hC : P * (finrank K (homN N N) - 1) ≤ finrank K W ^ 2 - 1) :
    N ^ (P - 1) ≠ 0 ∨ (finrank K W = P - 1 ∧ N ^ (P - 2) ≠ 0) := by
  by_cases h1 : N ^ (P - 1) = 0
  swap
  · exact Or.inl h1
  right
  set d := finrank K W with hddef
  set C := finrank K (homN N N) with hCdef
  set c : ℕ → ℕ := fun j => rkPow N j - rkPow N (j + 1) with hcdef
  have hS2 : ∑ j ∈ Finset.range (P - 1), c j ^ 2 ≤ C := sum_sq_le_finrank_homN N h1
  have hS1 : ∑ j ∈ Finset.range (P - 1), c j = d := sum_range_sub_rkPow N h1
  have hCS : (∑ j ∈ Finset.range (P - 1), c j) ^ 2 ≤
      (P - 1) * ∑ j ∈ Finset.range (P - 1), c j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range (P - 1)) (f := c)
    simpa using this
  have hle : ∑ j ∈ Finset.range (P - 1), c j ≤ ∑ j ∈ Finset.range (P - 1), c j ^ 2 :=
    Finset.sum_le_sum fun j _ => Nat.le_self_pow two_ne_zero _
  rw [hS1] at hCS hle
  have ha : d ^ 2 ≤ (P - 1) * C := hCS.trans (Nat.mul_le_mul_left _ hS2)
  have hb : d ≤ C := hle.trans hS2
  have hdP : d = P - 1 := by
    have hP1 : ((P - 1 : ℕ) : ℤ) = (P : ℤ) - 1 := by push_cast [show 1 ≤ P by omega]; ring
    have hC1 : ((C - 1 : ℕ) : ℤ) = (C : ℤ) - 1 := by push_cast [show 1 ≤ C by omega]; ring
    have hd1 : ((d ^ 2 - 1 : ℕ) : ℤ) = (d : ℤ) ^ 2 - 1 := by
      push_cast [show 1 ≤ d ^ 2 by nlinarith]; ring
    have ha' : (d : ℤ) ^ 2 ≤ ((P : ℤ) - 1) * C := by
      have h := (Nat.cast_le (α := ℤ)).2 ha
      rw [Nat.cast_mul, Nat.cast_pow, hP1] at h
      exact h
    have hb' : (d : ℤ) ≤ C := by exact_mod_cast hb
    have hc' : (P : ℤ) * ((C : ℤ) - 1) ≤ (d : ℤ) ^ 2 - 1 := by
      rw [← hC1, ← hd1]
      exact_mod_cast hC
    have hd2 : (2 : ℤ) ≤ d := by exact_mod_cast hd
    have hP2 : (2 : ℤ) ≤ P := by exact_mod_cast hP
    have hup : (d : ℤ) ≤ P - 1 := by nlinarith
    have hlo : (P : ℤ) - 1 ≤ d := by nlinarith
    have : (d : ℤ) = P - 1 := le_antisymm hup hlo
    omega
  have hCd : C ≤ d := by
    have hC1 : ((C - 1 : ℕ) : ℤ) = (C : ℤ) - 1 := by push_cast [show 1 ≤ C by omega]; ring
    have hd1 : ((d ^ 2 - 1 : ℕ) : ℤ) = (d : ℤ) ^ 2 - 1 := by
      push_cast [show 1 ≤ d ^ 2 by nlinarith]; ring
    have hc' : (P : ℤ) * ((C : ℤ) - 1) ≤ (d : ℤ) ^ 2 - 1 := by
      rw [← hC1, ← hd1]
      exact_mod_cast hC
    have hdP' : (d : ℤ) = P - 1 := by omega
    have hP2 : (2 : ℤ) ≤ P := by exact_mod_cast hP
    have : (C : ℤ) ≤ d := by nlinarith
    exact_mod_cast this
  refine ⟨hdP, fun h2 => ?_⟩
  have heq : ∑ j ∈ Finset.range (P - 1), c j = ∑ j ∈ Finset.range (P - 1), c j ^ 2 := by
    rw [hS1]
    exact le_antisymm hle (hS2.trans hCd)
  have hc1 : ∀ j ∈ Finset.range (P - 1), c j ≤ 1 := by
    intro j hj
    have hj' := (Finset.sum_eq_sum_iff_of_le fun i _ => Nat.le_self_pow two_ne_zero (c i)).1
      heq j hj
    by_contra hcj
    have : c j * 1 < c j * c j := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    rw [sq] at hj'
    omega
  have hS1' : ∑ j ∈ Finset.range (P - 2), c j = d := sum_range_sub_rkPow N h2
  have hbound : ∑ j ∈ Finset.range (P - 2), c j ≤ P - 2 := by
    calc ∑ j ∈ Finset.range (P - 2), c j ≤ ∑ _j ∈ Finset.range (P - 2), 1 :=
          Finset.sum_le_sum fun j hj => hc1 j (by simp at hj ⊢; omega)
      _ = P - 2 := by simp
  omega

end CFSG.GroupTheory.HallHigmanB
