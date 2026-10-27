module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFamAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutField
import CFSG.GH74.Generic.S45.LUniVec
import CFSG.ClassicalGroups.Orthogonal.MinusPlaneFrames
import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open Matrix Module CFSG.ComponentClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

section Semi

theorem glEquiv_semiConj_pow_apply (A : GL ι K) (σ : K ≃+* K) (k : ℕ) (g : GL ι K)
    (v : ι → K) :
    glEquiv ((ModelGen.semiConj A σ ^ k) g) ((ModelGen.semiMap A σ)^[k] v) =
      (ModelGen.semiMap A σ)^[k] (glEquiv g v) := by
  induction k generalizing g v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
      ModelGen.glEquiv_semiConj_apply]

theorem semiMap_iterate_smul (A : GL ι K) (σ : K ≃+* K) (k : ℕ) (c : K) (v : ι → K) :
    (ModelGen.semiMap A σ)^[k] (c • v) = (σ ^ k) c • (ModelGen.semiMap A σ)^[k] v := by
  induction k generalizing c v with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ModelGen.semiMap_smul, ih,
      pow_succ]
    rfl

theorem semiMap_iterate_add (A : GL ι K) (σ : K ≃+* K) (k : ℕ) (v w : ι → K) :
    (ModelGen.semiMap A σ)^[k] (v + w) =
      (ModelGen.semiMap A σ)^[k] v + (ModelGen.semiMap A σ)^[k] w :=
  iterate_map_add (ModelGen.semiMap A σ) k v w

theorem semiMap_iterate_mem {A : GL ι K} {σ : K ≃+* K} {U : Submodule K (ι → K)}
    (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) (k : ℕ) {u : ι → K} (hu : u ∈ U) :
    (ModelGen.semiMap A σ)^[k] u ∈ U := by
  induction k generalizing u with
  | zero => exact hu
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (hU u hu)

variable {τ : K →+* K} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K} {U W : Submodule K (ι → K)}

theorem commute_of_forall_semiConj_pow (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) {A : GL ι K} {σ : K ≃+* K}
    {y : GL ι K} {k : ℕ}
    (H : ∀ j ∈ blkI β U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j)
    {s : U ≃ₗ[K] U} (hs : s ∈ ⁅isomU β U, isomU β U⁆) (v : U)
    (hTv : glEquiv y ((ModelGen.semiMap A σ)^[k] v) ∈ U) :
    glEquiv y ((ModelGen.semiMap A σ)^[k] (s v : ι → K)) = (s ⟨_, hTv⟩ : ι → K) := by
  have hj := extU_mem_blkI hUW horth hs
  have hjy : y * (ModelGen.semiConj A σ ^ k) (glEquiv.symm (extU hUW s)) =
      glEquiv.symm (extU hUW s) * y :=
    mul_inv_eq_iff_eq_mul.1 (H _ hj)
  have h1 : glEquiv (glEquiv.symm (extU hUW s)) (v : ι → K) = s v := by
    rw [MulEquiv.apply_symm_apply, extU_apply_mem]
  calc glEquiv y ((ModelGen.semiMap A σ)^[k] (s v : ι → K))
      = glEquiv y ((ModelGen.semiMap A σ)^[k] (glEquiv (glEquiv.symm (extU hUW s)) v)) := by
        rw [h1]
    _ = glEquiv (y * (ModelGen.semiConj A σ ^ k) (glEquiv.symm (extU hUW s)))
          ((ModelGen.semiMap A σ)^[k] v) := by
        rw [← glEquiv_semiConj_pow_apply, map_mul, LinearEquiv.mul_apply]
    _ = glEquiv (glEquiv.symm (extU hUW s)) (glEquiv y ((ModelGen.semiMap A σ)^[k] v)) := by
        rw [hjy, map_mul, LinearEquiv.mul_apply]
    _ = (s ⟨_, hTv⟩ : ι → K) := by
        rw [MulEquiv.apply_symm_apply]
        exact extU_apply_mem hUW s ⟨_, hTv⟩

end Semi

section Test

variable {ρ : K → K} {T : (ι → K) → (ι → K)} {U : Submodule K (ι → K)}

theorem eq_of_commute_one_add (hTadd : ∀ v w, T (v + w) = T v + T w)
    (hTsmul : ∀ (c : K) v, T (c • v) = ρ c • T v) (hTinj : Function.Injective T)
    (hTU : ∀ u ∈ U, T u ∈ U) (N : U →ₗ[K] U) {x₀ : U} (hx₀ : N x₀ ≠ 0) {c : K}
    (h1 : ∀ u : U, T ((u : ι → K) + (N u : ι → K)) = T u + (N ⟨T u, hTU u u.2⟩ : ι → K))
    (hc : ∀ u : U,
      T ((u : ι → K) + c • (N u : ι → K)) = T u + c • (N ⟨T u, hTU u u.2⟩ : ι → K)) :
    ρ c = c := by
  have hT0 : T 0 = 0 := by
    have h := hTadd 0 0
    rw [add_zero] at h
    exact (add_eq_left.1 h.symm)
  have hN : T (N x₀ : ι → K) = (N ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) := by
    have h := h1 x₀
    rw [hTadd] at h
    exact add_left_cancel h
  have h2 := hc x₀
  rw [hTadd, hTsmul, hN] at h2
  have h3 : (ρ c - c) • (N ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.2 (add_left_cancel h2)
  have hne : (N ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) ≠ 0 := by
    rw [← hN]
    intro h
    exact hx₀ (Subtype.ext (hTinj (h.trans hT0.symm)))
  exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hne)

theorem eq_of_commute_one_add_sq (hTadd : ∀ v w, T (v + w) = T v + T w)
    (hTsmul : ∀ (c : K) v, T (c • v) = ρ c • T v) (hTinj : Function.Injective T)
    (hTU : ∀ u ∈ U, T u ∈ U) (h2 : (2 : K) ≠ 0) (N₁ N₂ : U →ₗ[K] U) {x₀ : U}
    (hx₁ : N₁ x₀ ≠ 0) (hx₂ : N₂ x₀ = 0)
    (hR : ∀ (a : K) (u : U), T ((u : ι → K) + a • (N₁ u : ι → K) + (a * a) • (N₂ u : ι → K)) =
      T u + a • (N₁ ⟨T u, hTU u u.2⟩ : ι → K) + (a * a) • (N₂ ⟨T u, hTU u u.2⟩ : ι → K))
    (c : K) : ρ c = c := by
  have hT0 : T 0 = 0 := by
    have h := hTadd 0 0
    rw [add_zero] at h
    exact (add_eq_left.1 h.symm)
  have hTneg : ∀ v, T (-v) = -T v := fun v => by
    have h := hTadd v (-v)
    rw [add_neg_cancel, hT0] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  have hz : (N₂ x₀ : ι → K) = 0 := by rw [hx₂]; rfl
  have E1 : T (N₁ x₀ : ι → K) = (N₁ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) +
      (N₂ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) := by
    have h := hR 1 x₀
    simp only [one_smul, one_mul, hz, smul_zero, add_zero] at h
    rw [hTadd] at h
    exact add_left_cancel (h.trans (add_assoc _ _ _))
  have E2 : -T (N₁ x₀ : ι → K) = -(N₁ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) +
      (N₂ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) := by
    have h := hR (-1) x₀
    simp only [neg_one_smul, neg_one_mul, neg_neg, one_smul, hz, smul_zero, add_zero] at h
    rw [hTadd, hTneg] at h
    exact add_left_cancel (h.trans (add_assoc _ _ _))
  have hz' : (N₂ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) = 0 := by
    have e1 : (N₂ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) =
        T (N₁ x₀ : ι → K) - (N₁ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) := by
      rw [E1]
      abel
    have e2 : (N₂ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) =
        -T (N₁ x₀ : ι → K) + (N₁ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) := by
      rw [E2]
      abel
    have h4 : (2 : K) • (N₂ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [e1]
      rw [e2]
      abel
    exact (smul_eq_zero.1 h4).resolve_left h2
  have E1' : T (N₁ x₀ : ι → K) = (N₁ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) := by
    rw [E1, hz', add_zero]
  have hc := hR c x₀
  simp only [hz, hz', smul_zero, add_zero] at hc
  rw [hTadd, hTsmul, E1'] at hc
  have h3 : (ρ c - c) • (N₁ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.2 (add_left_cancel hc)
  have hne : (N₁ ⟨T x₀, hTU x₀ x₀.2⟩ : ι → K) ≠ 0 := by
    rw [← E1']
    intro h
    exact hx₁ (Subtype.ext (hTinj (h.trans hT0.symm)))
  exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hne)

end Test

section Crit

variable {τ : K →+* K} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K} {U W : Submodule K (ι → K)}

theorem pow_apply_eq_of_forall_semiConj_pow (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) {A : GL ι K} {σ : K ≃+* K}
    (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) {y : GL ι K} (hyU : ∀ u ∈ U, glEquiv y u ∈ U)
    {k : ℕ} (H : ∀ j ∈ blkI β U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j)
    (N : U →ₗ[K] U) {x₀ : U} (hx₀ : N x₀ ≠ 0) {c : K} {s₁ s : U ≃ₗ[K] U}
    (hs₁ : s₁ ∈ ⁅isomU β U, isomU β U⁆) (hs : s ∈ ⁅isomU β U, isomU β U⁆)
    (hs₁N : ∀ u, s₁ u = u + N u) (hsN : ∀ u, s u = u + c • N u) : (σ ^ k) c = c := by
  have hTU : ∀ u ∈ U, glEquiv y ((ModelGen.semiMap A σ)^[k] u) ∈ U :=
    fun u hu => hyU _ (semiMap_iterate_mem hU k hu)
  refine eq_of_commute_one_add (T := fun v => glEquiv y ((ModelGen.semiMap A σ)^[k] v))
    (ρ := fun c => (σ ^ k) c) (fun v w => ?_) (fun c v => ?_) ?_ hTU N hx₀ (fun u => ?_)
    (fun u => ?_)
  · rw [semiMap_iterate_add, map_add]
  · rw [semiMap_iterate_smul, map_smul]
  · exact (glEquiv y).injective.comp (Function.Injective.iterate (ModelGen.semiMap A σ).injective k)
  · have e := commute_of_forall_semiConj_pow hUW horth H hs₁ u (hTU u u.2)
    rw [hs₁N, hs₁N, Submodule.coe_add, Submodule.coe_add] at e
    exact e
  · have e := commute_of_forall_semiConj_pow hUW horth H hs u (hTU u u.2)
    rw [hsN, hsN, Submodule.coe_add, Submodule.coe_add, Submodule.coe_smul,
      Submodule.coe_smul] at e
    exact e

end Crit

section Field

variable {r f : ℕ}

theorem eq_one_or_sq_eq_one_of_fix (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K)
    {τ : K ≃+* K} (h : ∀ μ, hK.bar μ = μ → τ μ = μ) : τ = 1 ∨ τ ^ 2 = 1 := by
  have key : ∀ c, τ c = c ∨ τ c = hK.bar c := by
    intro c
    have hs : τ (c + hK.bar c) = c + hK.bar c := h _ (by rw [map_add, hK.bar_bar, add_comm])
    have hn : τ (c * hK.bar c) = c * hK.bar c := h _ (by rw [map_mul, hK.bar_bar, mul_comm])
    have h0 : (τ c - c) * (τ c - hK.bar c) = 0 := by
      have e : (τ c - c) * (τ c - hK.bar c) =
          τ (c * c) - τ (c + hK.bar c) * τ c + τ (c * hK.bar c) := by
        rw [hs, hn, map_mul]
        ring
      rw [e, ← map_mul, ← map_sub, ← map_add]
      rw [show c * c - (c + hK.bar c) * c + c * hK.bar c = 0 by ring, map_zero]
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (sub_eq_zero.1 h1)
  by_cases h1 : ∀ c, τ c = c
  · exact Or.inl (RingEquiv.ext h1)
  push Not at h1
  obtain ⟨c₁, hc₁⟩ := h1
  have hc₁' : τ c₁ = hK.bar c₁ := (key c₁).resolve_left hc₁
  have hall : ∀ c, τ c = hK.bar c := by
    intro c₂
    by_contra hc₂
    have hc₂' : τ c₂ = c₂ := (key c₂).resolve_right hc₂
    rcases key (c₁ + c₂) with h3 | h3
    · rw [map_add, hc₁', hc₂'] at h3
      exact hc₁ (hc₁'.trans (add_right_cancel h3))
    · rw [map_add, map_add, hc₁', hc₂'] at h3
      exact hc₂ (hc₂'.trans (add_left_cancel h3))
  right
  refine RingEquiv.ext fun c => ?_
  show τ (τ c) = c
  rw [hall c, hall (hK.bar c), hK.bar_bar]

end Field

section Roots

theorem resBilin_apply (J : Matrix ι ι K) (U : Submodule K (ι → K)) (x y : U) :
    resBilin J U x y = Matrix.toBilin' J x y :=
  rfl

theorem transvection_mem_isomU_toBilin' {J : Matrix ι ι K} (hJ : ∀ x, Matrix.toBilin' J x x = 0)
    {U : Submodule K (ι → K)} (w : U) {c : K} (h : (c • LinearMap.flip (resBilin J U) w) w = 0) :
    LinearEquiv.transvection h ∈ isomU (Matrix.toBilin' J) U := by
  intro x x'
  have hJ' : (Matrix.toBilin' J).IsAlt := hJ
  have hww := hJ (w : ι → K)
  have hwx := LinearMap.IsAlt.neg hJ' (x' : ι → K) (w : ι → K)
  simp only [LinearEquiv.transvection.apply, Submodule.coe_add, Submodule.coe_smul,
    LinearMap.smul_apply, LinearMap.flip_apply, resBilin_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [← hwx, hww]
  ring

theorem transvection_mem_isomU_unitForm {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    {U : Submodule K (ι → K)} (w : U) (hww : unitForm σ (w : ι → K) (w : ι → K) = 0) {c : K}
    (hc : σ c + c = 0)
    (h : (c • ((unitForm σ).flip (w : ι → K)).comp U.subtype) w = 0) :
    LinearEquiv.transvection h ∈ isomU (unitForm σ) U := by
  intro x x'
  have hwx : unitForm σ (w : ι → K) (x' : ι → K) = σ (unitForm σ (x' : ι → K) (w : ι → K)) :=
    (unitForm_swap hσσ _ _).symm
  simp only [LinearEquiv.transvection.apply, Submodule.coe_add, Submodule.coe_smul,
    LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply,
    map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    map_mul]
  rw [hwx, hww]
  linear_combination (unitForm σ (x : ι → K) (w : ι → K) *
    σ (unitForm σ (x' : ι → K) (w : ι → K))) * hc

end Roots

section Main

theorem not_forall_semiConj_pow_zero [Finite K] {σ₀ : K →+* K} {U W : Submodule K (ι → K)}
    (hUW : IsCompl U W) (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ 4 ≤ Nat.card K))
    {A : GL ι K} {σ : K ≃+* K} {p : ℕ} (hσ : orderOf σ = p)
    (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) {y : GL ι K} (hyU : ∀ u ∈ U, glEquiv y u ∈ U)
    {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ¬ ∀ j ∈ blkI (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ₀] K) U W,
      y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j := by
  intro H
  have horth : ∀ u ∈ U, ∀ w ∈ W, (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ₀] K) u w = 0 ∧
      (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ₀] K) w u = 0 := fun _ _ _ _ => ⟨rfl, rfl⟩
  have heq := commutator_isomU_zero (σ := σ₀) U hdim
  have h2 : 2 ≤ finrank K U := by omega
  let b := finBasis K U
  let i₀ : Fin (finrank K U) := ⟨0, by omega⟩
  let i₁ : Fin (finrank K U) := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := Fin.ne_of_val_ne zero_ne_one
  have hfv : b.coord i₁ (b i₀) = 0 := by
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg hi]
  have hfc : ∀ c : K, (c • b.coord i₁) (b i₀) = 0 := fun c => by
    rw [LinearMap.smul_apply, hfv, smul_zero]
  have hmem : ∀ c : K, LinearEquiv.transvection (hfc c) ∈
      ⁅isomU (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ₀] K) U,
        isomU (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ₀] K) U⁆ := fun c => by
    rw [heq, MonoidHom.mem_ker]
    apply Units.ext
    rw [LinearEquiv.coe_det, LinearEquiv.transvection.coe_toLinearMap, LinearMap.transvection.det,
      hfc, add_zero, Units.val_one]
  have key : ∀ c : K, (σ ^ k) c = c := fun c =>
    pow_apply_eq_of_forall_semiConj_pow hUW horth hU hyU H ((b.coord i₁).smulRight (b i₀))
      (x₀ := b i₁) (by
        rw [LinearMap.smulRight_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
          one_smul]
        exact b.ne_zero i₀) (hmem 1) (hmem c)
      (fun u => by rw [LinearEquiv.transvection.apply, one_smul, LinearMap.smulRight_apply])
      (fun u => by
        rw [LinearEquiv.transvection.apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
          smul_eq_mul, mul_smul])
  exact pow_ne_one_of_lt_orderOf hk0.ne' (hσ ▸ hkp) (RingEquiv.ext fun c => key c)

theorem not_forall_semiConj_pow_toBilin' [Finite K] (hodd : Odd (Nat.card K))
    {J : Matrix ι ι K} (hJ : ∀ x, Matrix.toBilin' J x x = 0) {U W : Submodule K (ι → K)}
    (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, Matrix.toBilin' J u w = 0 ∧ Matrix.toBilin' J w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, Matrix.toBilin' J u u' = 0) → u = 0)
    (hdim : 2 ≤ finrank K U) (hexc : finrank K U ≠ 2 ∨ Nat.card K ≠ 3) {A : GL ι K}
    {σ : K ≃+* K} {p : ℕ} (hσ : orderOf σ = p) (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U)
    {y : GL ι K} (hyU : ∀ u ∈ U, glEquiv y u ∈ U) {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ¬ ∀ j ∈ blkI (Matrix.toBilin' J) U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j := by
  intro H
  have heq := commutator_eq_of_perfect (Subgroup.commutator_le_self _) le_rfl
    (isQuasisimple_isomU_toBilin' hodd hJ hnd hdim hexc).1
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨w, hw0⟩ := exists_ne (0 : U)
  obtain ⟨x₀, hx₀⟩ : ∃ x : U, resBilin J U x w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 ((resBilin_nondegenerate hJ hnd).2 w hcon)
  have hfc : ∀ c : K, (c • LinearMap.flip (resBilin J U) w) w = 0 := fun c => by
    rw [LinearMap.smul_apply, LinearMap.flip_apply, resBilin_isAlt hJ U w, smul_zero]
  have hmem : ∀ c : K, LinearEquiv.transvection (hfc c) ∈
      ⁅isomU (Matrix.toBilin' J) U, isomU (Matrix.toBilin' J) U⁆ := fun c => by
    rw [heq]
    exact transvection_mem_isomU_toBilin' hJ w (hfc c)
  have key : ∀ c : K, (σ ^ k) c = c := fun c =>
    pow_apply_eq_of_forall_semiConj_pow hUW horth hU hyU H
      ((LinearMap.flip (resBilin J U) w).smulRight w)
      (x₀ := x₀) (by
        rw [LinearMap.smulRight_apply, LinearMap.flip_apply]
        exact smul_ne_zero hx₀ hw0) (hmem 1) (hmem c)
      (fun u => by rw [LinearEquiv.transvection.apply, one_smul, LinearMap.smulRight_apply])
      (fun u => by
        rw [LinearEquiv.transvection.apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
          smul_eq_mul, mul_smul])
  exact pow_ne_one_of_lt_orderOf hk0.ne' (hσ ▸ hkp) (RingEquiv.ext fun c => key c)

theorem not_forall_semiConj_pow_unitForm {r f : ℕ}
    (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K) (hr : r ≠ 2)
    {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, unitForm hK.bar u w = 0 ∧ unitForm hK.bar w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, unitForm hK.bar u u' = 0) → u = 0)
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ r ^ f ≠ 3)) {A : GL ι K} {σ : K ≃+* K}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p)
    (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) {y : GL ι K} (hyU : ∀ u ∈ U, glEquiv y u ∈ U)
    {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ¬ ∀ j ∈ blkI (unitForm hK.bar) U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j := by
  intro H
  have heq := commutator_isomU_unitForm hK hr hnd hdim
  haveI : Fact r.Prime := ⟨hK.prime⟩
  haveI : Finite K := hK.finite
  have hE : Nat.card K = (r ^ f) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  let τ := CatalogueBUnitaryTwo.unitaryFieldConjugation r f hE
  have hτ : ∀ c, τ.toRingHom c = hK.bar c := fun c => by
    show τ c = hK.bar c
    rw [CatalogueBUnitaryTwo.unitaryFieldConjugation_apply,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
  obtain ⟨hsigma, hne, -⟩ := CatalogueBUnitaryTwo.unitaryFieldConjugation_data r f hE
  obtain ⟨b, hb⟩ := CatalogueBHermitian.exists_orthonormal_basis (unitFormU τ.toRingHom hτ U)
    (unitFormU_isSymm τ.toRingHom hτ hK.bar_bar U)
    (unitFormU_nondegenerate τ.toRingHom hτ hK.bar_bar hnd) hsigma hne
  have h2 : 2 ≤ finrank K U := by omega
  let i₀ : Fin (finrank K U) := ⟨0, by omega⟩
  let i₁ : Fin (finrank K U) := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := Fin.ne_of_val_ne zero_ne_one
  have hb' : ∀ i j, unitForm hK.bar ((b j : U) : ι → K) ((b i : U) : ι → K) =
      if i = j then 1 else 0 := hb
  obtain ⟨s, hs⟩ := CFSG.GH74.Generic.S45.Uni.exists_norm_eq hK
    (show hK.bar (-1) = -1 by rw [map_neg, map_one]) (neg_ne_zero.2 one_ne_zero)
  let w : U := b i₀ + s • b i₁
  have hb00 := hb' i₀ i₀
  have hb01 := hb' i₀ i₁
  have hb10 := hb' i₁ i₀
  have hb11 := hb' i₁ i₁
  rw [if_pos rfl] at hb00 hb11
  rw [if_neg hi] at hb01
  rw [if_neg (Ne.symm hi)] at hb10
  have hww : unitForm hK.bar (w : ι → K) (w : ι → K) = 0 := by
    simp only [w, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, map_smulₛₗ,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hb00, hb01, hb10, hb11]
    linear_combination hs
  have hx₀w : unitForm hK.bar ((b i₀ : U) : ι → K) (w : ι → K) = 1 := by
    simp only [w, Submodule.coe_add, Submodule.coe_smul, map_add, map_smulₛₗ, smul_eq_mul]
    rw [hb00, hb10, mul_zero, add_zero]
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, Submodule.coe_zero, map_zero] at hx₀w
    exact zero_ne_one hx₀w
  obtain ⟨δ, hδ0, hδ⟩ := CFSG.GH74.Generic.S45.Uni.exists_bar_neg hK
  let f₀ : U →ₗ[K] K := ((unitForm hK.bar).flip (w : ι → K)).comp U.subtype
  have hf₀ : ∀ x : U, f₀ x = unitForm hK.bar (x : ι → K) (w : ι → K) := fun x => rfl
  have hfc : ∀ μ : K, ((μ * δ) • f₀) w = 0 := fun μ => by
    rw [LinearMap.smul_apply, hf₀, hww, smul_zero]
  have hmem : ∀ μ : K, hK.bar μ = μ → LinearEquiv.transvection (hfc μ) ∈
      ⁅isomU (unitForm hK.bar) U, isomU (unitForm hK.bar) U⁆ := fun μ hμ => by
    rw [heq]
    refine Subgroup.mem_inf.2 ⟨transvection_mem_isomU_unitForm hK.bar_bar w hww
      (by rw [map_mul, hμ, hδ]; ring) (hfc μ), MonoidHom.mem_ker.2 (Units.ext ?_)⟩
    rw [LinearEquiv.coe_det, LinearEquiv.transvection.coe_toLinearMap, LinearMap.transvection.det,
      hfc, add_zero, Units.val_one]
  have key : ∀ μ : K, hK.bar μ = μ → (σ ^ k) μ = μ := fun μ hμ =>
    pow_apply_eq_of_forall_semiConj_pow hUW horth hU hyU H ((δ • f₀).smulRight w)
      (x₀ := b i₀) (by
        rw [LinearMap.smulRight_apply, LinearMap.smul_apply, hf₀, hx₀w, smul_eq_mul, mul_one]
        exact smul_ne_zero hδ0 hw0) (hmem 1 (map_one _)) (hmem μ hμ)
      (fun u => by
        rw [LinearEquiv.transvection.apply, one_mul, LinearMap.smulRight_apply])
      (fun u => by
        rw [LinearEquiv.transvection.apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
          LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc, mul_smul])
  rcases eq_one_or_sq_eq_one_of_fix hK key with h1 | h1
  · exact pow_ne_one_of_lt_orderOf hk0.ne' (hσ ▸ hkp) h1
  · rw [← pow_mul] at h1
    have hd := orderOf_dvd_of_pow_eq_one h1
    rw [hσ] at hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with hk | hk
    · exact absurd (Nat.le_of_dvd hk0 hk) (by omega)
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hk)

theorem not_forall_semiConj_pow_polarBilin [Finite K] (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K (ι → K)) {U W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W,
      QuadraticMap.polarBilin Q u w = 0 ∧ QuadraticMap.polarBilin Q w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, QuadraticMap.polarBilin Q u u' = 0) → u = 0)
    (hdim : 3 ≤ finrank K U) {A : GL ι K} {σ : K ≃+* K} {p : ℕ} (hσ : orderOf σ = p)
    (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) {y : GL ι K} (hyU : ∀ u ∈ U, glEquiv y u ∈ U)
    {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ¬ ∀ j ∈ blkI (QuadraticMap.polarBilin Q) U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j := by
  intro H
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hO := isomU_polarBilin_eq h2 Q U
  have hK2 : 2 < Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    omega
  set Q₀ := Q.comp U.subtype
  obtain ⟨-, ⟨P⟩, hP⟩ :=
    CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar hK2 Q₀
      (polarBilin_comp_nondegenerate Q hnd) hdim
  have hperp := CFSG.ClassicalGroups.Orthogonal.HypPair.finrank_perp_add_two P
  have hpos : 0 < finrank K P.perp := by omega
  haveI : Nontrivial P.perp := Module.nontrivial_of_finrank_pos (R := K) hpos
  obtain ⟨⟨w, hw⟩, hw0⟩ := exists_ne (0 : P.perp)
  have hw0' : w ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hew := (CFSG.ClassicalGroups.Orthogonal.HypPair.mem_perp.1 hw).1
  have hfw := (CFSG.ClassicalGroups.Orthogonal.HypPair.mem_perp.1 hw).2
  let N₁ : U →ₗ[K] U := ((QuadraticMap.polarBilin Q₀).flip P.e).smulRight w -
    ((QuadraticMap.polarBilin Q₀).flip w).smulRight P.e
  let N₂ : U →ₗ[K] U := (-Q₀ w) • ((QuadraticMap.polarBilin Q₀).flip P.e).smulRight P.e
  have hN₁ : ∀ x : U, N₁ x = QuadraticMap.polar Q₀ x P.e • w - QuadraticMap.polar Q₀ x w • P.e :=
    fun x => rfl
  have hN₂ : ∀ x : U, N₂ x = (-(Q₀ w * QuadraticMap.polar Q₀ x P.e)) • P.e := fun x => by
    show (-Q₀ w) • (QuadraticMap.polar Q₀ x P.e • P.e) = _
    rw [smul_smul, neg_mul]
  have hR : ∀ a : K, ∃ g ∈ ⁅isomU (QuadraticMap.polarBilin Q) U,
      isomU (QuadraticMap.polarBilin Q) U⁆, ∀ x : U, g x = x + a • N₁ x + (a * a) • N₂ x := by
    intro a
    obtain ⟨g, hg, hge⟩ := ((hP P).1 w hw a).1
    refine ⟨g, by rw [hO]; exact hg, fun x => ?_⟩
    have e := congrArg (fun M : U →ₗ[K] U => M x) hge
    simp only [LinearEquiv.coe_coe] at e
    rw [e, CFSG.LocalAnalysis.ComponentInitial.orthElementaryMap_apply, hN₁, hN₂,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq,
      CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq]
    module
  have he0 := P.e_ne_zero
  obtain ⟨x₀, hx₁, hx₂⟩ : ∃ x₀ : U, N₁ x₀ ≠ 0 ∧ N₂ x₀ = 0 := by
    by_cases hQw : Q₀ w = 0
    · refine ⟨P.f, ?_, ?_⟩
      · rw [hN₁, P.polar_fe, one_smul, hfw, zero_smul, sub_zero]
        exact hw0'
      · rw [hN₂, hQw, zero_mul, neg_zero, zero_smul]
    · refine ⟨w, ?_, ?_⟩
      · rw [hN₁, QuadraticMap.polar_comm, hew, zero_smul, zero_sub,
          CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, neg_ne_zero]
        exact smul_ne_zero (mul_ne_zero h2 hQw) he0
      · rw [hN₂, QuadraticMap.polar_comm, hew, mul_zero, neg_zero, zero_smul]
  have hTU : ∀ u ∈ U, glEquiv y ((ModelGen.semiMap A σ)^[k] u) ∈ U :=
    fun u hu => hyU _ (semiMap_iterate_mem hU k hu)
  have key : ∀ c : K, (σ ^ k) c = c := fun c =>
    eq_of_commute_one_add_sq (T := fun v => glEquiv y ((ModelGen.semiMap A σ)^[k] v))
      (ρ := fun c => (σ ^ k) c) (fun v w => by rw [semiMap_iterate_add, map_add])
      (fun c v => by rw [semiMap_iterate_smul, map_smul])
      ((glEquiv y).injective.comp (Function.Injective.iterate (ModelGen.semiMap A σ).injective k))
      hTU h2 N₁ N₂ hx₁ hx₂ (fun a u => by
        obtain ⟨g, hg, hgN⟩ := hR a
        have e := commute_of_forall_semiConj_pow hUW horth H hg u (hTU u u.2)
        rw [hgN, hgN] at e
        simpa only [Submodule.coe_add, Submodule.coe_smul] using e) c
  exact pow_ne_one_of_lt_orderOf hk0.ne' (hσ ▸ hkp) (RingEquiv.ext fun c => key c)

end Main

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
