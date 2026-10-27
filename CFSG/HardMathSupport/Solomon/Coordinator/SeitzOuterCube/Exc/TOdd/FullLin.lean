module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.FullAbs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

section MatrixLemmas

open Polynomial Matrix

variable {F : Type*} [Field F]

theorem charpoly_fin_three' (M : Matrix (Fin 3) (Fin 3) F) :
    M.charpoly = X ^ 3 + C (M.charpoly.coeff 2) * X ^ 2 + C (M.charpoly.coeff 1) * X
      + C (M.charpoly.coeff 0) := by
  have hdeg : M.charpoly.natDegree = 3 := by
    simpa using M.charpoly_natDegree_eq_dim
  have hmonic := M.charpoly_monic
  ext i
  by_cases hi : i ∈ Finset.range 4
  · fin_cases hi
    · simp [coeff_X, coeff_C]
    · simp [coeff_X, coeff_C]
    · simp [coeff_X, coeff_C]
    · simpa [leadingCoeff, hdeg, coeff_X, coeff_C] using hmonic.leadingCoeff
  · rw [Finset.mem_range, not_lt] at hi
    have : M.charpoly.coeff i = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      omega
    rw [this]
    have h3 : i ≠ 3 := by omega
    have h2 : i ≠ 2 := by omega
    have h1 : 1 ≠ i := by omega
    have h0 : i ≠ 0 := by omega
    simp [coeff_X, coeff_C, coeff_X_pow, h3, h2, h1, h0]

theorem det_sub_eq_zero {S : Matrix (Fin 3) (Fin 3) F} (hS3 : S ^ 3 = 1) (hdet : S.det = 1)
    (hns : ∀ r : F, S ≠ r • 1) {a : F} (ha : a ^ 3 = 1) :
    (a • (1 : Matrix (Fin 3) (Fin 3) F) - S).det = 0 := by
  have hχ := charpoly_fin_three' S
  set c2 := S.charpoly.coeff 2 with hc2
  set c1 := S.charpoly.coeff 1 with hc1
  set c0 := S.charpoly.coeff 0 with hc0
  have hdet' : c0 = -1 := by
    have := Matrix.det_eq_sign_charpoly_coeff S
    rw [hdet, Fintype.card_fin, ← hc0] at this
    linear_combination this
  have hCH := Matrix.aeval_self_charpoly S
  rw [hχ] at hCH
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, hS3, hdet'] at hCH
  have h1 : c2 • S ^ 2 + c1 • S = 0 := by
    have e : c2 • S ^ 2 + c1 • S =
        1 + c2 • S ^ 2 + c1 • S + (-1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      module
    rw [e]; exact hCH
  have h2 : c2 • S + c1 • (1 : Matrix (Fin 3) (Fin 3) F) = 0 := by
    have e4 : S ^ 2 * S ^ 2 = S := by
      rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hS3, one_mul]
    have e3 : S * S ^ 2 = 1 := by rw [← pow_succ']; exact hS3
    have : (c2 • S ^ 2 + c1 • S) * S ^ 2 = 0 := by rw [h1, zero_mul]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, e4, e3] at this
    exact this
  have hc2z : c2 = 0 := by
    by_contra hne
    apply hns (-(c1 / c2))
    have h3 : c2 • S = -(c1 • (1 : Matrix (Fin 3) (Fin 3) F)) := eq_neg_of_add_eq_zero_left h2
    calc S = c2⁻¹ • (c2 • S) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (-(c1 / c2)) • (1 : Matrix (Fin 3) (Fin 3) F) := by
        rw [h3, smul_neg, smul_smul, neg_smul]; simp [div_eq_inv_mul]
  have hc1z : c1 = 0 := by
    rw [hc2z, zero_smul, zero_add] at h2
    have := congrFun (congrFun h2 0) 0
    simpa using this
  have hev := Matrix.eval_charpoly S a
  rw [hχ] at hev
  have e : (a • (1 : Matrix (Fin 3) (Fin 3) F) - S) = Matrix.scalar (Fin 3) a - S := by
    simp [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  rw [e, ← hev]
  simp [hc2z, hc1z, hdet', ha]

theorem exists_eigenbasis {S : Matrix (Fin 3) (Fin 3) F} (hS3 : S ^ 3 = 1) (hdet : S.det = 1)
    (hns : ∀ r : F, S ≠ r • 1) {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) F, IsUnit P ∧ S * P = P * Matrix.diagonal ![1, ω, ω ^ 2] := by
  set a : Fin 3 → F := ![1, ω, ω ^ 2] with ha
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    intro i
    fin_cases i
    · simp [ha]
    · simpa [ha] using hω3
    · show (ω ^ 2) ^ 3 = 1
      rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have h12 : ω ^ 2 ≠ 1 := by
    intro h
    have h3 : ω ^ 3 = ω * ω ^ 2 := by ring
    rw [h, mul_one, hω3] at h3
    exact hω1 h3.symm
  have h1ω2 : ω ≠ ω ^ 2 := by
    intro h
    have h3 : ω * 1 = ω * ω := by rw [mul_one, ← sq]; exact h
    exact hω1 (mul_left_cancel₀ hω0 h3).symm
  have hωm1 : ω ≠ -1 := fun h => h12 (by rw [h]; norm_num)
  have hinj : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [ha] at hij ⊢ <;> tauto
  have hex : ∀ i, ∃ v : Fin 3 → F, v ≠ 0 ∧ S *ᵥ v = a i • v := by
    intro i
    have h0 := det_sub_eq_zero hS3 hdet hns (ha3 i)
    obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmv
    exact hmv.symm
  choose v hv0 hv using hex
  have hli : LinearIndependent F v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' S) a hinj v (fun i => ?_)
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa using hv i
  let P : Matrix (Fin 3) (Fin 3) F := Matrix.of fun r c => v c r
  have hP : IsUnit P := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  refine ⟨P, hP, ?_⟩
  ext r c
  have := congrFun (hv c) r
  simp only [P, Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct] at this ⊢
  simpa [Matrix.diagonal_apply, mul_comm] using this

theorem exists_commute_det_eq {S : Matrix.SpecialLinearGroup (Fin 3) F}
    (hS3 : (S : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1)
    (hns : ∀ r : F, (S : Matrix (Fin 3) (Fin 3) F) ≠ r • 1)
    {ω : F} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (μ : Fˣ) :
    ∃ Z : Matrix.GeneralLinearGroup (Fin 3) F,
      Z * Matrix.SpecialLinearGroup.toGL S = Matrix.SpecialLinearGroup.toGL S * Z ∧
        Matrix.GeneralLinearGroup.det Z = μ := by
  obtain ⟨P, hP, hSP⟩ := exists_eigenbasis hS3 S.det_coe hns hω3 hω1
  have hPdet : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).1 hP).ne_zero
  set Δ : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![1, ω, ω ^ 2] with hΔ
  set D' : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![(μ : F), 1, 1] with hD'
  have hD'det : D'.det = μ := by simp [D', Matrix.det_diagonal, Fin.prod_univ_three]
  have hDΔ : D' * Δ = Δ * D' := by
    rw [hD', hΔ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  let Pu : Matrix.GeneralLinearGroup (Fin 3) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero P hPdet
  let Du : Matrix.GeneralLinearGroup (Fin 3) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero D' (by rw [hD'det]; exact μ.ne_zero)
  have hPu : (Pu : Matrix (Fin 3) (Fin 3) F) = P := rfl
  have hDu : (Du : Matrix (Fin 3) (Fin 3) F) = D' := rfl
  refine ⟨Pu * Du * Pu⁻¹, ?_, ?_⟩
  · apply Units.ext
    have h1 : ((Pu⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * P =
        1 := by
      rw [← hPu]; exact Units.inv_mul Pu
    have h2 : P * ((Pu⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        1 := by
      rw [← hPu]; exact Units.mul_inv Pu
    set Pinv := ((Pu⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      with hPinv
    have hS : (S : Matrix (Fin 3) (Fin 3) F) = P * Δ * Pinv := by
      rw [← hSP, Matrix.mul_assoc, h2, Matrix.mul_one]
    show P * D' * Pinv * (S : Matrix (Fin 3) (Fin 3) F) =
      (S : Matrix (Fin 3) (Fin 3) F) * (P * D' * Pinv)
    rw [hS]
    calc P * D' * Pinv * (P * Δ * Pinv) = P * D' * (Pinv * P) * Δ * Pinv := by
          simp only [Matrix.mul_assoc]
      _ = P * (D' * Δ) * Pinv := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P * (Δ * D') * Pinv := by rw [hDΔ]
      _ = P * Δ * (Pinv * P) * D' * Pinv := by
          rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P * Δ * Pinv * (P * D' * Pinv) := by simp only [Matrix.mul_assoc]
  · have hdetDu : Matrix.GeneralLinearGroup.det Du = μ := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hDu, hD'det]
    rw [map_mul, map_mul, map_inv, hdetDu, mul_right_comm, mul_inv_cancel, one_mul]

theorem exists_primitive_cube_root [Finite F] (h3 : 3 ∣ Nat.card F - 1) :
    ∃ ω : F, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf ζ = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  have h := orderOf_pow_orderOf_div (n := 3) (orderOf_pos ζ).ne' (hord ▸ h3)
  refine ⟨((ζ ^ (orderOf ζ / 3) : Fˣ) : F), ?_, ?_⟩
  · have := pow_orderOf_eq_one (ζ ^ (orderOf ζ / 3))
    rw [h] at this
    simpa using congrArg Units.val this
  · intro h1
    have : ζ ^ (orderOf ζ / 3) = 1 := Units.ext h1
    rw [this, orderOf_one] at h
    omega

theorem exists_special_conj_eq [Finite F] (h3 : 3 ∣ Nat.card F - 1)
    {S : Matrix.SpecialLinearGroup (Fin 3) F} (hS3 : S ^ 3 = 1)
    (hns : ∀ r : F, (S : Matrix (Fin 3) (Fin 3) F) ≠ r • 1)
    (N : Matrix.GeneralLinearGroup (Fin 3) F) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 3) F,
      Matrix.SpecialLinearGroup.toGL (M * S * M⁻¹) =
        N * Matrix.SpecialLinearGroup.toGL S * N⁻¹ := by
  obtain ⟨ω, hω3, hω1⟩ := exists_primitive_cube_root h3
  have hS3' : (S : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hS3]
    rfl
  obtain ⟨Z, hZ, hZdet⟩ := exists_commute_det_eq hS3' hns hω3 hω1
    (Matrix.GeneralLinearGroup.det N)⁻¹
  obtain ⟨M, hM⟩ : ∃ M : Matrix.SpecialLinearGroup (Fin 3) F,
      Matrix.SpecialLinearGroup.toGL M = N * Z := by
    have h : N * Z ∈ (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 3) F →* Fˣ).ker := by
      rw [MonoidHom.mem_ker, map_mul, hZdet, mul_inv_cancel]
    rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at h
    exact h
  refine ⟨M, ?_⟩
  simp only [map_mul, map_inv, hM]
  calc N * Z * Matrix.SpecialLinearGroup.toGL S * (N * Z)⁻¹
      = N * (Z * Matrix.SpecialLinearGroup.toGL S) * Z⁻¹ * N⁻¹ := by group
    _ = N * (Matrix.SpecialLinearGroup.toGL S * Z) * Z⁻¹ * N⁻¹ := by rw [hZ]
    _ = N * Matrix.SpecialLinearGroup.toGL S * N⁻¹ := by group

end MatrixLemmas

section ActsVia

variable {G : Type*} [Group G] {F : Type*} [Field F]

@[expose] def LayerActsVia {x : G} (e : layerOf x ≃* Matrix.SpecialLinearGroup (Fin 3) F) (g : G)
    (N : Matrix.GeneralLinearGroup (Fin 3) F) : Prop :=
  ∀ d d' : layerOf x, (d' : G) = g * d * g⁻¹ →
    ((e d' : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (N : Matrix (Fin 3) (Fin 3) F) * ((e d : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * ((N⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F)

variable {x : G} {e : layerOf x ≃* Matrix.SpecialLinearGroup (Fin 3) F} {g g' : G}
  {N N' : Matrix.GeneralLinearGroup (Fin 3) F}

theorem layerActsVia_iff :
    LayerActsVia e g N ↔ ∀ d d' : layerOf x, (d' : G) = g * d * g⁻¹ →
      Matrix.SpecialLinearGroup.toGL (e d') = N * Matrix.SpecialLinearGroup.toGL (e d) * N⁻¹ := by
  constructor
  · intro h d d' hd
    apply Units.ext
    simpa using h d d' hd
  · intro h d d' hd
    have := congrArg
      (fun u : Matrix.GeneralLinearGroup (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) (h d d' hd)
    simpa using this

theorem LayerActsVia.one :
    LayerActsVia e (1 : G) (1 : Matrix.GeneralLinearGroup (Fin 3) F) := by
  rw [layerActsVia_iff]
  intro d d' hd
  have : d' = d := Subtype.ext (by simpa using hd)
  subst this
  simp

theorem LayerActsVia.mul (hg : g ∈ Subgroup.centralizer ({x} : Set G)) (hN : LayerActsVia e g N)
    (hN' : LayerActsVia e g' N') : LayerActsVia e (g' * g) (N' * N) := by
  rw [layerActsVia_iff] at hN hN' ⊢
  intro d d' hd
  have hd'' : g * (d : G) * g⁻¹ ∈ layerOf x := conj_mem_layerOf hg d.2
  have h1 := hN d ⟨g * d * g⁻¹, hd''⟩ rfl
  have h2 := hN' ⟨g * d * g⁻¹, hd''⟩ d' (by rw [hd]; group)
  rw [h2, h1]
  group

theorem LayerActsVia.pow (hg : g ∈ Subgroup.centralizer ({x} : Set G)) (hN : LayerActsVia e g N)
    (k : ℕ) : LayerActsVia e (g ^ k) (N ^ k) := by
  induction k with
  | zero => simpa using (LayerActsVia.one (e := e))
  | succ k ih =>
    rw [pow_succ', pow_succ']
    exact LayerActsVia.mul (Subgroup.pow_mem _ hg k) ih hN

theorem mem_sup_of_actsVia (hg : g ∈ Subgroup.centralizer ({x} : Set G)) (hN : LayerActsVia e g N)
    (w : Fˣ) (hw : w ^ 3 = Matrix.GeneralLinearGroup.det N) : g ∈ layerOf x ⊔ torusOf x := by
  rw [layerActsVia_iff] at hN
  set c : Matrix.GeneralLinearGroup (Fin 3) F :=
    Matrix.GeneralLinearGroup.scalar (Fin 3) w⁻¹ with hc
  have hdet1 : Matrix.GeneralLinearGroup.det (c * N) = 1 := by
    rw [map_mul, hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, ← hw,
      inv_mul_cancel]
  obtain ⟨M, hM⟩ : ∃ M : Matrix.SpecialLinearGroup (Fin 3) F,
      Matrix.SpecialLinearGroup.toGL M = c * N := by
    have h : c * N ∈ (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 3) F →* Fˣ).ker := hdet1
    rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at h
    exact h
  set r : layerOf x := e.symm M with hr
  have hconj : ∀ d : layerOf x, g * (d : G) * g⁻¹ = (r : G) * d * (r : G)⁻¹ := by
    intro d
    have h1 := hN d ⟨g * d * g⁻¹, conj_mem_layerOf hg d.2⟩ rfl
    have h2 : e ⟨g * d * g⁻¹, conj_mem_layerOf hg d.2⟩ = e (r * d * r⁻¹) := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      have he : e r = M := e.apply_symm_apply M
      rw [h1]
      simp only [map_mul, map_inv, he, hM]
      have hcomm : ∀ B : Matrix.GeneralLinearGroup (Fin 3) F, c * B = B * c :=
        Matrix.GeneralLinearGroup.scalar_commute w⁻¹
      calc N * Matrix.SpecialLinearGroup.toGL (e d) * N⁻¹
          = (N * Matrix.SpecialLinearGroup.toGL (e d) * N⁻¹) * c * c⁻¹ := by group
        _ = c * (N * Matrix.SpecialLinearGroup.toGL (e d) * N⁻¹) * c⁻¹ := by rw [hcomm]
        _ = _ := by group
    have h3 := e.injective h2
    simpa using congrArg Subtype.val h3
  have hrC : (r : G) ∈ Subgroup.centralizer ({x} : Set G) := layerOf_le_centralizer x r.2
  have hl : (r : G)⁻¹ * g ∈ torusOf x := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hrC) hg, ?_⟩
    show (r : G)⁻¹ * g ∈ Subgroup.centralizer (layerOf x : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := hconj ⟨d, hd⟩
    simp only at h
    calc d * ((r : G)⁻¹ * g) = (r : G)⁻¹ * ((r : G) * d * (r : G)⁻¹) * g := by group
      _ = (r : G)⁻¹ * (g * d * g⁻¹) * g := by rw [h]
      _ = (r : G)⁻¹ * g * d := by group
  have := Subgroup.mul_mem_sup r.2 hl
  simpa using this

end ActsVia

theorem exists_cube_mul_pow {F : Type*} [Field F] [Finite F] {u v : Fˣ}
    (hu : ¬ ∃ w : Fˣ, w ^ 3 = u) : ∃ k : ℕ, ∃ w : Fˣ, w ^ 3 = v * u ^ k := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hζ u)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hζ v)
  have ha : ¬ (3 : ℤ) ∣ a := by
    rintro ⟨c, hc⟩
    refine hu ⟨ζ ^ c, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, hc]
    norm_num [mul_comm]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (3 : ℤ) ∣ b + k * a := by
    have h1 : a % 3 = 1 ∨ a % 3 = 2 := by omega
    have h2 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2
    · exact ⟨0, by omega⟩
    · exact ⟨2, by push_cast; omega⟩
    · exact ⟨1, by push_cast; omega⟩
    · exact ⟨0, by omega⟩
    · exact ⟨1, by push_cast; omega⟩
    · exact ⟨2, by push_cast; omega⟩
  obtain ⟨c, hc⟩ := hk
  refine ⟨k, ζ ^ c, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  congr 1
  push_cast
  linarith

section M1M2

variable {G : Type*} [Group G] {F : Type*} [Field F] [Finite F] {x : G}

theorem layer_M1_of_linear (e : layerOf x ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hact : ∀ g ∈ Subgroup.centralizer ({x} : Set G),
      ∃ N : Matrix.GeneralLinearGroup (Fin 3) F, LayerActsVia e g N) :
    ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∉ layerOf x ⊔ torusOf x →
      ∀ g' ∈ Subgroup.centralizer ({x} : Set G), ∃ k : ℕ, g' * g ^ k ∈ layerOf x ⊔ torusOf x := by
  intro g hg hgn g' hg'
  obtain ⟨N, hN⟩ := hact g hg
  obtain ⟨N', hN'⟩ := hact g' hg'
  have hu : ¬ ∃ w : Fˣ, w ^ 3 = Matrix.GeneralLinearGroup.det N := fun ⟨w, hw⟩ =>
    hgn (mem_sup_of_actsVia hg hN w hw)
  obtain ⟨k, w, hw⟩ := exists_cube_mul_pow (v := Matrix.GeneralLinearGroup.det N') hu
  refine ⟨k, ?_⟩
  refine mem_sup_of_actsVia (N := N' * N ^ k)
    (Subgroup.mul_mem _ hg' (Subgroup.pow_mem _ hg k))
    (LayerActsVia.mul (Subgroup.pow_mem _ hg k) (hN.pow hg k) hN') w ?_
  rw [map_mul, map_pow]
  exact hw

theorem layer_M2_of_linear (h3 : 3 ∣ Nat.card F - 1)
    (hZD : ∀ w ∈ layerOf x, (∀ d ∈ layerOf x, w * d = d * w) → w ∈ Subgroup.zpowers x)
    (e : layerOf x ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hact : ∀ g ∈ Subgroup.centralizer ({x} : Set G),
      ∃ N : Matrix.GeneralLinearGroup (Fin 3) F, LayerActsVia e g N) :
    ∀ s ∈ layerOf x, s ^ 3 = 1 → s ∉ Subgroup.zpowers x →
      ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∃ h ∈ layerOf x, h * s * h⁻¹ = g * s * g⁻¹ := by
  intro s hs hs3 hsx g hg
  set d : layerOf x := ⟨s, hs⟩ with hd
  have hS3 : e d ^ 3 = 1 := by
    have : d ^ 3 = 1 := Subtype.ext (by simpa using hs3)
    rw [← map_pow, this, map_one]
  have hns : ∀ r : F, (e d : Matrix (Fin 3) (Fin 3) F) ≠ r • 1 := by
    intro r hr
    apply hsx
    refine hZD s hs fun d₂ hd₂ => ?_
    have hcomm : e d * e ⟨d₂, hd₂⟩ = e ⟨d₂, hd₂⟩ * e d := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hr]
      simp
    have := e.injective (by simpa using hcomm : e (d * ⟨d₂, hd₂⟩) = e (⟨d₂, hd₂⟩ * d))
    simpa using congrArg Subtype.val this
  obtain ⟨N, hN⟩ := hact g hg
  rw [layerActsVia_iff] at hN
  have hd' : g * s * g⁻¹ ∈ layerOf x := conj_mem_layerOf hg hs
  have h1 := hN d ⟨g * s * g⁻¹, hd'⟩ rfl
  obtain ⟨M, hM⟩ := exists_special_conj_eq h3 hS3 hns N
  refine ⟨((e.symm M : layerOf x) : G), (e.symm M).2, ?_⟩
  have h2 : e ⟨g * s * g⁻¹, hd'⟩ = e (e.symm M * d * (e.symm M)⁻¹) := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [h1, ← hM]
    simp only [map_mul, map_inv, e.apply_symm_apply]
  have h3 := e.injective h2
  simpa using (congrArg Subtype.val h3).symm

end M1M2

section Packaged

variable {G : Type*} [Group G] [Finite G] {x a' : G}

theorem centralizer_le_of_layer_linear (hx3 : x ^ 3 = 1)
    (hxD : x ∈ layerOf x)
    (hZD : ∀ w ∈ layerOf x, (∀ d ∈ layerOf x, w * d = d * w) → w ∈ Subgroup.zpowers x)
    (hZ3 : ∀ z ∈ Subgroup.centralizer (layerOf x : Set G),
      (∃ k : ℕ, z ^ (3 ^ k) = 1) → z ∈ Subgroup.zpowers x)
    (ha'C : a' * x = x * a') (ha'3 : a' ^ 3 = 1) (ha'x : a' ∉ Subgroup.zpowers x)
    {F : Type*} [Field F] [Finite F] (h3 : 3 ∣ Nat.card F - 1)
    (e : layerOf x ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hact : ∀ g ∈ Subgroup.centralizer ({x} : Set G),
      ∃ N : Matrix.GeneralLinearGroup (Fin 3) F, ∀ d d' : layerOf x,
        (d' : G) = g * d * g⁻¹ →
          ((e d' : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
            (N : Matrix (Fin 3) (Fin 3) F) * ((e d : Matrix.SpecialLinearGroup (Fin 3) F) :
              Matrix (Fin 3) (Fin 3) F) * ((N⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) :
                Matrix (Fin 3) (Fin 3) F))
    {Γ : Subgroup G} (hDΓ : layerOf x ≤ Γ)
    (hΓ : ∀ l ∈ Subgroup.centralizer ({x} : Set G), l * a' = a' * l → l ∈ Γ) :
    Subgroup.centralizer ({x} : Set G) ≤ Γ :=
  centralizer_le_of_layer hx3 hxD hZD hZ3 ha'C ha'3 ha'x (layer_M1_of_linear e hact)
    (layer_M2_of_linear h3 hZD e hact) hDΓ hΓ

end Packaged

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
