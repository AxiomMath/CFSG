module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OutL
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace UnitaryOut

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def uStar {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  (M.map h.bar)ᵀ

theorem uStar_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) K) :
    uStar h (M * N) = uStar h N * uStar h M := by
  rw [uStar, uStar, uStar, Matrix.map_mul, transpose_mul]

theorem uStar_one {n : ℕ} : uStar h (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [uStar, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]

@[expose] noncomputable def uMat (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {A | uStar h (A : Matrix (Fin n) (Fin n) K) * A = 1}
  one_mem' := by
    change uStar h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * _ = 1
    rw [Units.val_one, uStar_one, Matrix.one_mul]
  mul_mem' {A B} hA hB := by
    change uStar h ((A * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * _ = 1
    have hA' : uStar h (A : Matrix (Fin n) (Fin n) K) * A = 1 := hA
    have hB' : uStar h (B : Matrix (Fin n) (Fin n) K) * B = 1 := hB
    rw [Units.val_mul, uStar_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (uStar h (A : Matrix (Fin n) (Fin n) K)) (A : Matrix (Fin n) (Fin n) K),
      hA', Matrix.one_mul, hB']
  inv_mem' {A} hA := by
    have hA' : uStar h (A : Matrix (Fin n) (Fin n) K) * A = 1 := hA
    change uStar h ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * _ = 1
    have h1 : uStar h ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        uStar h (A : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← uStar_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, uStar_one]
    have h2 : uStar h ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = A := by
      calc uStar h ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          = uStar h ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (uStar h (A : Matrix (Fin n) (Fin n) K) * A) := by rw [hA', Matrix.mul_one]
        _ = A := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [h2, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem mem_uMat {n : ℕ} {A : GL (Fin n) K} :
    A ∈ uMat h n ↔ ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * A = 1 := by
  rfl

theorem glAut_mem_uMat [Finite K] {n : ℕ} (φ : K ≃+* K) {A : GL (Fin n) K}
    (hA : A ∈ uMat h n) : glAut φ A ∈ uMat h n := by
  have hcomm : ∀ c, h.bar (φ c) = φ (h.bar c) := by
    intro c
    rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]
  rw [mem_uMat] at hA ⊢
  have e1 : ((glAut φ A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K).map φ := rfl
  rw [e1]
  have e2 : ((A : Matrix (Fin n) (Fin n) K).map φ).map h.bar =
      ((A : Matrix (Fin n) (Fin n) K).map h.bar).map φ := by
    ext i j
    simp [hcomm]
  rw [e2, ← Matrix.transpose_map, ← Matrix.map_mul, hA, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem det_pow_eq_one_of_mem_uMat {n : ℕ} {A : GL (Fin n) K} (hA : A ∈ uMat h n) :
    (A : Matrix (Fin n) (Fin n) K).det ^ (p ^ f + 1) = 1 := by
  rw [mem_uMat] at hA
  have h1 := congrArg Matrix.det hA
  have h2 : ((A : Matrix (Fin n) (Fin n) K).map h.bar).det =
      h.bar (A : Matrix (Fin n) (Fin n) K).det := by
    rw [RingHom.map_det]
    rfl
  rw [det_mul, det_transpose, h2, det_one, UnitaryFieldData.bar_apply, ← pow_succ] at h1
  exact h1

theorem det_glAut' {n : ℕ} (φ : K ≃+* K) (A : GL (Fin n) K) :
    ((glAut φ A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      φ (A : Matrix (Fin n) (Fin n) K).det := by
  change ((A : Matrix (Fin n) (Fin n) K).map φ).det = _
  rw [show φ (A : Matrix (Fin n) (Fin n) K).det =
    (φ : K →+* K) (A : Matrix (Fin n) (Fin n) K).det from rfl, RingHom.map_det]
  rfl

include h in
theorem out_comm_statedSU_four (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1)
    (u v : MulAut (StatedProj (StatedSU 4 (p ^ f) K))) :
    ⁅u, v⁆ ∈ (MulAut.conj : StatedProj (StatedSU 4 (p ^ f) K) →*
      MulAut (StatedProj (StatedSU 4 (p ^ f) K))).range := by
  classical
  have : Finite K := h.finite
  set Z := (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) with hZ
  set θ : unitarySU p f K 4 →* StatedProj (StatedSU 4 (p ^ f) K) := QuotientGroup.mk' Z
    with hθdef
  have hθ : Function.Surjective θ := QuotientGroup.mk'_surjective Z
  have hker : θ.ker ≤ Subgroup.center (unitarySU p f K 4) := by
    rw [hθdef, QuotientGroup.ker_mk']
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨c, hc⟩ := hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
    have hcen : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    exact Subgroup.mem_center_iff.mp hcen _
  have hq5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
    have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
    omega
  obtain ⟨A, φ, hA, hAu, hu, -⟩ := ClassicalInvolution.ModelFacts.UnitaryAut.exists_lift_unitarySU
    h hp2 hq5 (d := 4) (by norm_num) θ hθ hker u
  obtain ⟨B, ψ, hB, hBu, hv, -⟩ := ClassicalInvolution.ModelFacts.UnitaryAut.exists_lift_unitarySU
    h hp2 hq5 (d := 4) (by norm_num) θ hθ hker v
  have hφψ : φ * ψ = ψ * φ := ringAut_mul_comm K φ ψ
  set M₁ := A * glAut φ B with hM₁
  set M₂ := B * glAut ψ A with hM₂
  set C := M₁ * M₂⁻¹ with hC
  have hAU : A ∈ uMat h 4 := (mem_uMat h).2 hAu
  have hBU : B ∈ uMat h 4 := (mem_uMat h).2 hBu
  have hCU : C ∈ uMat h 4 := mul_mem (mul_mem hAU (glAut_mem_uMat h φ hBU))
    (inv_mem (mul_mem hBU (glAut_mem_uMat h ψ hAU)))
  set z := GeneralLinearGroup.det C with hz
  set m := (p ^ f + 1) / 2 with hm
  have hmodd : Odd m := ⟨(p ^ f - 1) / 4, by omega⟩
  have hm2 : p ^ f + 1 = 2 * m := by omega
  set dA := (A : Matrix (Fin 4) (Fin 4) K).det with hdA
  set dB := (B : Matrix (Fin 4) (Fin 4) K).det with hdB
  have hzval : (z : K) = dA * φ dB * (dB * ψ dA)⁻¹ := by
    rw [hz, hC, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hM₁, hM₂, map_mul,
      map_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.val_det_apply,
      GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply,
      GeneralLinearGroup.val_det_apply, det_glAut', det_glAut']
  have hpm : ∀ d : K, d ^ (p ^ f + 1) = 1 → d ^ m = 1 ∨ d ^ m = -1 := by
    intro d hd
    have : (d ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, ← hm2, hd]
    exact mul_self_eq_one_iff.1 (by rw [← sq]; exact this)
  have hfix : ∀ (σ : K ≃+* K) (d : K), d ^ (p ^ f + 1) = 1 → σ (d ^ m) = d ^ m := by
    intro σ d hd
    rcases hpm d hd with h1 | h1 <;> rw [h1] <;> simp
  have hdA1 : dA ^ (p ^ f + 1) = 1 := det_pow_eq_one_of_mem_uMat h hAU
  have hdB1 : dB ^ (p ^ f + 1) = 1 := det_pow_eq_one_of_mem_uMat h hBU
  have hdA0 : dA ≠ 0 := fun h0 => by rw [h0, zero_pow (by omega)] at hdA1; exact zero_ne_one hdA1
  have hdB0 : dB ≠ 0 := fun h0 => by rw [h0, zero_pow (by omega)] at hdB1; exact zero_ne_one hdB1
  have hz1 : z ^ m = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hzval, mul_pow, mul_pow, inv_pow, mul_pow, ← map_pow,
      ← map_pow, hfix φ dB hdB1, hfix ψ dA hdA1, Units.val_one]
    field_simp
  obtain ⟨k, hk⟩ := exists_pow_pow_four_eq_of_pow_odd_eq_one hmodd hz1
  set y := z ^ k with hy
  have hyN' : y ^ (p ^ f + 1) = 1 := by
    rw [hy, ← pow_mul, mul_comm, pow_mul, hm2, pow_mul', hz1, one_pow, one_pow]
  have hyN : (y : K) ^ (p ^ f + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hyN', Units.val_one]
  set s := GeneralLinearGroup.scalar (Fin 4) y with hs
  have hsc : s ∈ Subgroup.center (GL (Fin 4) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨y, rfl⟩
  have hsU : s ∈ uMat h 4 := by
    rw [mem_uMat, hs, GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, UnitaryFieldData.bar_apply, ← pow_succ, hyN]
    · simp [Matrix.scalar_apply, Matrix.one_apply_ne hij, Matrix.mul_apply, Matrix.diagonal_apply,
        hij]
  set S := s⁻¹ * C with hSdef
  have hSdet : GeneralLinearGroup.det S = 1 := by
    rw [hSdef, map_mul, map_inv, ← hz, hk]
    have : GeneralLinearGroup.det s = (z ^ k) ^ 4 := by
      apply Units.ext
      simp [hs, hy]
      ring
    rw [this, inv_mul_cancel]
  have hSU : S ∈ uMat h 4 := mul_mem (inv_mem hsU) hCU
  have hSmem : S ∈ unitarySU p f K 4 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, (mem_uMat h).1 hSU⟩
    have := congrArg Units.val hSdet
    rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this
  set sS : unitarySU p f K 4 := ⟨S, hSmem⟩ with hsS
  have hs' : ∀ W : GL (Fin 4) K, s⁻¹ * W = W * s⁻¹ := fun W =>
    (Subgroup.mem_center_iff.mp (inv_mem hsc) W).symm
  have hSC : ∀ W : GL (Fin 4) K, S * W * S⁻¹ = C * W * C⁻¹ := by
    intro W
    rw [hSdef, _root_.mul_inv_rev, inv_inv]
    calc s⁻¹ * C * W * (C⁻¹ * s) = s⁻¹ * (C * W * C⁻¹) * s := by group
      _ = (C * W * C⁻¹) * s⁻¹ * s := by rw [hs' (C * W * C⁻¹)]
      _ = C * W * C⁻¹ := by group
  have hgl : ∀ g : GL (Fin 4) K, glAut φ (glAut ψ g) = glAut ψ (glAut φ g) := by
    intro g
    have h1 : (glAut φ * glAut ψ : MulAut (GL (Fin 4) K)) = glAut ψ * glAut φ := by
      rw [← map_mul, ← map_mul, hφψ]
    exact congrArg (fun χ : MulAut (GL (Fin 4) K) => χ g) h1
  have hkey : ∀ g : unitarySU p f K 4,
      ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA
          (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom B ψ hB g) =
        sS * ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom B ψ hB
          (ClassicalInvolution.ModelFacts.UnitaryAut.unitaryConjHom A φ hA g) * sS⁻¹ := by
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom,
      ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom,
      ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom,
      ClassicalInvolution.ModelFacts.UnitaryAut.coe_unitaryConjHom, hsS]
    change A * glAut φ (B * glAut ψ (g : GL (Fin 4) K) * B⁻¹) * A⁻¹ =
      S * (B * glAut ψ (A * glAut φ (g : GL (Fin 4) K) * A⁻¹) * B⁻¹) * S⁻¹
    rw [hSC, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hgl, hC, hM₁, hM₂]
    group
  have hcomm : u * v = MulAut.conj (θ sS) * (v * u) := by
    ext x
    obtain ⟨g, rfl⟩ := hθ x
    simp only [MulAut.mul_apply]
    rw [MulAut.conj_apply, ← hv g, ← hu, ← hu g, ← hv, hkey, map_mul, map_mul, map_inv]
  refine ⟨θ sS, ?_⟩
  rw [commutatorElement_def, hcomm]
  group

end UnitaryOut

end CFSG.ComponentClassification.CatFactsL4U4
