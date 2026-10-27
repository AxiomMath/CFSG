module

public import CFSG.GH74.Generic.S45.LUniReal
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain

public section

namespace CFSG.GH74.Generic.S45.Uni

open Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

section Dispatch

open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

@[expose] noncomputable def mkSU (c : Matrix (Fin n) (Fin n) K) (hunit : (c.map h.bar)ᵀ * c = 1)
    (hdet : c.det = 1) : unitarySU p f K n :=
  ⟨GeneralLinearGroup.mkOfDetNeZero c (by rw [hdet]; exact one_ne_zero),
    (mem_unitarySU_iff h).2 ⟨by simpa using hdet, by simpa using hunit⟩⟩

theorem coe_mkSU (c : Matrix (Fin n) (Fin n) K) (hunit : (c.map h.bar)ᵀ * c = 1)
    (hdet : c.det = 1) :
    (((mkSU h c hunit hdet : unitarySU p f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c :=
  rfl

theorem comm_of_comp {A : GL (Fin n) K} {φ : K ≃+* K} (hφφ : φ * φ = 1)
    (hA : ∀ g : unitarySU p f K n, A * glAut φ (g : GL (Fin n) K) * A⁻¹ ∈ unitarySU p f K n)
    (hcomp : (unitaryConjHom A φ hA).comp (unitaryConjHom A φ hA) = MonoidHom.id _)
    (g : unitarySU p f K n) :
    (A * glAut φ A) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * (A * glAut φ A) := by
  have h1 := congrArg (fun F : unitarySU p f K n →* unitarySU p f K n => ((F g : unitarySU p f K n) :
    GL (Fin n) K)) hcomp
  simp only [MonoidHom.comp_apply, coe_unitaryConjHom, MonoidHom.id_apply] at h1
  have h2 : glAut φ (glAut φ (g : GL (Fin n) K)) = (g : GL (Fin n) K) := by
    have : (glAut φ * glAut φ : MulAut (GL (Fin n) K)) = 1 := by
      rw [← map_mul, hφφ, map_one]
    exact congrArg (fun F : MulAut (GL (Fin n) K) => F (g : GL (Fin n) K)) this
  rw [map_mul, map_mul, map_inv, h2] at h1
  have h3 : (A * glAut φ A) * (g : GL (Fin n) K) * (A * glAut φ A)⁻¹ = (g : GL (Fin n) K) := by
    calc (A * glAut φ A) * (g : GL (Fin n) K) * (A * glAut φ A)⁻¹ =
        A * (glAut φ A * (g : GL (Fin n) K) * (glAut φ A)⁻¹) * A⁻¹ := by group
      _ = (g : GL (Fin n) K) := h1
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3

@[expose] def FixConcl (n : ℕ) (A : Matrix (Fin n) (Fin n) K)
    (ψ : Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ c : Matrix (Fin n) (Fin n) K, (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧
    (∀ l : K, c * c ≠ l • 1) ∧ (c * c * (c * c) = 1 ∨ (Even n ∧ c * c * (c * c) = -1)) ∧
      A * ψ c = c * A

include h in
theorem scalar_of_comp (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {A : GL (Fin n) K} {φ : K ≃+* K}
    (hφφ : φ * φ = 1)
    (hA : ∀ g : unitarySU p f K n, A * glAut φ (g : GL (Fin n) K) * A⁻¹ ∈ unitarySU p f K n)
    (hcomp : (unitaryConjHom A φ hA).comp (unitaryConjHom A φ hA) = MonoidHom.id _) :
    ∃ μ : K, (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K).map φ = μ • 1 := by
  refine eq_smul_one_of_comm_rot h h2 hn fun i j hij => ?_
  have hx : ∀ i : Fin n, stdHermForm h n (Pi.single i 1) (Pi.single i 1) = 1 := by
    intro i
    rw [stdHermForm_single]
    simp
  have hxy : stdHermForm h n (Pi.single i 1) (Pi.single j 1) = 0 := by
    rw [stdHermForm_single]
    simp [hij]
  let g := mkSU h (pairRot h (Pi.single i 1) (Pi.single j 1))
    (unitary_of_isometry h (pairRot_isometry h (hx i) (hx j) hxy))
    (pairRot_det h (hx i) (hx j) hxy)
  have := comm_of_comp hφφ hA hcomp g
  have h2' := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) this
  simp only [Units.val_mul, coe_glAut] at h2'
  exact h2'

theorem ustar_ustar (A : Matrix (Fin n) (Fin n) K) :
    (((A.map h.bar)ᵀ).map h.bar)ᵀ = A := by
  ext i j
  simp [h.bar_bar]

theorem ustar_smul (c : K) (A : Matrix (Fin n) (Fin n) K) :
    ((c • A).map h.bar)ᵀ = h.bar c • (A.map h.bar)ᵀ := by
  ext i j
  simp

theorem isSquare_of_norm_one (hp : p ≠ 2) {μ : K} (hμ : h.bar μ * μ = 1) : IsSquare μ := by
  classical
  have : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ
  have hodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp).pow
  have hchar : ringChar K ≠ 2 := by
    have : CharP K p := h.charP
    rw [ringChar.eq K p]
    exact hp
  rw [FiniteField.isSquare_iff hchar hμ0]
  obtain ⟨m, hm⟩ := hodd
  have hcard : Fintype.card K = (2 * m + 1) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h.card_eq_sq, hm]
  have hhalf : Fintype.card K / 2 = (p ^ f + 1) * m := by
    rw [hcard, hm]
    have : (2 * m + 1) ^ 2 = 2 * ((2 * m + 1 + 1) * m) + 1 := by ring
    omega
  rw [hhalf, pow_mul, ← h.norm_eq_pow, UnitaryFieldData.norm, mul_comm, hμ, one_pow]

theorem fixed_class1 (hp : p ≠ 2) (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    (h1b : ∀ (A : Matrix (Fin n) (Fin n) K) (l : K), (A.map h.bar)ᵀ * A = 1 →
      A * A = (l * l) • 1 → h.bar l * l = -1 → FixConcl h n A id)
    {A : Matrix (Fin n) (Fin n) K} (hAu : (A.map h.bar)ᵀ * A = 1) {μ : K}
    (hμ : A * A = μ • 1) : FixConcl h n A id := by
  have hA' : A = μ • (A.map h.bar)ᵀ := by
    calc A = ((A.map h.bar)ᵀ * A) * A := by rw [hAu, Matrix.one_mul]
      _ = (A.map h.bar)ᵀ * (A * A) := by rw [Matrix.mul_assoc]
      _ = μ • (A.map h.bar)ᵀ := by rw [hμ, Matrix.mul_smul, Matrix.mul_one]
  have hA0 : A ≠ 0 := by
    rintro rfl
    have : (1 : Matrix (Fin n) (Fin n) K) = 0 := by
      rw [← hAu]; simp
    have h00 := congrFun (congrFun this ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at h00
  have hA'' : (A.map h.bar)ᵀ = h.bar μ • A := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) K => (M.map h.bar)ᵀ) hA'
    simp only [ustar_smul, ustar_ustar] at this
    exact this
  have hμN : h.bar μ * μ = 1 := by
    have e : μ • (h.bar μ • A) = A := by rw [← hA'', ← hA']
    have h3 : (1 - μ * h.bar μ) • A = 0 := by
      rw [sub_smul, one_smul, ← smul_smul, e, sub_self]
    have := (smul_eq_zero.1 h3).resolve_right hA0
    linear_combination -this
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμN
  obtain ⟨l, hl⟩ := isSquare_of_norm_one h hp hμN
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hμ0 (by rw [hl]; ring)
  have hNl : (h.bar l * l) * (h.bar l * l) = 1 := by
    have : h.bar μ * μ = (h.bar l * l) * (h.bar l * l) := by
      rw [hl, map_mul]; ring
    rw [← this, hμN]
  rcases mul_self_eq_one_iff.1 hNl with hN1 | hN1
  ·
    set T : Matrix (Fin n) (Fin n) K := l⁻¹ • A with hT
    have hTa : ∀ z w, stdHermForm h n (T *ᵥ z) w = stdHermForm h n z (T *ᵥ w) := by
      intro z w
      rw [hT, smul_mulVec, smul_mulVec, map_smulₛₗ, LinearMap.smul_apply, map_smul,
        hh_mulVec_left, hA'', smul_mulVec, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      have hbl : h.bar l = l⁻¹ := eq_inv_of_mul_eq_one_left hN1
      rw [map_inv₀, hbl, hl, map_mul, hbl, inv_inv]
      field_simp
    have hT2 : T * T = 1 := by
      rw [hT, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hμ, smul_smul, hl]
      have : l⁻¹ * l⁻¹ * (l * l) = 1 := by field_simp
      rw [this, one_smul]
    obtain ⟨x, y, ε, hε, hx, hy, hxx, hyy, hxy⟩ := exists_eigenpair h h2 hn hTa hT2
    obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ := exists_rot_commuting h h2 hn hxx hyy hxy hε hTa hx hy
    refine ⟨c, hc1, hc2, hc3, Or.inl hc4, ?_⟩
    have hAT : A = l • T := by rw [hT, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    show A * c = c * A
    rw [hAT, Matrix.smul_mul, Matrix.mul_smul, hc5]
  · exact h1b A l hAu (by rw [hμ, hl]) hN1

theorem class2_transpose {A : Matrix (Fin n) (Fin n) K} (hAu : (A.map h.bar)ᵀ * A = 1) {μ : K}
    (hμ : A * A.map h.bar = μ • 1) : A = μ • Aᵀ ∧ Aᵀ = μ • A := by
  have h1 : Aᵀ * A.map h.bar = 1 := by
    have := congrArg Matrix.transpose hAu
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  have h2' : A.map h.bar * Aᵀ = 1 := mul_eq_one_comm.1 h1
  have hAt : A = μ • Aᵀ := by
    calc A = A * (A.map h.bar * Aᵀ) := by rw [h2', Matrix.mul_one]
      _ = (A * A.map h.bar) * Aᵀ := by rw [Matrix.mul_assoc]
      _ = μ • Aᵀ := by rw [hμ, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨hAt, ?_⟩
  have := congrArg Matrix.transpose hAt
  rw [transpose_smul, transpose_transpose] at this
  exact this

theorem ne_zero_of_unitary (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) K}
    (hAu : (A.map h.bar)ᵀ * A = 1) : A ≠ 0 := by
  rintro rfl
  have : (1 : Matrix (Fin n) (Fin n) K) = 0 := by
    rw [← hAu]; simp
  have h00 := congrFun (congrFun this ⟨0, by omega⟩) ⟨0, by omega⟩
  simp at h00

theorem fixed_class2 (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    (h2a : ∀ A : Matrix (Fin n) (Fin n) K, (A.map h.bar)ᵀ * A = 1 →
      A * A.map h.bar = (-1 : K) • 1 → FixConcl h n A (fun M => M.map h.bar))
    {A : Matrix (Fin n) (Fin n) K} (hAu : (A.map h.bar)ᵀ * A = 1) {μ : K}
    (hμ : A * A.map h.bar = μ • 1) : FixConcl h n A (fun M => M.map h.bar) := by
  obtain ⟨hAt, hAt'⟩ := class2_transpose h hAu hμ
  have hA0 := ne_zero_of_unitary h (by omega) hAu
  have hμμ : μ * μ = 1 := by
    have h3 : (μ * μ - 1) • A = 0 := by
      rw [sub_smul, one_smul, ← smul_smul, ← hAt', ← hAt, sub_self]
    have := (smul_eq_zero.1 h3).resolve_right hA0
    linear_combination this
  rcases mul_self_eq_one_iff.1 hμμ with hμ1 | hμ1
  · rw [hμ1] at hμ
    obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ := exists_class2_symm h h2 hn hAu hμ
    exact ⟨c, hc1, hc2, hc3, Or.inl hc4, hc5⟩
  · rw [hμ1] at hμ
    exact h2a A hAu hμ

include h in
theorem two_ne_zero_of_ne (hp : p ≠ 2) : (2 : K) ≠ 0 := by
  have : CharP K p := h.charP
  intro h0
  have h1 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
  have h2' := (CharP.cast_eq_zero_iff K p 2).1 h1
  exact hp ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 h2')

theorem det_unitary_norm {A : Matrix (Fin n) (Fin n) K} (hAu : (A.map h.bar)ᵀ * A = 1) :
    h.bar A.det * A.det = 1 := by
  have := congrArg Matrix.det hAu
  rw [det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_one] at this
  exact this

theorem class1b_odd (hodd : Odd n) (h2 : (2 : K) ≠ 0) :
    ∀ (A : Matrix (Fin n) (Fin n) K) (l : K), (A.map h.bar)ᵀ * A = 1 →
      A * A = (l * l) • 1 → h.bar l * l = -1 → FixConcl h n A id := by
  intro A l hAu hAA hNl
  exfalso
  have hd1 := det_unitary_norm h hAu
  have hd2 : A.det * A.det = l ^ n * l ^ n := by
    have := congrArg Matrix.det hAA
    rw [det_mul, det_smul, det_one, Fintype.card_fin] at this
    rw [this]
    ring
  have hN : h.bar (l ^ n) * l ^ n = -1 := by
    rw [map_pow, ← mul_pow, hNl, hodd.neg_one_pow]
  have hd : A.det = l ^ n ∨ A.det = -l ^ n := by
    have : (A.det - l ^ n) * (A.det + l ^ n) = 0 := by linear_combination hd2
    rcases mul_eq_zero.1 this with h3 | h3
    · exact Or.inl (sub_eq_zero.1 h3)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h3)
  rcases hd with hd | hd
  · rw [hd, hN] at hd1
    exact h2 (by linear_combination -hd1)
  · rw [hd, map_neg, neg_mul_neg, hN] at hd1
    exact h2 (by linear_combination -hd1)

theorem class2alt_odd (hodd : Odd n) (h2 : (2 : K) ≠ 0) :
    ∀ A : Matrix (Fin n) (Fin n) K, (A.map h.bar)ᵀ * A = 1 → A * A.map h.bar = (-1 : K) • 1 →
      FixConcl h n A (fun M => M.map h.bar) := by
  intro A hAu hAA
  exfalso
  obtain ⟨-, hAt'⟩ := class2_transpose h hAu hAA
  have hd1 := det_unitary_norm h hAu
  have h3 : A.det = -A.det := by
    have := congrArg Matrix.det hAt'
    rw [det_transpose, det_smul, Fintype.card_fin, hodd.neg_pow, one_pow] at this
    linear_combination this
  have h4 : A.det = 0 := by
    have : (2 : K) * A.det = 0 := by linear_combination h3
    exact (mul_eq_zero.1 this).resolve_left h2
  rw [h4, map_zero, zero_mul] at hd1
  exact zero_ne_one hd1

theorem scalar_mem_unitaryScalars (u : K) (hu0 : u ≠ 0) (hN : h.norm u = 1)
    (hu : u ^ n = 1) (g : unitarySU p f K n)
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = u • 1) :
    g ∈ unitaryScalars h n := by
  rw [mem_unitaryScalars]
  refine ⟨Units.mk0 u hu0, by simpa using hN, ?_, ?_⟩
  · apply Units.ext
    simp [hu]
  · apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, hg, Units.val_mk0, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]

theorem exists_fixed_unitary (hp : p ≠ 2) (hn : 3 ≤ n)
    (h1b : ∀ (A : Matrix (Fin n) (Fin n) K) (l : K), (A.map h.bar)ᵀ * A = 1 →
      A * A = (l * l) • 1 → h.bar l * l = -1 → FixConcl h n A id)
    (h2a : ∀ A : Matrix (Fin n) (Fin n) K, (A.map h.bar)ᵀ * A = 1 →
      A * A.map h.bar = (-1 : K) • 1 → FixConcl h n A (fun M => M.map h.bar))
    {A : GL (Fin n) K} {φ : K ≃+* K}
    (hA : ∀ g : unitarySU p f K n, A * glAut φ (g : GL (Fin n) K) * A⁻¹ ∈ unitarySU p f K n)
    (hAu : ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1)
    (hφ : φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c)
    (hcomp : (unitaryConjHom A φ hA).comp (unitaryConjHom A φ hA) = MonoidHom.id _) :
    ∃ c : unitarySU p f K n, unitaryConjHom A φ hA c = c ∧ c ^ 2 ∉ unitaryScalars h n ∧
      c ^ 4 ∈ unitaryScalars h n := by
  have h2 := two_ne_zero_of_ne h hp
  have hφφ : φ * φ = 1 := by
    rcases hφ with rfl | hb
    · ext c
      rfl
    · ext c
      change φ (φ c) = c
      rw [hb, hb, h.bar_bar]
  obtain ⟨μ, hμ⟩ := scalar_of_comp h h2 hn hφφ hA hcomp
  obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ : ∃ c : Matrix (Fin n) (Fin n) K,
      (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧ (∀ l : K, c * c ≠ l • 1) ∧
        (c * c * (c * c) = 1 ∨ (Even n ∧ c * c * (c * c) = -1)) ∧
        (A : Matrix (Fin n) (Fin n) K) * c.map φ = c * (A : Matrix (Fin n) (Fin n) K) := by
    rcases hφ with rfl | hb
    · have hmap : (A : Matrix (Fin n) (Fin n) K).map (RingEquiv.refl K) =
          (A : Matrix (Fin n) (Fin n) K) := by
        ext i j
        rfl
      rw [hmap] at hμ
      obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ := fixed_class1 h hp h2 hn h1b hAu hμ
      refine ⟨c, hc1, hc2, hc3, hc4, ?_⟩
      have hmapc : c.map (RingEquiv.refl K) = c := by
        ext i j
        rfl
      rw [hmapc]
      exact hc5
    · have hmap : (A : Matrix (Fin n) (Fin n) K).map φ = (A : Matrix (Fin n) (Fin n) K).map h.bar := by
        ext i j
        exact hb _
      rw [hmap] at hμ
      obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ := fixed_class2 h h2 hn h2a hAu hμ
      refine ⟨c, hc1, hc2, hc3, hc4, ?_⟩
      have hmapc : c.map φ = c.map h.bar := by
        ext i j
        exact hb _
      rw [hmapc]
      exact hc5
  have hcoe : (((mkSU h c hc1 hc2 : unitarySU p f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c :=
    coe_mkSU h c hc1 hc2
  refine ⟨mkSU h c hc1 hc2, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [coe_unitaryConjHom, mul_inv_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glAut, hcoe]
    exact hc5
  · intro hmem
    rw [mem_unitaryScalars] at hmem
    obtain ⟨u, -, -, hu⟩ := hmem
    apply hc3 (u : K)
    have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hu
    simp only [pow_two, Subgroup.coe_mul, Units.val_mul, hcoe, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at this
    rw [this, Matrix.smul_one_eq_diagonal]
  · rcases hc4 with hc4 | ⟨hev, hc4⟩
    · have : (mkSU h c hc1 hc2 : unitarySU p f K n) ^ 4 = 1 := by
        apply Subtype.ext
        apply Units.ext
        simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe, OneMemClass.coe_one,
          Units.val_one]
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hc4]
      rw [this]
      exact one_mem _
    · refine scalar_mem_unitaryScalars h (-1) (by simp) (by simp [UnitaryFieldData.norm])
        hev.neg_one_pow _ ?_
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe]
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hc4, neg_smul, one_smul]

end Dispatch
end CFSG.GH74.Generic.S45.Uni
