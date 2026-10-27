module

public import CFSG.GH74.Generic.BProg.B3.S3OuterCore
public import CFSG.GH74.Generic.BProg.B3.S3OuterUniAlg
public import CFSG.GH74.Generic.BProg.B3.S3OuterRank
public import CFSG.GH74.Generic.BProg.B2.PumpupTableOutU3
public import CFSG.GH74.Generic.BProg.B3.L2CompU3Fix

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3OuterUni

open CFSG CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.GH74.KGroups.L3Eps CFSG.GH74.KGroups.L3Eps.Uni
  Matrix Subgroup S3OuterCore
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {F : Type} [Field F]

theorem exists_trace_sq_add_sq (h : UnitaryFieldData p f F) (hp : p ≠ 2) :
    ∃ x y : F, h.bar x = -x ∧ h.bar y = -y ∧ x ^ 2 + y ^ 2 = -1 := by
  classical
  have : Finite F := h.finite
  obtain ⟨u, hu⟩ := h.exists_bar_ne
  set θ₀ : F := u - h.bar u with hθ₀
  have hθ₀bar : h.bar θ₀ = -θ₀ := by
    rw [hθ₀, map_sub, h.bar_bar]
    ring
  have hθ₀ne : θ₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hu)
  have hfix : θ₀ ^ 2 ∈ h.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, map_pow, hθ₀bar]
    ring
  set z : h.fixedField := ⟨-(θ₀ ^ 2)⁻¹, by
    have := h.fixedField.inv_mem hfix
    exact h.fixedField.neg_mem this⟩ with hz
  have : Fintype h.fixedField := Fintype.ofFinite _
  have hodd : Fintype.card h.fixedField % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, h.card_fixedField]
    exact Nat.odd_iff.1 ((h.prime.odd_of_ne_two hp).pow)
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X ^ 2 : Polynomial h.fixedField))
    (g := (Polynomial.X ^ 2 - Polynomial.C z : Polynomial h.fixedField))
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by decide) z) hodd
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at hab
  have hab' : (a : F) ^ 2 + (b : F) ^ 2 = -(θ₀ ^ 2)⁻¹ := by
    have := congrArg Subtype.val (show a ^ 2 + (b ^ 2 - z) = 0 from hab)
    simp only [Subfield.coe_add, Subfield.coe_sub, SubmonoidClass.coe_pow, hz,
      Subfield.coe_zero] at this
    linear_combination this
  have ha : h.bar (a : F) = a := (UnitaryFieldData.mem_fixedField h).1 a.2
  have hb : h.bar (b : F) = b := (UnitaryFieldData.mem_fixedField h).1 b.2
  refine ⟨θ₀ * a, θ₀ * b, ?_, ?_, ?_⟩
  · rw [map_mul, hθ₀bar, ha]
    ring
  · rw [map_mul, hθ₀bar, hb]
    ring
  · calc (θ₀ * a) ^ 2 + (θ₀ * b) ^ 2 = θ₀ ^ 2 * ((a : F) ^ 2 + (b : F) ^ 2) := by ring
      _ = -1 := by rw [hab']; field_simp

theorem exists_twist (h : UnitaryFieldData p f F) (hp : p ≠ 2) {φ : F ≃+* F}
    (hφ : ∀ c, φ c = h.bar c) {A : GL (Fin 3) F}
    {hA : ∀ g : ↥(unitarySU p f F 3), A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∈ unitarySU p f F 3}
    {c : ↥(unitarySU p f F 3)} (hc : unitaryConjHom A φ hA c = c) (hc4 : c ^ 4 = 1) :
    ∃ k : ↥(unitarySU p f F 3), unitaryConjHom A φ hA k = c ^ 2 * k := by
  classical
  have : Finite F := h.finite
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have hc0 := h.charP
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 (by exact_mod_cast h0)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
    · exact h.prime.one_lt.ne' h1
    · exact hp h1
  have hφb : (⇑φ : F → F) = ⇑h.bar := funext hφ
  set Am : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hAm
  set Ai : Matrix (Fin 3) (Fin 3) F := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hAi
  have h1 : Am * Ai = 1 := by rw [hAm, hAi]; exact A.mul_inv
  have h2' : Ai * Am = 1 := by rw [hAm, hAi]; exact A.inv_mul
  set Cm : Matrix (Fin 3) (Fin 3) F := (((c : ↥(unitarySU p f F 3)) : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) with hCm
  obtain ⟨hCdet, hCu⟩ := (mem_unitarySU_iff h).1 c.2
  have hAC : Am * Cm.map φ * Ai = Cm := by
    have := congrArg
      (fun g : ↥(unitarySU p f F 3) => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hc
    simpa [coe_unitaryConjHom, coe_glAut, hAm, hAi, hCm] using this
  have hCu' : (Cm.map φ)ᵀ * Cm = 1 := by rw [hφb]; exact hCu
  have hc4' : Cm * Cm * (Cm * Cm) = 1 := by
    have := congrArg
      (fun g : ↥(unitarySU p f F 3) => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hc4
    have h4 : Cm ^ 4 = 1 := by simpa [hCm] using this
    rw [show Cm * Cm * (Cm * Cm) = Cm ^ 4 by noncomm_ring]
    exact h4
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_trace_sq_add_sq h hp
  obtain ⟨K, hK1, hK2⟩ := S3OuterUniAlg.mu_alg h2 φ Am Ai Cm h1 h2' hAC hCu' hc4' x y
    (by rw [hφ]; exact hx) (by rw [hφ]; exact hy) hxy
  have hAdet : Am.det * Ai.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
  have hdetmap : (K.map φ).det = φ K.det := (RingHom.map_det (φ : F →+* F) K).symm
  have hδφ : φ K.det = K.det := by
    have h3 := congrArg Matrix.det hK1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hCdet, hdetmap] at h3
    have h4 : Am.det * φ K.det * Ai.det = φ K.det := by
      calc Am.det * φ K.det * Ai.det = (Am.det * Ai.det) * φ K.det := by ring
        _ = φ K.det := by rw [hAdet, one_mul]
    rw [h4] at h3
    simpa using h3
  have hδδ : K.det * K.det = 1 := by
    have h3 := congrArg Matrix.det hK2
    rw [Matrix.det_mul, Matrix.det_transpose, hdetmap, hδφ, Matrix.det_one] at h3
    exact h3
  set δ : F := K.det with hδ
  set K' : Matrix (Fin 3) (Fin 3) F := δ • K with hK'
  have hdet' : K'.det = 1 := by
    rw [hK', Matrix.det_smul, Fintype.card_fin, ← hδ]
    calc δ ^ 3 * δ = (δ * δ) * (δ * δ) := by ring
      _ = 1 := by rw [hδδ, one_mul]
  have hunit' : (K'.map φ)ᵀ * K' = 1 := by
    rw [hK', Matrix.map_smul' _ _ _ φ.map_mul, hδφ, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, hK2, smul_smul, hδδ, one_smul]
  have hΨ' : Am * K'.map φ * Ai = (Cm * Cm) * K' := by
    rw [hK', Matrix.map_smul' _ _ _ φ.map_mul, hδφ, Matrix.mul_smul, Matrix.smul_mul, hK1,
      Matrix.mul_smul]
  have hdet0 : K'.det ≠ 0 := by rw [hdet']; exact one_ne_zero
  set Kg : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero K' hdet0 with hKg
  have hKgv : (Kg : Matrix (Fin 3) (Fin 3) F) = K' := rfl
  have hKgmem : Kg ∈ unitarySU p f F 3 := by
    rw [mem_unitarySU_iff h, hKgv]
    refine ⟨hdet', ?_⟩
    rw [← hφb]
    exact hunit'
  refine ⟨⟨Kg, hKgmem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change Am * (Kg : Matrix (Fin 3) (Fin 3) F).map φ * Ai = _
  rw [hKgv, hΨ']
  simp [pow_two, hCm, hKgv]

theorem outerCore_unitary (h : UnitaryFieldData p f F) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) {K : Type}
    [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ) {σ : MulAut K} (hσ : σ * σ = 1)
    (hout : σ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) : OuterCore σ := by
  classical
  have hq : Odd (p ^ f) := (h.prime.odd_of_ne_two hp).pow
  have : Finite F := h.finite
  have : Finite K := Finite.of_surjective θ hθ.surj
  obtain ⟨N, hGD, ⟨eN⟩⟩ := B2.PumpupTableOutU3.graphData_of_cover_psl2 h hp h5 hq hθ hσ hout
  have hfc : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hk2 : Nat.card h.fixedField ≠ 2 := by omega
  have hk3 : Nat.card h.fixedField ≠ 3 := by omega
  rcases involution_type h hp h5 hθ hσ with ⟨A, hAu, hAA, hrel⟩ | ⟨φ, A, hφ, hAu, hAA, hrel⟩
  · exfalso
    obtain ⟨y, hy⟩ := exists_conj_of_typeI h hθ hAu hAA hrel
    exact hout ⟨y, hy⟩
  · have hA : ∀ g : ↥(unitarySU p f F 3),
        A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∈ unitarySU p f F 3 := by
      intro g
      obtain ⟨g', hg'1, -⟩ := hrel g
      rw [← hg'1]
      exact g'.2
    have hτθ : ∀ g, θ (unitaryConjHom A φ hA g) = σ (θ g) := by
      intro g
      obtain ⟨g', hg'1, hg'2⟩ := hrel g
      have : g' = unitaryConjHom A φ hA g := Subtype.ext hg'1
      rw [← this]
      exact hg'2
    have hφφ : ∀ c, φ (φ c) = c := fun c => by rw [hφ, hφ, h.bar_bar]
    have hglφ : ∀ g : GL (Fin 3) F, glAut φ (glAut φ g) = g := by
      intro g
      apply Units.ext
      rw [coe_glAut, coe_glAut]
      ext i j
      simp [Matrix.map_apply, hφφ]
    have hAB : A * glAut φ A = 1 := by
      apply Units.ext
      rw [Units.val_mul, coe_glAut, Units.val_one]
      have : (A : Matrix (Fin 3) (Fin 3) F).map φ = (A : Matrix (Fin 3) (Fin 3) F).map h.bar := by
        ext i j
        exact hφ _
      rw [this]
      exact hAA
    have hcomp : (unitaryConjHom A φ hA).comp (unitaryConjHom A φ hA) = MonoidHom.id _ := by
      refine MonoidHom.ext fun g => ?_
      apply Subtype.ext
      change A * glAut φ (A * glAut φ (g : GL (Fin 3) F) * A⁻¹) * A⁻¹ = g
      rw [map_mul, map_mul, hglφ, map_inv, eq_inv_of_mul_eq_one_right hAB]
      group
    obtain ⟨c, d, hc, hd, hc2, hc4, hd2, hdc⟩ :=
      L2CompU3Fix.exists_fixed_unitary_D8 h hp hA hAu (Or.inr hφ) hcomp
    obtain ⟨k, hk⟩ := exists_twist h hp hφ hc hc4
    have ha : σ (θ c) = θ c := by rw [← hτθ, hc]
    have hb : σ (θ d) = θ d := by rw [← hτθ, hd]
    have ha4 : θ c ^ 4 = 1 := by rw [← map_pow, hc4, map_one]
    have hb2 : θ d * θ d = 1 := by rw [← map_mul, hd2, map_one]
    have hbab : θ d * θ c * θ d = θ c ^ 3 := by rw [← map_mul, ← map_mul, hdc, map_pow]
    have hcomm : ⁅θ d, θ c⁆ = θ c ^ 2 := by
      have hbi : (θ d)⁻¹ = θ d := inv_eq_of_mul_eq_one_right hb2
      rw [commutatorElement_def, hbi, hbab]
      group
    have ht : θ c ^ 2 ∈ N := hcomm ▸ hGD.commutator_mem _ _ hb ha
    have ht2 : θ c ^ 2 * θ c ^ 2 = 1 := by
      calc θ c ^ 2 * θ c ^ 2 = θ c ^ 4 := by group
        _ = 1 := ha4
    have ht1 : θ c ^ 2 ≠ 1 := by
      intro h1
      apply hc2
      rw [← hθ.ker]
      change θ (c ^ 2) = 1
      rw [map_pow]
      exact h1
    have hfin : Finite ↥N := inferInstance
    refine ⟨N, hGD.quasisimple, S3OuterRank.two_le_pRank_of_psl2 hGD.quasisimple hk2 hk3 eN,
      hGD.fixed, hGD.conj_mem, θ c ^ 2, ht, ht2, ht1, θ k, ?_⟩
    rw [← hτθ, hk, map_mul, map_pow, mul_inv_cancel_right]

end S3OuterUni

end CFSG.GH74.Generic.BProg.B3
