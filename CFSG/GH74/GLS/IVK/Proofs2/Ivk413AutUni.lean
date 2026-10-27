module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Aut
public import CFSG.GH74.Generic.S45.LUniLift

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5 Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.GH74.Ivk413

section Abstract

variable {F : Type} [Field F]

theorem conjTr_scalar (σ : F ≃+* F) (c : F) :
    conjTr σ (Matrix.scalar (Fin 4) c) = Matrix.scalar (Fin 4) (σ c) := by
  ext i j
  simp [conjTr, Matrix.scalar_apply, Matrix.diagonal_apply, eq_comm]

theorem conjTr_mul_self_su2 (σ : F ≃+* F) (hσσ : ∀ c, σ (σ c) = c) {x y : F} (hσx : σ x = x)
    (hyN : y * σ y = 1 - x * x) :
    conjTr σ (!![x, y; -σ y, x] : Matrix (Fin 2) (Fin 2) F) * !![x, y; -σ y, x] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, hσσ, hσx] <;>
    first | ring1 | linear_combination hyN

theorem phi_sq_of_fixes (σ φ : F ≃+* F) (hσσ : ∀ c, σ (σ c) = c)
    (hcomm : ∀ c, σ (φ c) = φ (σ c)) (hfix : ∀ t, σ t = t → φ t = t) :
    ∀ x, φ (φ x) = x := by
  intro x
  have hs : σ (x + σ x) = x + σ x := by rw [map_add, hσσ, add_comm]
  have hn : σ (x * σ x) = x * σ x := by rw [map_mul, hσσ, mul_comm]
  have hq : (φ x - x) * (φ x - σ x) = 0 := by
    have h1 : x * x - (x + σ x) * x + x * σ x = 0 := by ring
    have hs'' : φ x + φ (σ x) = x + σ x := by rw [← map_add]; exact hfix _ hs
    have hn'' : φ x * φ (σ x) = x * σ x := by rw [← map_mul]; exact hfix _ hn
    have h2 := congrArg φ h1
    simp only [map_add, map_sub, map_mul, map_zero] at h2
    rw [hs'', hn''] at h2
    linear_combination h2
  rcases mul_eq_zero.1 hq with h | h
  · have h' : φ x = x := sub_eq_zero.1 h
    rw [h', h']
  · have h' : φ x = σ x := sub_eq_zero.1 h
    rw [h', ← hcomm x, h', hσσ]

end Abstract

section Unitary

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [CharP F p] in
theorem unitaryFieldData_of_card' (hF : Nat.card F = (p ^ f) ^ 2) : UnitaryFieldData p f F := by
  refine ⟨Fact.out, ?_, by rw [hF, ← pow_mul, mul_comm]⟩
  by_contra h0
  have : f = 0 := by omega
  subst this
  have h1 := Finite.one_lt_card (α := F)
  rw [hF] at h1
  simp at h1

theorem coe_unitaryInvolution_eq_bar (h : UnitaryFieldData p f F) :
    (⇑(unitaryInvolution F p f) : F → F) = ⇑h.bar :=
  funext fun c => by rw [unitaryInvolution_apply, h.bar_apply]

omit [Finite F] in
theorem two_ne_zero_of_prime_ne_two (hp2 : p ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')

theorem mem_U4_uni_iff (hF : Nat.card F = (p ^ f) ^ 2) {A : GL (Fin 4) F} :
    A ∈ (ModelData.uni hF).U4 ↔
      conjTr (unitaryInvolution F p f) (A : Matrix (Fin 4) (Fin 4) F) *
        (A : Matrix (Fin 4) (Fin 4) F) = 1 :=
  Iff.rfl

theorem semiRep_uni (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    SemiRep (ModelData.uni hF) := by
  intro β _hodd
  have h := unitaryFieldData_of_card' (p := p) (f := f) hF
  have hZN : (Zs (ModelData.uni hF)).Normal := Zs_normal _
  have hker : (mkP (ModelData.uni hF)).ker ≤ Subgroup.center (unitarySU p f F 4) := by
    rw [QuotientGroup.ker_mk']
    exact Zs_le_center (ModelData.uni hF)
  obtain ⟨A, φ, hA, hAu, hlift, -⟩ := CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp2 (d := 4)
    (by norm_num) (mkP (ModelData.uni hF)) (QuotientGroup.mk'_surjective (Zs (ModelData.uni hF)))
    hker β
  refine ⟨A, φ, ?_, fun g => ⟨hA g, (hlift g).symm⟩⟩
  rw [ModelData.uni, mem_uniGL]
  simpa [conjTr, coe_unitaryInvolution_eq_bar h] using hAu

theorem hdet_uni (hF : Nat.card F = (p ^ f) ^ 2) :
    ∀ C ∈ (ModelData.uni hF).U4,
      sc4 (Matrix.GeneralLinearGroup.det C) ∈ (ModelData.uni hF).U4 := by
  intro C hC
  have hd : (unitaryInvolution F p f) ((C : Matrix (Fin 4) (Fin 4) F).det) *
      (C : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    have := congrArg Matrix.det ((mem_U4_uni_iff hF).1 hC)
    rw [Matrix.det_mul, Matrix.det_one, conjTr, Matrix.det_transpose] at this
    have h2 := RingHom.map_det (unitaryInvolution F p f : F →+* F) (C : Matrix (Fin 4) (Fin 4) F)
    rw [RingHom.mapMatrix_apply] at h2
    rw [← this]
    congr 1
  rw [mem_U4_uni_iff]
  rw [sc4, Matrix.GeneralLinearGroup.coe_scalar, conjTr_scalar, ← map_mul]
  simpa using congrArg (Matrix.scalar (Fin 4)) hd

theorem hphiU_uni (hF : Nat.card F = (p ^ f) ^ 2) :
    ∀ (φ : F ≃+* F) (C : GL (Fin 4) F), C ∈ (ModelData.uni hF).U4 →
      glAut φ C ∈ (ModelData.uni hF).U4 := by
  intro φ C hC
  rw [mem_U4_uni_iff] at hC ⊢
  rw [coe_glAut]
  have hcomm : ∀ c : F, unitaryInvolution F p f (φ c) = φ (unitaryInvolution F p f c) := by
    intro c
    rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]
  have e : conjTr (unitaryInvolution F p f) ((C : Matrix (Fin 4) (Fin 4) F).map φ) =
      (conjTr (unitaryInvolution F p f) (C : Matrix (Fin 4) (Fin 4) F)).map φ := by
    ext i j
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, hcomm]
  rw [e]
  have := congrArg (fun N : Matrix (Fin 4) (Fin 4) F => N.map φ) hC
  simp only [Matrix.map_mul, Matrix.map_one, map_zero, map_one] at this
  exact this

theorem exists_H2_trace (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (t : F)
    (ht : unitaryInvolution F p f t = t) :
    ∃ a ∈ (ModelData.uni hF).H2, ((a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = t := by
  have h := unitaryFieldData_of_card' (p := p) (f := f) hF
  have hσσ : ∀ c, unitaryInvolution F p f (unitaryInvolution F p f c) = c :=
    unitaryInvolution_involutive hF
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_prime_ne_two hp2
  set x : F := t / 2 with hx
  have hσx : unitaryInvolution F p f x = x := by rw [hx, map_div₀, ht, map_ofNat]
  have hr : unitaryInvolution F p f (1 - x * x) = 1 - x * x := by
    rw [map_sub, map_one, map_mul, hσx]
  have hrmem : (1 - x * x) ∈ h.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, ← coe_unitaryInvolution_eq_bar h]
    exact hr
  obtain ⟨y, hy⟩ := h.normHom_surjective ⟨1 - x * x, hrmem⟩
  have hyN : y * unitaryInvolution F p f y = 1 - x * x := by
    have := congrArg Subtype.val hy
    rw [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm,
      ← coe_unitaryInvolution_eq_bar h] at this
    exact this
  let g : SpecialLinearGroup (Fin 2) F :=
    ⟨!![x, y; -unitaryInvolution F p f y, x], by
      rw [Matrix.det_fin_two_of]
      linear_combination hyN⟩
  refine ⟨(SpecialLinearGroup.toGL g : GL (Fin 2) F), ?_, ?_⟩
  · rw [(ModelData.uni hF).mem_H2]
    refine ⟨?_, ?_⟩
    · show conjTr (unitaryInvolution F p f)
        ((SpecialLinearGroup.toGL g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((SpecialLinearGroup.toGL g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
      rw [SpecialLinearGroup.coe_GL_coe_matrix]
      exact conjTr_mul_self_su2 (unitaryInvolution F p f) hσσ hσx hyN
    · rw [SpecialLinearGroup.coe_GL_coe_matrix]
      exact g.2
  · rw [SpecialLinearGroup.coe_GL_coe_matrix]
    have e : (g : Matrix (Fin 2) (Fin 2) F).trace = x + x := by
      simp [Matrix.trace, g, Fin.sum_univ_two]
    rw [e, hx]
    field_simp
    ring

theorem hphi_uni (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    ∀ φ : F ≃+* F, (∀ a ∈ (ModelData.uni hF).H2,
      φ ((a : Matrix (Fin 2) (Fin 2) F).trace) = (a : Matrix (Fin 2) (Fin 2) F).trace) →
        ∀ x, φ (φ x) = x := by
  intro φ hφ
  refine phi_sq_of_fixes (unitaryInvolution F p f) φ (unitaryInvolution_involutive hF) ?_ ?_
  · intro c
    rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]
  · intro t ht
    obtain ⟨a, ha, hat⟩ := exists_H2_trace hF hp2 t ht
    have := hφ a ha
    rwa [hat] at this

theorem autInner_uni (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hG : GoodModel (ModelData.uni hF)) : AutInner (ModelData.uni hF) :=
  autInner_of_semiRep hG (semiRep_uni hF hp2) (hdet_uni hF) (hphiU_uni hF) (hphi_uni hF hp2)

end Unitary

end CFSG.GH74.Ivk413
