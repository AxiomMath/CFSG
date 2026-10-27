module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNU43MatFin
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN.U43

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Multipliers.U43 (F9)

theorem hud : UnitaryFieldData 3 1 F9 :=
  ⟨Nat.prime_three, le_rfl, by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num⟩

abbrev P43 : Type := primeFormP hud ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)

namespace Mat

open CFSG.GH74.GLS.C3.Layer1.EndN.U43.Mat

theorem hud_bar (x : F9) : hud.bar x = barF x := by
  rw [UnitaryFieldData.bar_apply]
  revert x
  decide

theorem isPrimeFormGram_one4 : IsPrimeFormGram (1 : GL (Fin 4) F9) := by
  refine ⟨by rw [Units.val_one, transpose_one], fun i j => ?_⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

abbrev SU4 : Type :=
  ↥(gramSU hud ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9))

@[expose] def suOf (M : Matrix (Fin 4) (Fin 4) F9) (h1 : (M.map barF)ᵀ * M = 1)
    (h2 : M.det = 1) : SU4 :=
  ⟨⟨M, (M.map barF)ᵀ, mul_eq_one_comm.mpr h1, h1⟩, by
    refine ⟨?_, h2⟩
    have : M.map hud.bar = M.map barF := Matrix.ext fun i j => hud_bar (M i j)
    show (M.map hud.bar)ᵀ * ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) * M =
      ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)
    rw [this, Units.val_one, Matrix.mul_one]
    exact h1⟩

@[expose] def zS : SU4 := suOf zM zM_unitary zM_det

end Mat

open CFSG.GH74.GLS.C3.Layer1.EndN.U43.Mat

@[expose] def z5 : P43 := QuotientGroup.mk zS

namespace Mat

theorem coe_scalar_smul (c : F9ˣ) :
    ((GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      (c : F9) • 1 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem mk_eq_one_iff (g : SU4) : (QuotientGroup.mk g : P43) = 1 ↔
    ∃ c : F9, c ^ 4 = 1 ∧ ((g : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = c • 1 := by
  rw [QuotientGroup.eq_one_iff, mem_normOneScalars]
  constructor
  · rintro ⟨c, hc1, hc4, hg⟩
    refine ⟨c, ?_, ?_⟩
    · rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]
    · rw [hg, coe_scalar_smul]
  · rintro ⟨c, hc4, hg⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc4
    refine ⟨Units.mk0 c hc0, ?_, ?_, ?_⟩
    · rw [hud.norm_eq_pow]
      simpa using hc4
    · refine Units.ext ?_
      simpa using hc4
    · refine Units.ext ?_
      rw [hg, coe_scalar_smul]
      rfl

end Mat

theorem orderOf_z5 : orderOf z5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [z5, ← QuotientGroup.mk_pow, mk_eq_one_iff]
    refine ⟨1, one_pow _, ?_⟩
    rw [one_smul, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact zM_pow_five
  · rw [z5, Ne, mk_eq_one_iff]
    rintro ⟨c, -, hc⟩
    exact zM_not_scalar c hc

namespace Mat

theorem aut_form (α : MulAut P43) :
    ∃ (A : primeFormUnitary hud ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9))
      (φ : F9 ≃+* F9), α = primeFormConjHom hud _ A *
        primeFormFieldHom hud isPrimeFormGram_one4 φ := by
  obtain ⟨φ, ⟨A, hA⟩, -⟩ :=
    (unitary_prime_form_full_semilinear_realization hud isPrimeFormGram_one4 (by norm_num)
      (by decide)).2.2.2.2.1 α
  exact ⟨A, φ, hA⟩

@[expose] def conjField
    (A : primeFormUnitary hud ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9))
    (φ : F9 ≃+* F9) (g : SU4) : SU4 :=
  ⟨(A : GL (Fin 4) F9) * glAut φ (g : GL (Fin 4) F9) * (A : GL (Fin 4) F9)⁻¹,
    conj_mem_gramSU hud _ A.2 (glAut_mem_gramSU hud isPrimeFormGram_one4 φ g.2)⟩

theorem act_mk (A : primeFormUnitary hud ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9))
    (φ : F9 ≃+* F9) (g : SU4) :
    (primeFormConjHom hud _ A * primeFormFieldHom hud isPrimeFormGram_one4 φ)
      (QuotientGroup.mk g : P43) = QuotientGroup.mk (conjField A φ g) := by
  rw [MulAut.mul_apply]
  change primeFormConjAut hud _ A (primeFormFieldAut hud isPrimeFormGram_one4 φ
    (QuotientGroup.mk g : P43)) = _
  rw [primeFormFieldAut_mk, primeFormConjAut_mk]
  rfl

theorem eq_one_of_pow_five {G : Type*} [Group G] {y s : G} (hc : Commute y s) (hy : y ^ 5 = 1)
    (hys : (y * s) ^ 5 = 1) (hs : s ^ 4 = 1) : s = 1 := by
  have h1 : (y * s) ^ 5 = y ^ 5 * s ^ 5 := hc.mul_pow 5
  rw [hys, hy, one_mul] at h1
  have h2 : s ^ 5 = s := by rw [pow_succ, hs, one_mul]
  rw [h2] at h1
  exact h1.symm

theorem E1_of_fix (A : primeFormUnitary hud ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9))
    (φ : F9 ≃+* F9)
    (hz : (primeFormConjHom hud _ A * primeFormFieldHom hud isPrimeFormGram_one4 φ) z5 = z5) :
    ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) * zM.map φ =
      zM * ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) := by
  rw [z5, act_mk] at hz
  obtain ⟨c, -, hc4, hc⟩ := mem_normOneScalars.mp (QuotientGroup.eq.mp hz)
  set zU : GL (Fin 4) F9 := (zS : GL (Fin 4) F9) with hzU
  set y : GL (Fin 4) F9 := (A : GL (Fin 4) F9) * glAut φ zU * (A : GL (Fin 4) F9)⁻¹ with hy
  have hc' : y⁻¹ * zU = GeneralLinearGroup.scalar (Fin 4) c := by
    simpa [conjField, hy, hzU] using hc
  have hzy : zU = y * GeneralLinearGroup.scalar (Fin 4) c := inv_mul_eq_iff_eq_mul.mp hc'
  have hzU5 : zU ^ 5 = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact zM_pow_five
  have hy5 : y ^ 5 = 1 := by
    rw [hy, conj_pow, ← map_pow, hzU5, map_one, mul_one, mul_inv_cancel]
  have hs4 : (GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F9) ^ 4 = 1 := by
    rw [← map_pow, hc4, map_one]
  have hs1 : GeneralLinearGroup.scalar (Fin 4) c = (1 : GL (Fin 4) F9) := by
    refine eq_one_of_pow_five (commute_scalar c y) hy5 ?_ hs4
    rw [← hzy]
    exact hzU5
  rw [hs1, mul_one] at hzy
  have h2 : zU * (A : GL (Fin 4) F9) = (A : GL (Fin 4) F9) * glAut φ zU := by
    have h4 : y * (A : GL (Fin 4) F9) = (A : GL (Fin 4) F9) * glAut φ zU := by
      rw [hy]
      group
    exact (congrArg (· * (A : GL (Fin 4) F9)) hzy).trans h4
  have h3 := congrArg (fun g : GL (Fin 4) F9 => (g : Matrix (Fin 4) (Fin 4) F9)) h2
  simp only [Units.val_mul, coe_glAut] at h3
  exact h3.symm

theorem E3_of_sq (A : primeFormUnitary hud ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9))
    (φ : F9 ≃+* F9)
    (hα : (primeFormConjHom hud _ A * primeFormFieldHom hud isPrimeFormGram_one4 φ) *
      (primeFormConjHom hud _ A * primeFormFieldHom hud isPrimeFormGram_one4 φ) = 1) :
    ∃ c : F9, ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) *
      ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9).map φ = c • 1 := by
  have hpsi : primeFormPsi hud isPrimeFormGram_one4
      ((⟨A, φ⟩ : primeFormUnitary hud ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) ⋊[
        primeFormFieldU hud isPrimeFormGram_one4] (F9 ≃+* F9)) * ⟨A, φ⟩) = 1 := by
    rw [map_mul, primeFormPsi_apply]
    exact hα
  obtain ⟨-, c, -, hcl⟩ :=
    (primeFormPsi_eq_one_iff hud isPrimeFormGram_one4 (by norm_num) _).mp hpsi
  refine ⟨(c : F9), ?_⟩
  change (A : GL (Fin 4) F9) * glAut φ (A : GL (Fin 4) F9) = GeneralLinearGroup.scalar (Fin 4) c
    at hcl
  have := congrArg (fun g : GL (Fin 4) F9 => (g : Matrix (Fin 4) (Fin 4) F9)) hcl
  simp only [Units.val_mul, coe_glAut] at this
  rw [coe_scalar_smul] at this
  exact this

theorem fix_of (A : primeFormUnitary hud ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9))
    (φ : F9 ≃+* F9) (g : SU4) (lam : F9) (hlam : lam ^ 4 = 1)
    (h : ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) *
        ((g : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9).map φ =
      lam • (((g : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) *
        ((A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9))) :
    (primeFormConjHom hud _ A * primeFormFieldHom hud isPrimeFormGram_one4 φ)
      (QuotientGroup.mk g : P43) = QuotientGroup.mk g := by
  rw [act_mk]
  symm
  rw [QuotientGroup.eq, mem_normOneScalars]
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam
  refine ⟨Units.mk0 lam hlam0, ?_, ?_, ?_⟩
  · rw [hud.norm_eq_pow]
    simpa using hlam
  · refine Units.ext ?_
    simpa using hlam
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul]
    refine Units.ext ?_
    simp only [conjField, Units.val_mul, coe_glAut, coe_scalar_smul]
    rw [h, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_one]
    rfl

theorem ringEquiv_cases (φ : F9 ≃+* F9) : (∀ x, φ x = x) ∨ (∀ x, φ x = barF x) := by
  have hI : φ (f9 0 1) * φ (f9 0 1) = -1 := by
    rw [← map_mul, show f9 0 1 * f9 0 1 = -1 by decide, map_neg, map_one]
  have hI' : φ (f9 0 1) = f9 0 1 ∨ φ (f9 0 1) = f9 0 2 := by
    revert hI
    generalize φ (f9 0 1) = y
    revert y
    decide
  have hprime : ∀ a : ZMod 3, φ (f9 a 0) = f9 a 0 := by
    intro a
    fin_cases a
    · exact map_zero φ
    · exact map_one φ
    · show φ (f9 2 0) = f9 2 0
      have : f9 2 0 = 1 + 1 := by decide
      rw [this, map_add, map_one]
  have hdecomp : ∀ x : F9, x = f9 x.re 0 + f9 x.im 0 * f9 0 1 := by decide
  rcases hI' with h | h
  · left
    intro x
    conv_lhs => rw [hdecomp x]
    rw [map_add, map_mul, hprime, hprime, h]
    exact (hdecomp x).symm
  · right
    intro x
    conv_lhs => rw [hdecomp x]
    rw [map_add, map_mul, hprime, hprime, h]
    revert x
    decide

theorem even_of_witness (g : Matrix (Fin 4) (Fin 4) F9) (h1 : (g.map barF)ᵀ * g = 1)
    (h2 : g.det = 1) (hq : ∃ c : F9, c ^ 4 = 1 ∧ qOf g * qOf g = c • 1)
    (hq' : ∀ c : F9, qOf g ≠ c • 1) :
    Even (orderOf (z5 * ((QuotientGroup.mk (suOf g h1 h2) : P43) * z5 *
      (QuotientGroup.mk (suOf g h1 h2) : P43)⁻¹))) := by
  set gS : SU4 := suOf g h1 h2 with hgS
  have hQ : z5 * ((QuotientGroup.mk gS : P43) * z5 * (QuotientGroup.mk gS : P43)⁻¹) =
      QuotientGroup.mk (zS * (gS * zS * gS⁻¹)) := by
    simp [z5, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hmat : (((zS * (gS * zS * gS⁻¹) : SU4) : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      qOf g := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, qOf]
    simp only [Matrix.mul_assoc]
    rfl
  rw [hQ]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (QuotientGroup.mk (zS * (gS * zS * gS⁻¹)) : P43) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, mk_eq_one_iff]
      obtain ⟨c, hc4, hc⟩ := hq
      refine ⟨c, hc4, ?_⟩
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_two, hmat, hc]
    · rw [Ne, mk_eq_one_iff]
      rintro ⟨c, -, hc⟩
      exact hq' c (hmat ▸ hc)
  rw [hord]
  exact even_two

theorem witness_even : ∀ g ∈ [gA, gB, gC], ∃ gS : SU4,
    ((gS : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = g ∧
      Even (orderOf (z5 * ((QuotientGroup.mk gS : P43) * z5 * (QuotientGroup.mk gS : P43)⁻¹))) := by
  intro g hg
  obtain ⟨h1, h2, hq, hq'⟩ := witness_spec g hg
  exact ⟨suOf g h1 h2, rfl, even_of_witness g h1 h2 hq hq'⟩

theorem E2_of (M : Matrix (Fin 4) (Fin 4) F9)
    (h : (M.map hud.bar)ᵀ * ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) * M =
      ((1 : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)) : (M.map barF)ᵀ * M = 1 := by
  have hb : M.map hud.bar = M.map barF := Matrix.ext fun i j => hud_bar _
  rwa [hb, Units.val_one, Matrix.mul_one] at h

end Mat

theorem u43_witness (α : MulAut P43) (hα : α * α = 1) (hz : α z5 = z5) :
    ∃ g : P43, α g = g ∧ Even (orderOf (z5 * (g * z5 * g⁻¹))) := by
  obtain ⟨A, φ, rfl⟩ := aut_form α
  have E1 := E1_of_fix A φ hz
  obtain ⟨c, E3⟩ := E3_of_sq A φ hα
  have E2 := E2_of _ (mem_primeFormUnitary.mp A.2)
  rcases ringEquiv_cases φ with hφ | hφ
  · obtain ⟨g, hg, lam, hlam, heq⟩ := finite_id φ.toRingHom hφ _ E1 E2 ⟨c, E3⟩
    obtain ⟨gS, rfl, hev⟩ := witness_even g hg
    exact ⟨QuotientGroup.mk gS, fix_of A φ gS lam (mu4_pow_four lam hlam) heq, hev⟩
  · obtain ⟨g, hg, lam, hlam, heq⟩ := finite_bar φ.toRingHom hφ _ E1 E2 ⟨c, E3⟩
    obtain ⟨gS, rfl, hev⟩ := witness_even g hg
    exact ⟨QuotientGroup.mk gS, fix_of A φ gS lam (mu4_pow_four lam hlam) heq, hev⟩

end CFSG.GH74.GLS.C3.Layer1.EndN.U43
