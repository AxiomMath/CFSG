module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3Basic

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.Steinberg Matrix
open scoped MatrixGroups

section Block

variable {K : Type} [Field K]

@[expose] def D3 : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![-1, -1, 1]

theorem D3_mul_D3 : (D3 : Matrix (Fin 3) (Fin 3) K) * D3 = 1 := by
  rw [D3, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

@[expose] def D3GL : GL (Fin 3) K := ⟨D3, D3, D3_mul_D3, D3_mul_D3⟩

theorem coe_D3GL : ((D3GL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = D3 := rfl

theorem commute_D3_entries (h2 : (2 : K) ≠ 0) {x : Matrix (Fin 3) (Fin 3) K}
    (hx : x * D3 = D3 * x) : x 0 2 = 0 ∧ x 1 2 = 0 ∧ x 2 0 = 0 ∧ x 2 1 = 0 := by
  have k02 : x 0 2 * 1 = -1 * x 0 2 := by
    simpa [D3, Matrix.mul_diagonal, Matrix.diagonal_mul] using congrFun (congrFun hx 0) 2
  have k12 : x 1 2 * 1 = -1 * x 1 2 := by
    simpa [D3, Matrix.mul_diagonal, Matrix.diagonal_mul] using congrFun (congrFun hx 1) 2
  have k20 : x 2 0 * -1 = 1 * x 2 0 := by
    simpa [D3, Matrix.mul_diagonal, Matrix.diagonal_mul] using congrFun (congrFun hx 2) 0
  have k21 : x 2 1 * -1 = 1 * x 2 1 := by
    simpa [D3, Matrix.mul_diagonal, Matrix.diagonal_mul] using congrFun (congrFun hx 2) 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (2 : K) * x 0 2 = 0 := by linear_combination k02
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : K) * x 1 2 = 0 := by linear_combination k12
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : K) * x 2 0 = 0 := by linear_combination (-1 : K) * k20
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : K) * x 2 1 = 0 := by linear_combination (-1 : K) * k21
    exact (mul_eq_zero.mp this).resolve_left h2

theorem eq_embPair_of_commute_fix (h2 : (2 : K) ≠ 0) {x : Matrix (Fin 3) (Fin 3) K}
    (hx : x * D3 = D3 * x) (he : x *ᵥ Pi.single 2 1 = Pi.single 2 1) :
    x = embPair 2 !![x 0 0, x 0 1; x 1 0, x 1 1] := by
  obtain ⟨h02, h12, h20, h21⟩ := commute_D3_entries h2 hx
  have h22 : x 2 2 = 1 := by
    have := congrFun he 2
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair, h02, h12, h20, h21, h22]

theorem mulVec_single_of_commute (h2 : (2 : K) ≠ 0) {x : Matrix (Fin 3) (Fin 3) K}
    (hx : x * D3 = D3 * x) : x *ᵥ Pi.single 2 1 = x 2 2 • Pi.single 2 1 := by
  obtain ⟨h02, h12, -, -⟩ := commute_D3_entries h2 hx
  rw [Matrix.mulVec_single_one]
  ext i
  fin_cases i <;> simp [h02, h12]

@[expose] def blockSub (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {y | ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 2 1 =
      Pi.single 2 1 ∧ y * D3GL = D3GL * y}
  mul_mem' {y z} hy hz := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hz.1, hy.1]
    · rw [mul_assoc, hz.2, ← mul_assoc, hy.2, mul_assoc]
  one_mem' := ⟨by rw [Units.val_one, Matrix.one_mulVec], by simp⟩
  inv_mem' {y} hy := by
    refine ⟨?_, ?_⟩
    · have h := congrArg (fun v => ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) hy.1
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] at h
      exact h.symm
    · calc y⁻¹ * D3GL = y⁻¹ * (D3GL * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * D3GL) * y⁻¹ := by rw [hy.2]
        _ = D3GL * y⁻¹ := by group

theorem conj_mem_blockSub (h2 : (2 : K) ≠ 0) {g n : GL (Fin 3) K} (hg : g * D3GL = D3GL * g)
    (hn : n ∈ blockSub K) : g * n * g⁻¹ ∈ blockSub K := by
  have hgm : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * D3 =
      D3 * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun y : GL (Fin 3) K => ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hg
    simpa [coe_D3GL] using this
  have hv := mulVec_single_of_commute h2 hgm
  have hb : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hv
    have h1 := congrArg (fun v => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) hv
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    have := congrFun h1 2
    simp at this
  set b : K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 with hbdef
  have hinvv : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 2 1 =
      b⁻¹ • Pi.single 2 1 := by
    have h1 : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (b⁻¹ • Pi.single 2 1) =
        Pi.single 2 1 := by
      rw [Matrix.mulVec_smul, hv, smul_smul, inv_mul_cancel₀ hb, one_smul]
    have h2' := congrArg (fun v => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h2'
    exact h2'.symm
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinvv,
      Matrix.mulVec_smul, hn.1, Matrix.mulVec_smul, hv, smul_smul, inv_mul_cancel₀ hb, one_smul]
  · have hginv : g⁻¹ * D3GL = D3GL * g⁻¹ := by
      calc g⁻¹ * D3GL = g⁻¹ * (D3GL * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * D3GL) * g⁻¹ := by rw [hg]
        _ = D3GL * g⁻¹ := by group
    calc g * n * g⁻¹ * D3GL = g * n * (g⁻¹ * D3GL) := by group
      _ = g * (n * D3GL) * g⁻¹ := by rw [hginv]; group
      _ = g * (D3GL * n) * g⁻¹ := by rw [hn.2]
      _ = (g * D3GL) * n * g⁻¹ := by group
      _ = D3GL * g * n * g⁻¹ := by rw [hg]
      _ = D3GL * (g * n * g⁻¹) := by group

@[expose] def Nst (Hg : Subgroup (GL (Fin 3) K)) (P : GL (Fin 3) K) : Subgroup (GL (Fin 3) K) :=
  Hg ⊓ (blockSub K).comap (MulAut.conj P⁻¹).toMonoidHom

theorem mem_Nst_iff {Hg : Subgroup (GL (Fin 3) K)} {P x : GL (Fin 3) K} :
    x ∈ Nst Hg P ↔ x ∈ Hg ∧ P⁻¹ * x * P ∈ blockSub K := by
  simp [Nst]

section Adapted

variable (Hg : Subgroup (GL (Fin 3) K)) (A : Hg) (P : GL (Fin 3) K)

theorem eq_conj_D3GL (hAP : (A : GL (Fin 3) K) * P = P * D3GL) :
    (A : GL (Fin 3) K) = P * D3GL * P⁻¹ := by
  calc (A : GL (Fin 3) K) = A * P * P⁻¹ := by group
    _ = P * D3GL * P⁻¹ := by rw [hAP]

theorem Nst_commute (hAP : (A : GL (Fin 3) K) * P = P * D3GL) {n : GL (Fin 3) K}
    (hn : n ∈ Nst Hg P) : n * (A : GL (Fin 3) K) = (A : GL (Fin 3) K) * n := by
  have hn' : (P⁻¹ * n * P) * D3GL = D3GL * (P⁻¹ * n * P) := (mem_Nst_iff.1 hn).2.2
  have e1 : n * (P * D3GL * P⁻¹) = P * ((P⁻¹ * n * P) * D3GL) * P⁻¹ := by group
  have e2 : (P * D3GL * P⁻¹) * n = P * (D3GL * (P⁻¹ * n * P)) * P⁻¹ := by group
  rw [eq_conj_D3GL Hg A P hAP, e1, e2, hn']

theorem Nst_scalar {n : GL (Fin 3) K} (hn : n ∈ Nst Hg P) (hs : n ∈ StatedScalars (Fin 3) K) :
    n = 1 := by
  obtain ⟨c, rfl⟩ := hs
  have hcent : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcomm : P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) c =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * P⁻¹ := Subgroup.mem_center_iff.1 hcent P⁻¹
  have hconj : P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 3) c * P =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    rw [hcomm, mul_assoc, inv_mul_cancel, mul_one]
  have hfix := (mem_Nst_iff.1 hn).2.1
  rw [hconj] at hfix
  have h2 := congrFun hfix 2
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal] at h2
  have hc : c = 1 := h2
  rw [hc, map_one]

theorem Nst_normalized (h2 : (2 : K) ≠ 0) (hAP : (A : GL (Fin 3) K) * P = P * D3GL)
    {g : GL (Fin 3) K} (hg : g ∈ Hg) (hgA : g * (A : GL (Fin 3) K) = (A : GL (Fin 3) K) * g)
    {n : GL (Fin 3) K} (hn : n ∈ Nst Hg P) : g * n * g⁻¹ ∈ Nst Hg P := by
  have hPD : P * D3GL = (A : GL (Fin 3) K) * P := hAP.symm
  have hPAP : P⁻¹ * (A : GL (Fin 3) K) * P = D3GL := by
    calc P⁻¹ * (A : GL (Fin 3) K) * P = P⁻¹ * ((A : GL (Fin 3) K) * P) := by rw [mul_assoc]
      _ = D3GL := by rw [hAP]; group
  have hgD : (P⁻¹ * g * P) * D3GL = D3GL * (P⁻¹ * g * P) := by
    calc (P⁻¹ * g * P) * D3GL = P⁻¹ * g * (P * D3GL) := by group
      _ = P⁻¹ * (g * (A : GL (Fin 3) K)) * P := by rw [hPD]; group
      _ = P⁻¹ * ((A : GL (Fin 3) K) * g) * P := by rw [hgA]
      _ = (P⁻¹ * (A : GL (Fin 3) K) * P) * (P⁻¹ * g * P) := by group
      _ = D3GL * (P⁻¹ * g * P) := by rw [hPAP]
  refine mem_Nst_iff.2 ⟨Hg.mul_mem (Hg.mul_mem hg (mem_Nst_iff.1 hn).1) (Hg.inv_mem hg), ?_⟩
  have h := conj_mem_blockSub h2 hgD (mem_Nst_iff.1 hn).2
  have e : P⁻¹ * (g * n * g⁻¹) * P =
      (P⁻¹ * g * P) * (P⁻¹ * n * P) * (P⁻¹ * g * P)⁻¹ := by group
  rw [e]
  exact h

theorem not_charTwo_centralizer_of_adapted [Finite K] (h2 : (2 : K) ≠ 0)
    (hdet : ∀ g ∈ Hg, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hA2 : A * A = 1) (hAP : (A : GL (Fin 3) K) * P = P * D3GL)
    (hq : CFSG.IsQuasisimple (Nst Hg P)) :
    ¬ CharTwo (Subgroup.centralizer
      ({(QuotientGroup.mk A : StatedProj Hg)} : Set (StatedProj Hg))) := by
  refine not_charTwo_centralizer_of_component Hg A (Nst Hg P) inf_le_left hq
    (fun n hn => Nst_commute Hg A P hAP hn) ?_ (fun n hn hs => Nst_scalar Hg P hn hs)
  intro g hg u hu n hn
  have hA2m : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := congrArg (fun y : Hg => ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hA2
    simpa using this
  have hcomm := commute_of_scalar_commute (ι := Fin 3) (by simp) hA2m (hdet _ A.2)
    (hdet _ hg) (u : K) hu
  have hgA : g * (A : GL (Fin 3) K) = (A : GL (Fin 3) K) * g := Units.ext hcomm
  exact Nst_normalized Hg A P h2 hAP hg hgA hn

end Adapted

end Block

end CFSG.QuasithinUnique.Ch1
