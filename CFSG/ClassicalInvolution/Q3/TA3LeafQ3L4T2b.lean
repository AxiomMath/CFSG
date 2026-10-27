module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4T2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLb

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

namespace Q3L4

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL TBlocks HBlocks
open scoped MatrixGroups

variable {K : Type} [Field K] [Fintype K] (hK3 : Fintype.card K = 3)

include hK3 in
theorem ker_bdHom_iff (P : GL (Fin 4) K) (a b : SL(2, K)) :
    proj 4 K (bdHom P (a, b)) = 1 ↔ (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
  constructor
  · intro h
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h)
    have e : bd (a : Matrix (Fin 2) (Fin 2) K) (b : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
      rw [← cP4_bdHom_mk P a b, cP4, hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    have ha : (a : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
      have e1 := congrArg ul e
      rw [ul_bd] at e1
      rw [e1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ul]
    have hb : (b : Matrix (Fin 2) (Fin 2) K) = (c : K) • 1 := by
      have e1 := congrArg lr e
      rw [lr_bd] at e1
      rw [e1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lr]
    rcases eq_zero_or_eq_one_or_eq_neg_one hK3 (c : K) with h0 | h1 | h1
    · exact absurd h0 c.ne_zero
    · left
      refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
      · rw [ha, h1, one_smul, Matrix.SpecialLinearGroup.coe_one]
      · rw [hb, h1, one_smul, Matrix.SpecialLinearGroup.coe_one]
    · right
      refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
      · rw [ha, h1, neg_one_smul, Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_one]
      · rw [hb, h1, neg_one_smul, Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_one]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact map_one ((proj 4 K).comp (bdHom P))
    · apply proj_eq_one_iff.2
      rw [mem_scalars]
      refine ⟨-1, by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_one_sq, one_pow], ?_⟩
      have hbd : bd ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
          ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [bd]
      rw [coe_bdHom]
      change (P : Matrix (Fin 4) (Fin 4) K) * bd ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
        ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = _
      rw [hbd, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Units.val_neg, Units.val_one, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, neg_one_smul]

variable {P : GL (Fin 4) K} {X : SL(4, K)}
  (hXP : (X : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
    (P : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))

omit [Fintype K] in
include hXP in
theorem proj_bdHom_neg_one : proj 4 K (bdHom P (-1, 1)) = proj 4 K X := by
  refine (proj_eq_of_smul (neg_ne_zero.mpr one_ne_zero) ?_).symm
  have hb : bd ((-1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
      ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = (-1 : K) • X1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bd, X1]
  rw [val_eq_cP4 P (bdHom P (-1, 1)), val_eq_cP4 P X, cP4_bdHom_mk, cP4_X hXP, hb,
    Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype K] in
include hXP in
theorem isBD_cP4_of_comm (h2 : (2 : K) ≠ 0) {Y : SL(4, K)} (hY : Y * X = X * Y) :
    IsBD (cP4 P Y) := by
  have hm := congrArg (cP4 P) hY
  rw [cP4_mul, cP4_mul, cP4_X hXP] at hm
  exact isBD_of_comm_X1 h2 one_ne_zero hm

omit [Fintype K] in
include hXP in
theorem exists_conj_of_comm (h2 : (2 : K) ≠ 0) {G : SL(4, K)} (hG : G * X = X * G)
    (y : SL(2, K) × SL(2, K)) : ∃ z, bdHom P z = G * bdHom P y * G⁻¹ := by
  have hGi : G⁻¹ * X = X * G⁻¹ := by
    calc G⁻¹ * X = G⁻¹ * (X * G) * G⁻¹ := by group
      _ = G⁻¹ * (G * X) * G⁻¹ := by rw [hG]
      _ = X * G⁻¹ := by group
  have hy : bdHom P y * X = X * bdHom P y := Subtype.ext (bdHom_comm P hXP y)
  have hGy : G * bdHom P y * X = X * (G * bdHom P y) := by
    calc G * bdHom P y * X = G * (bdHom P y * X) := by group
      _ = G * (X * bdHom P y) := by rw [hy]
      _ = G * X * bdHom P y := by group
      _ = X * (G * bdHom P y) := by rw [hG]; group
  set Y := G * bdHom P y * G⁻¹ with hYdef
  have hYX : Y * X = X * Y := by
    calc Y * X = G * bdHom P y * (G⁻¹ * X) := by rw [hYdef]; group
      _ = G * bdHom P y * (X * G⁻¹) := by rw [hGi]
      _ = G * bdHom P y * X * G⁻¹ := by group
      _ = X * (G * bdHom P y) * G⁻¹ := by rw [hGy]
      _ = X * Y := by rw [hYdef]; group
  have hA := isBD_cP4_of_comm hXP h2 hG
  have hAi := isBD_cP4_of_comm hXP h2 hGi
  have hAy := isBD_cP4_of_comm hXP h2 hGy
  have hBy : IsBD (cP4 P (bdHom P y)) := by
    rw [cP4_bdHom]
    exact isBD_bd _ _
  have hBD := isBD_cP4_of_comm hXP h2 hYX
  have hdu : (ul (cP4 P Y)).det = 1 := by
    rw [hYdef, cP4_mul, ul_mul hAy hAi, cP4_mul, ul_mul hA hBy, cP4_bdHom, ul_bd, det_mul,
      det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one, ← det_mul, ← ul_mul hA hAi,
      ← cP4_mul, mul_inv_cancel, cP4_one, ul_one, det_one]
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hd : (cP4 P Y).det = 1 := by
    rw [cP4, det_mul, det_mul, mul_right_comm, ← det_mul, hPP, det_one, one_mul]
    exact Matrix.SpecialLinearGroup.det_coe Y
  have hdl : (lr (cP4 P Y)).det = 1 := by
    rw [det_of_isBD hBD, hdu, one_mul] at hd
    exact hd
  exact ⟨(⟨ul (cP4 P Y), hdu⟩, ⟨lr (cP4 P Y), hdl⟩),
    eq_of_cP4_eq P ((cP4_bdHom P _).trans (eq_bd hBD).symm)⟩

omit [Fintype K] in
theorem comm_of_anticomm {A B C : Matrix (Fin 4) (Fin 4) K} (h1 : B * C = (-1 : K) • (C * B))
    (h2 : A * C = (-1 : K) • (C * A)) : A * B * C = C * (A * B) := by
  calc A * B * C = A * (B * C) := Matrix.mul_assoc _ _ _
    _ = (-1 : K) • ((A * C) * B) := by rw [h1, Matrix.mul_smul, Matrix.mul_assoc]
    _ = C * (A * B) := by
        rw [h2, Matrix.smul_mul, smul_smul, neg_one_mul, neg_neg, one_smul, Matrix.mul_assoc]

include hK3 hXP in
theorem conj_mem_range_L4 (g : projectiveSL 4 K) (hg : g * proj 4 K X = proj 4 K X * g) :
    ∀ x ∈ ((proj 4 K).comp (bdHom P)).range,
      g * x * g⁻¹ ∈ ((proj 4 K).comp (bdHom P)).range := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨G, rfl⟩ := proj_surjective 4 K g
  have h2 := two_ne_zero' hK3
  have hgX : proj 4 K (X * G) = proj 4 K (G * X) := by rw [map_mul, map_mul, hg]
  obtain ⟨c, hc⟩ := InvClassL.eq_smul_of_proj_eq hgX
  rcases eq_zero_or_eq_one_or_eq_neg_one hK3 c with rfl | rfl | rfl
  · exfalso
    have hd := congrArg Matrix.det hc
    rw [zero_smul, Matrix.det_zero, Matrix.SpecialLinearGroup.det_coe] at hd
    exact one_ne_zero hd
  · rw [one_smul] at hc
    obtain ⟨z, hz⟩ := exists_conj_of_comm hXP h2 (Subtype.ext hc) y
    refine ⟨z, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [hz, map_mul, map_mul, map_inv]
  · have h1 : ((G * X : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
        (-1 : K) • ((X * G : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) := hc
    have h2' := val_swP_mul_X hXP
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h1 h2'
    have hG'X : swP P * G * X = X * (swP P * G) := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      exact comm_of_anticomm h1 h2'
    obtain ⟨z, hz⟩ := exists_conj_of_comm hXP h2 hG'X y
    refine ⟨(z.2, z.1), ?_⟩
    have e : G * bdHom P y * G⁻¹ = bdHom P (z.2, z.1) := by
      rw [← swP_conj P z.1 z.2, Prod.mk.eta, hz]
      calc G * bdHom P y * G⁻¹ =
          (swP P * swP P) * G * bdHom P y * G⁻¹ * ((swP P)⁻¹ * swP P) := by
            rw [swP_mul_swP, inv_mul_cancel]
            group
        _ = swP P * (swP P * G * bdHom P y * (swP P * G)⁻¹) * swP P := by group
    simp only [MonoidHom.comp_apply]
    rw [← e, map_mul, map_mul, map_inv]

end Q3L4

end CFSG.ClassicalInvolution.Q3.TA3
