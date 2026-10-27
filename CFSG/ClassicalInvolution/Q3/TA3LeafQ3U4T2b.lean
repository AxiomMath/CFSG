module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3U4T2
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L4T2b

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

namespace Q3U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks UnitaryOut
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {R : GL (Fin 4) K} {t : K}
  (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
  {X : unitarySU p f K 4}
  (hXR : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
    (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K))

include hXR in
theorem exists_conj_of_comm_U (hp2 : p ≠ 2) (ht0 : t ≠ 0) {G : unitarySU p f K 4}
    (hG : G * X = X * G) (y : SL(2, h.fixedField) × SL(2, h.fixedField)) :
    G * bdHomU h hR y * G⁻¹ ∈ (bdHomU h hR).range := by
  have hGi : G⁻¹ * X = X * G⁻¹ := by
    calc G⁻¹ * X = G⁻¹ * (X * G) * G⁻¹ := by group
      _ = G⁻¹ * (G * X) * G⁻¹ := by rw [hG]
      _ = X * G⁻¹ := by group
  have hy := bdHomU_comm h hR hXR y
  have hGy : G * bdHomU h hR y * X = X * (G * bdHomU h hR y) := by
    calc G * bdHomU h hR y * X = G * (bdHomU h hR y * X) := by group
      _ = G * (X * bdHomU h hR y) := by rw [hy]
      _ = G * X * bdHomU h hR y := by group
      _ = X * (G * bdHomU h hR y) := by rw [hG]; group
  set Y := G * bdHomU h hR y * G⁻¹ with hYdef
  have hYX : Y * X = X * Y := by
    calc Y * X = G * bdHomU h hR y * (G⁻¹ * X) := by rw [hYdef]; group
      _ = G * bdHomU h hR y * (X * G⁻¹) := by rw [hGi]
      _ = G * bdHomU h hR y * X * G⁻¹ := by group
      _ = X * (G * bdHomU h hR y) * G⁻¹ := by rw [hGy]
      _ = X * Y := by rw [hYdef]; group
  have hA := isBD_cP_of_comm h hp2 hXR hG
  have hAi := isBD_cP_of_comm h hp2 hXR hGi
  have hAy := isBD_cP_of_comm h hp2 hXR hGy
  have hBy : IsBD (cP R (bdHomU h hR y)) := by
    rw [cP_bdHomU, bdK]
    exact isBD_bd _ _
  have hBD := isBD_cP_of_comm h hp2 hXR hYX
  have hdu : (ul (cP R Y)).det = 1 := by
    rw [hYdef, cP_mul, ul_mul hAy hAi, cP_mul, ul_mul hA hBy, cP_bdHomU, bdK, ul_bd, det_mul,
      det_mul, det_map_fixed, mul_one, ← det_mul, ← ul_mul hA hAi, ← cP_mul, mul_inv_cancel,
      cP_one, ul_one, det_one]
  exact mem_range_of_det_ul h ht0 hR hBD hdu

include hR hXR in
theorem conj_mem_range_U4 (hp2 : p ≠ 2) (ht0 : t ≠ 0)
    (hXX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = 1)
    (g : StatedProj (StatedSU 4 (p ^ f) K))
    (hg : g * QuotientGroup.mk X = QuotientGroup.mk X * g) :
    ∀ x ∈ ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).range,
      g * x * g⁻¹ ∈ ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).range := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨G, rfl⟩ := QuotientGroup.mk_surjective g
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have hX2 : X * X = 1 := ext_val (by rw [Subgroup.coe_mul, Units.val_mul, hXX]; rfl)
  have hs : G * X * G⁻¹ * X⁻¹ ∈ scal p f K := by
    have e : (QuotientGroup.mk (G * X * G⁻¹ * X⁻¹) : StatedProj (StatedSU 4 (p ^ f) K)) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hg]
      group
    exact (QuotientGroup.eq_one_iff _).mp e
  have hzc := mem_center_of_mem_scal hs
  obtain ⟨c, hc⟩ := val_of_mem_scal hs
  set z := G * X * G⁻¹ * X⁻¹ with hz
  have hz2 : z * z = 1 := by
    have e1 : G * X * G⁻¹ = z * X := by rw [hz]; group
    have e2 : (G * X * G⁻¹) * (G * X * G⁻¹) = 1 := by
      calc (G * X * G⁻¹) * (G * X * G⁻¹) = G * (X * X) * G⁻¹ := by group
        _ = 1 := by rw [hX2, mul_one, mul_inv_cancel]
    rw [e1] at e2
    have hXz : X * z = z * X := Subgroup.mem_center_iff.mp hzc X
    calc z * z = z * z * (X * X) := by rw [hX2, mul_one]
      _ = z * (X * z) * X := by rw [hXz]; group
      _ = z * X * (z * X) := by group
      _ = 1 := e2
  have hc2 : (c : K) * c = 1 := by
    have e := congrArg (fun w : unitarySU p f K 4 =>
      ((w : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) hz2
    simp only [Subgroup.coe_mul, Units.val_mul, hc, OneMemClass.coe_one, Units.val_one] at e
    simpa [Matrix.mul_apply, Fin.sum_univ_four] using e
  have hGX : G * X = z * (X * G) := by rw [hz]; group
  have hGX' : ((G : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) =
      (c : K) • (((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (G : GL (Fin 4) K)) := by
    have e := congrArg (fun w : unitarySU p f K 4 =>
      ((w : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hGX
    simp only [Subgroup.coe_mul, Units.val_mul, hc] at e
    rw [e, Matrix.smul_mul, Matrix.one_mul]
  have hc1 : ((c : K) - 1) * ((c : K) + 1) = 0 := by linear_combination hc2
  rcases mul_eq_zero.1 hc1 with h1 | h1
  · rw [sub_eq_zero.1 h1, one_smul] at hGX'
    have hGc : G * X = X * G := ext_val (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
      exact hGX')
    obtain ⟨w, hw⟩ := exists_conj_of_comm_U h hR hXR hp2 ht0 hGc y
    refine ⟨w, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [hw, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  · rw [eq_neg_of_add_eq_zero_left h1] at hGX'
    have h2' := val_swU_mul_X h hR hXR
    simp only [Subgroup.coe_mul, Units.val_mul] at h2'
    have hG'X : swU h hR * G * X = X * (swU h hR * G) := ext_val (by
      simp only [Subgroup.coe_mul, Units.val_mul]
      exact Q3L4.comm_of_anticomm hGX' h2')
    obtain ⟨w, hw⟩ := exists_conj_of_comm_U h hR hXR hp2 ht0 hG'X y
    refine ⟨(w.2, w.1), ?_⟩
    have e : G * bdHomU h hR y * G⁻¹ = bdHomU h hR (w.2, w.1) := by
      rw [← swU_conj h hR w.1 w.2, Prod.mk.eta, hw]
      calc G * bdHomU h hR y * G⁻¹ =
          (swU h hR * swU h hR) * G * bdHomU h hR y * G⁻¹ * ((swU h hR)⁻¹ * swU h hR) := by
            rw [swU_mul_swU, inv_mul_cancel]
            group
        _ = swU h hR * (swU h hR * G * bdHomU h hR y * (swU h hR * G)⁻¹) * swU h hR := by group
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [← e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

end Q3U4

end CFSG.ClassicalInvolution.Q3.TA3
