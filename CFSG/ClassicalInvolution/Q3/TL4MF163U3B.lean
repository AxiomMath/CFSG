module

public import CFSG.ClassicalInvolution.Q3.TL4MF163U3S
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF163.U3

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem eq_one_of_sq_of_cube {c : K} (h2 : c ^ 2 = 1) (h3 : c ^ 3 = 1) : c = 1 := by
  linear_combination h3 - c * h2

theorem block_of_inv (hq : 2 < p ^ f) (h2 : (2 : K) ≠ 0) {b : MulAut (unitaryPSU h 3)}
    (hb2 : b * b = 1) {l : K} (hl : l ^ 2 = -1) (hlu : h.bar l * l = 1)
    {dl : unitarySU p f K 3}
    (hdl : ((dl : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, -1])
    (hfix : b (dl : unitaryPSU h 3) = dl) :
    ∃ G : unitaryIsom3 h, b = psuConj h G ∧
      ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧
      ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  obtain ⟨G, τ, hb⟩ := exists_psuConj_mul_psuField (h := h) hq b
  have hτ : τ * τ = 1 := field_mul_self_eq_one h (B := 1) (by rw [← hb, hb2, map_one])
  rw [hb] at hfix
  obtain ⟨c, -, hc3, hc⟩ := exists_scalar_of_fix h hfix
  have hc3' : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  obtain ⟨hT, hE⟩ := mat_of_conj hc
  have hl0 : l ≠ 0 := fun h0 => by simp [h0] at hlu
  have hbl : h.bar l = -l := by
    have h1 : h.bar l = l⁻¹ := eq_inv_of_mul_eq_one_left hlu
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (by linear_combination -hl)
  rcases eq_one_or_barE h hτ with rfl | rfl
  · rw [map_one, mul_one] at hb
    have hD : ((glAut (1 : K ≃+* K) (dl : GL (Fin 3) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, -1] := by rw [map_one]; exact hdl
    rw [hD, hdl] at hT hE
    have htr := (MF163.trace_eq_of_conj hT).2
    simp [diagonal_mul_diagonal, Fin.sum_univ_three] at htr
    have hc2 : (c : K) ^ 2 = 1 := by linear_combination htr - 2 * (1 - (c : K) ^ 2) * hl
    rw [eq_one_of_sq_of_cube hc2 hc3', one_smul] at hE
    have hl1 : l ≠ -1 := fun h1 => h2 (by rw [h1] at hl; linear_combination hl)
    obtain ⟨z1, z2, z3, z4⟩ := MF163.block_of_commute_diag hl1 hE
    exact ⟨G, hb, z1, z2, z3, z4⟩
  · exfalso
    have hD : ((glAut (barE h) (dl : GL (Fin 3) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = diagonal ![-l, -l, -1] := by
      rw [coe_glAut, hdl, Matrix.diagonal_map (map_zero _)]
      congr 1
      ext i
      fin_cases i <;> simp [barE_apply, hbl]
    rw [hD, hdl] at hT
    obtain ⟨htr1, htr2⟩ := MF163.trace_eq_of_conj hT
    simp [diagonal_mul_diagonal, Fin.sum_univ_three] at htr1 htr2
    have hc2 : (c : K) ^ 2 = 1 := by linear_combination htr2 - 2 * (1 - (c : K) ^ 2) * hl
    rw [eq_one_of_sq_of_cube hc2 hc3'] at htr1
    have h4 : (2 : K) * (2 * l) = 0 := by linear_combination -htr1
    have hl0' : l = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h h2
      · exact (mul_eq_zero.mp h).resolve_left h2
    exact hl0 hl0'

theorem blk_of_comm {G M : unitaryIsom3 h} {m m' : K}
    (hG02 : ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0)
    (hG12 : ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    (hG20 : ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (hG21 : ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (hM : ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, m, 0; -m, 0, 0; 0, 0, m'])
    (hcomm : psuConj h G * (psuConj h M * psuField h (barE h)) =
      psuConj h M * psuField h (barE h) * psuConj h G) :
    ∃ A : GU2Stated (p ^ f) K, GeneralLinearGroup.det (A : GL (Fin 2) K) = 1 ∧
      psuConj h G = MulAut.conj ((Lemma41aU3.blkU h A : unitarySU p f K 3) : unitaryPSU h 3) := by
  set Gb : unitaryIsom3 h := ⟨glAut (barE h) G, glAut_mem_unitaryIsom3 _ G.2⟩ with hGb
  have hf : psuField h (barE h) * psuConj h G = psuConj h Gb * psuField h (barE h) := by
    rw [hGb, ← psuField_mul_psuConj_mul_inv]
    group
  have hGM : psuConj h (G * M) = psuConj h (M * Gb) := by
    have e : psuConj h G * psuConj h M * psuField h (barE h) =
        psuConj h M * psuConj h Gb * psuField h (barE h) := by
      calc psuConj h G * psuConj h M * psuField h (barE h)
          = psuConj h G * (psuConj h M * psuField h (barE h)) := by group
        _ = psuConj h M * psuField h (barE h) * psuConj h G := hcomm
        _ = psuConj h M * (psuField h (barE h) * psuConj h G) := by group
        _ = psuConj h M * psuConj h Gb * psuField h (barE h) := by rw [hf]; group
    rw [map_mul, map_mul]
    exact mul_right_cancel e
  have h1 : psuConj h ((M * Gb)⁻¹ * (G * M)) * psuField h 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, hGM, inv_mul_cancel]
  obtain ⟨-, ω, -, hωA⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ h1
  have hGL : (G : GL (Fin 3) K) * M =
      (M : GL (Fin 3) K) * Gb * GeneralLinearGroup.scalar (Fin 3) ω := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul] at hωA
    rw [← hωA]
    group
  have hmat := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hGL
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hmat
  have hGbm : ((Gb : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar := by
    rw [hGb]
    exact coe_glAut _ _
  rw [hGbm, hM] at hmat
  set g := ((G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hg
  have hU := mem_unitaryIsom3.mp G.2
  have u := fun i j => congrFun (congrFun hU i) j
  have u00 := u 0 0
  have u01 := u 0 1
  have u10 := u 1 0
  have u11 := u 1 1
  have u22 := u 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, ← hg, hG02, hG12, hG20, hG21] at u00 u01 u10 u11 u22
  have em := fun i j => congrFun (congrFun hmat i) j
  have e01 := em 0 1
  have e11 := em 1 1
  have e22 := em 2 2
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, hG02, hG12, hG20,
    hG21] at e01 e11 e22
  have hd := ((Matrix.isUnit_iff_isUnit_det _).mp (M : GL (Fin 3) K).isUnit).ne_zero
  rw [hM, Matrix.det_fin_three] at hd
  have hm : m ≠ 0 := fun h0 => hd (by simp [h0])
  have hm' : m' ≠ 0 := fun h0 => hd (by simp [h0])
  have ha : g 0 0 = h.bar (g 1 1) * ω := mul_left_cancel₀ hm (by linear_combination e01)
  have hc : g 1 0 = -(h.bar (g 0 1) * ω) := mul_left_cancel₀ hm (by linear_combination e11)
  have he : g 2 2 = h.bar (g 2 2) * ω := mul_left_cancel₀ hm' (by linear_combination e22)
  have he0 : g 2 2 ≠ 0 := fun h0 => by simp [h0] at u22
  have hω : (ω : K) = g 2 2 ^ 2 := by linear_combination -(g 2 2) * he - (ω : K) * u22
  set e := g 2 2 with hee
  set B : Matrix (Fin 2) (Fin 2) K := e⁻¹ • !![g 0 0, g 0 1; g 1 0, g 1 1] with hB
  have hdetB : B.det = 1 := by
    rw [hB, Matrix.det_smul, Fintype.card_fin, Matrix.det_fin_two_of, ha, hc, inv_pow,
      inv_mul_eq_one₀ (pow_ne_zero 2 he0)]
    linear_combination -(ω : K) * u11 - hω
  have hbe : (h.bar e)⁻¹ * e⁻¹ = 1 := by
    rw [← mul_inv, u22, inv_one]
  have hBu : (B.map h.bar)ᵀ * B = 1 := by
    rw [hB]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, map_mul]
    · linear_combination ((h.bar e)⁻¹ * e⁻¹) * u00 + hbe
    · linear_combination ((h.bar e)⁻¹ * e⁻¹) * u01
    · linear_combination ((h.bar e)⁻¹ * e⁻¹) * u10
    · linear_combination ((h.bar e)⁻¹ * e⁻¹) * u11 + hbe
  have hB0 : B.det ≠ 0 := by rw [hdetB]; exact one_ne_zero
  set BG : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero B hB0 with hBGdef
  have hBG : (BG : Matrix (Fin 2) (Fin 2) K) = B := rfl
  have hBmem : BG ∈ GU2Stated (p ^ f) K :=
    (Lemma41aU3.mem_GU2Stated_iff h).mpr (by rw [hBG]; exact hBu)
  refine ⟨⟨BG, hBmem⟩, Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact hdetB), ?_⟩
  set eU : Kˣ := Units.mk0 e he0 with heU
  have hne : h.norm (eU : K) = 1 := by
    rw [heU, Units.val_mk0, UnitaryFieldData.norm, mul_comm]
    exact u22
  set Y := Lemma41aU3.blkU h ⟨BG, hBmem⟩ with hY
  have hGeq : G = ⟨GeneralLinearGroup.scalar (Fin 3) eU, scalar_mem_unitaryIsom3 h hne⟩ *
      ⟨((Y : unitarySU p f K 3) : GL (Fin 3) K), unitarySU_le_unitaryIsom3 Y.2⟩ := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    rw [show ((Y : unitarySU p f K 3) : GL (Fin 3) K) = Lemma41aL3.blk BG from rfl,
      Lemma41aL3.coe_blk, hBG, hdetB, inv_one, heU, Units.val_mk0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Lemma41aL3.blkMat, hB, Matrix.scalar_apply, ← hg, hG02, hG12, hG20, hG21, he0, ← hee]
  rw [conj_mk_eq_psuConj, hGeq, map_mul, psuConj_scalar h hne, one_mul]

end CFSG.ClassicalInvolution.Q3.TL4.MF163.U3
