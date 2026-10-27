module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClD4Sit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Orth2

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points pointMk pointMk_submodule
  exists_eq_pointMk)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.D4

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem ClO.d4_tri_false_of_ts {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived Q)))}
    {t y : MulAut (StatedProj (matrixDerived Q))} (h : ClO.D4Sit Q t Ro y)
    {g : similarityPairs Q} (hg1 : g.val.right = 1) (htg : t = oκ Q g)
    {W : Submodule K (Fin d → K)} (hW : IsTS Q 4 W) (hAW : subPerm g.val.left W = W)
    (hno : ∀ v : Fin d → K, v ≠ 0 → ∀ l : K,
      (g.val.left : Matrix (Fin d) (Fin d) K) *ᵥ v ≠ l • v) : False := by
  have hty : t * y = y * t := (h.comm y h.mem).symm
  have htW : (subStab Q W).map t.toMonoidHom = subStab Q W := by
    rw [htg, subStab_map_oκ hg1, hAW]
  obtain ⟨L, hL⟩ := (h.geom y (ClSp.odd_orderOf_of_mem h.odd h.mem) h.move).exists_pt_of_ts_map
    hty hW htW
  rw [htg, subStab_map_oκ hg1] at hL
  obtain ⟨μ, hμ⟩ := similitude_of_pair hg1
  have hLL := h.rigid (pointTransport g.val.left μ hμ L) L hL
  have hAL : subPerm g.val.left L.val = L.val := by
    rw [← pointTransport_val g.val.left μ hμ L, hLL]
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  rw [pointMk_submodule] at hAL
  have hmem : (g.val.left : Matrix (Fin d) (Fin d) K) *ᵥ x ∈ Submodule.span K {x} := by
    rw [← hAL]
    exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 hmem
  exact hno x hx l hl.symm

theorem ClO.d4_pc_ns_false (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c)
    {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (wMat 1 (-c)))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (jMat c))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (h : ClO.D4Sit (oQ R) (oκ _ g) Ro y) :
    False := by
  have hc0 : c ≠ 0 := fun h0 => hc ⟨0, by rw [h0, mul_zero]⟩
  obtain ⟨α, β, hαβ⟩ := exists_sq_sub_mul_sq hK hc0 (-1)
  have hW := pc_ns_ts hR hαβ
  have hA2 : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * g.val.left = c • 1 := by
    rw [hgA, blkDiag_eq, blkDiagF_mul, jMat_mul_self, ← blkDiag_eq (c • 1), blkDiag_smul,
      blkDiag_one']
  refine ClO.d4_tri_false_of_ts h hg1 rfl hW ?_ (fun v hv l => no_eigen_of_sq hA2 hc hv l)
  have hle : subPerm g.val.left (LinearMap.range (pcMap c α β)) ≤
      LinearMap.range (pcMap c α β) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ pcMap c α β x ∈ _
    rw [hgA, pcMap_jMat]
    exact ⟨_, rfl⟩
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [subPerm_apply, LinearEquiv.finrank_map_eq]

theorem ClO.d4_orth2_false (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c)
    [Fact (Irreducible (sqPoly c))] {w : Fin 4 → EAlg c} (hw : ∀ i, w i ≠ 0)
    (hw1 : ∀ i : Fin 4, (i : ℕ) + 1 < 4 → w i = 1) {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      blkDiag 4 (wMat 1 c) * resMat (phiE c).toRingHom 4 (diagonal w))
    (hdet : IsSquare (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).det)
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (jMat c))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (h : ClO.D4Sit (oQ R) (oκ _ g) Ro y) :
    False := by
  have hc0 : c ≠ 0 := fun h0 => hc ⟨0, by rw [h0, mul_zero]⟩
  have hdetR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).det = c ^ 4 * (phiE c (w 3)).det := by
    rw [hR, blkDiag_eq, resMat_diagonal_eq, blkDiagF_mul, det_blkDiagF, Fin.prod_univ_four]
    have hw' : ∀ i : Fin 4, (i : ℕ) + 1 < 4 → (wMat 1 c * (phiE c).toRingHom (w i)).det = c := by
      intro i hi
      rw [hw1 i hi, map_one, Matrix.mul_one, wMat, det_diagonal, Fin.prod_univ_two]
      simp
    rw [hw' 0 (by decide), hw' 1 (by decide), hw' 2 (by decide), det_mul, wMat, det_diagonal,
      Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    change c * c * c * (c * (phiE c (w 3)).det) = _
    ring
  have hN : IsSquare (phiE c (w 3)).det := by
    obtain ⟨r, hr⟩ := hdet
    refine ⟨r / c ^ 2, ?_⟩
    have hc4 : c ^ 4 ≠ 0 := pow_ne_zero 4 hc0
    rw [hdetR] at hr
    field_simp
    linear_combination hr
  obtain ⟨l, hl⟩ := isSquare_of_isSquare_det_phiE hK hc (hw 3) hN
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hw 3 (by rw [hl, mul_zero])
  obtain ⟨α, β, hαβ⟩ := exists_sq_sub_mul_sq hK (neg_ne_zero.2 one_ne_zero) (-1)
  have hαβ' : α ^ 2 + β ^ 2 = -1 := by linear_combination hαβ
  have hW := orth2_ts hc0 hw1 hl0 (by rw [hl, sq]) hαβ' hR
  have hA2 : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * g.val.left = c • 1 := by
    rw [hgA, blkDiag_eq, blkDiagF_mul, jMat_mul_self, ← blkDiag_eq (c • 1), blkDiag_smul,
      blkDiag_one']
  refine ClO.d4_tri_false_of_ts h hg1 rfl hW ?_ (fun v hv l => no_eigen_of_sq hA2 hc hv l)
  have hle : subPerm g.val.left (LinearMap.range (o2Map (phiE c l⁻¹) α β)) ≤
      LinearMap.range (o2Map (phiE c l⁻¹) α β) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ o2Map (phiE c l⁻¹) α β x ∈ _
    rw [hgA, o2Map_jMat]
    exact ⟨_, rfl⟩
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [subPerm_apply, LinearEquiv.finrank_map_eq]

end CFSG.ComponentClassification.Foote5.OddLieCore
