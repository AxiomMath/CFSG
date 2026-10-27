module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Blk
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPcCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Tri
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPairNorm

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points pointMk pointMk_submodule
  exists_eq_pointMk)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (signMat signMat_mul_self reflGL rotGL
  mul_conj_mul_inv)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem similitude_of_pair {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {g : similarityPairs Q}
    (hg : g.val.right = 1) :
    ∃ μ : Kˣ, ∀ v, Q ((g.val.left : Matrix (Fin d) (Fin d) K) *ᵥ v) = μ * Q v := by
  obtain ⟨μ, hμ⟩ := g.2
  refine ⟨μ, fun v => ?_⟩
  have e := hμ v
  rw [coordinateSemilinearMap_apply, hg] at e
  simpa using e

theorem no_eigen_of_sq {d : ℕ} {A : Matrix (Fin d) (Fin d) K} {c : K} (hA2 : A * A = c • 1)
    (hc : ¬ IsSquare c) {v : Fin d → K} (hv : v ≠ 0) (l : K) : A *ᵥ v ≠ l • v := by
  intro h
  have e : A *ᵥ (A *ᵥ v) = (l * l) • v := by rw [h, mulVec_smul, h, smul_smul]
  rw [mulVec_mulVec, hA2, smul_mulVec, one_mulVec] at e
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc'
    push Not at hc'
    exact hv (funext hc')
  have := congrFun e i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact hc ⟨l, mul_right_cancel₀ hi this⟩

theorem tri_false_of_ts [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    {B : Subgroup (MulAut (StatedProj (matrixDerived Q)))}
    {t y : MulAut (StatedProj (matrixDerived Q))} (h : Sit Q B t y)
    {g : similarityPairs Q} (hg1 : g.val.right = 1) (htg : t = oκ Q g)
    {W : Submodule K (Fin d → K)} (hW : IsTS Q 4 W) (hAW : subPerm g.val.left W = W)
    (hno : ∀ v : Fin d → K, v ≠ 0 → ∀ l : K,
      (g.val.left : Matrix (Fin d) (Fin d) K) *ᵥ v ≠ l • v) : False := by
  have hty : t * y = y * t := (commute_of_mem_oddCoreIn h.core).symm
  have htW : (subStab Q W).map t.toMonoidHom = subStab Q W := by
    rw [htg, subStab_map_oκ hg1, hAW]
  obtain ⟨L, hL⟩ := (h.geom y (odd_orderOf_of_mem_oddCoreIn h.core) h.move).exists_pt_of_ts_map
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

theorem oQ_blkDiag_pc {R : GL (Fin (2 * 4)) K} {c : K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (wMat 1 (-c)))
    (u : Fin 4 → Fin 2 → K) : oQ R (blkVec u) = ∑ i, (u i 0 ^ 2 - c * u i 1 ^ 2) := by
  rw [oQ_apply, hR, blkDiag_eq, dot_blkDiagF]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [wMat, mulVec, dotProduct, Fin.sum_univ_two, diagonal]
  ring

@[expose] def lamMat (c α β : K) : Matrix (Fin 2) (Fin 2) K := α • 1 + β • jMat c

theorem lamMat_comm (c α β : K) : jMat c * lamMat c α β = lamMat c α β * jMat c := by
  rw [lamMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem norm_lamMat {c α β : K} (hαβ : α ^ 2 - c * β ^ 2 = -1) (z : Fin 2 → K) :
    (lamMat c α β *ᵥ z) 0 ^ 2 - c * (lamMat c α β *ᵥ z) 1 ^ 2 = -(z 0 ^ 2 - c * z 1 ^ 2) := by
  simp [lamMat, jMat, mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (z 0 ^ 2 - c * z 1 ^ 2) * hαβ

@[expose] def pcBlk (c α β : K) (x : Fin 2 → Fin 2 → K) : Fin 4 → Fin 2 → K :=
  ![x 0, lamMat c α β *ᵥ x 0, x 1, lamMat c α β *ᵥ x 1]

theorem pcBlk_zero (c α β : K) (x : Fin 2 → Fin 2 → K) : pcBlk c α β x 0 = x 0 := rfl
theorem pcBlk_one (c α β : K) (x : Fin 2 → Fin 2 → K) :
    pcBlk c α β x 1 = lamMat c α β *ᵥ x 0 := rfl
theorem pcBlk_two (c α β : K) (x : Fin 2 → Fin 2 → K) : pcBlk c α β x 2 = x 1 := rfl
theorem pcBlk_three (c α β : K) (x : Fin 2 → Fin 2 → K) :
    pcBlk c α β x 3 = lamMat c α β *ᵥ x 1 := rfl

theorem pcBlk_add (c α β : K) (x x' : Fin 2 → Fin 2 → K) :
    pcBlk c α β (x + x') = pcBlk c α β x + pcBlk c α β x' := by
  funext i
  fin_cases i
  · rfl
  · change lamMat c α β *ᵥ (x 0 + x' 0) = lamMat c α β *ᵥ x 0 + lamMat c α β *ᵥ x' 0
    exact mulVec_add _ _ _
  · rfl
  · change lamMat c α β *ᵥ (x 1 + x' 1) = lamMat c α β *ᵥ x 1 + lamMat c α β *ᵥ x' 1
    exact mulVec_add _ _ _

theorem pcBlk_smul (c α β a : K) (x : Fin 2 → Fin 2 → K) :
    pcBlk c α β (a • x) = a • pcBlk c α β x := by
  funext i
  fin_cases i
  · rfl
  · change lamMat c α β *ᵥ (a • x 0) = a • lamMat c α β *ᵥ x 0
    exact mulVec_smul _ _ _
  · rfl
  · change lamMat c α β *ᵥ (a • x 1) = a • lamMat c α β *ᵥ x 1
    exact mulVec_smul _ _ _

@[expose] def pcMap (c α β : K) : (Fin 2 → Fin 2 → K) →ₗ[K] (Fin (2 * 4) → K) where
  toFun x := blkVec (pcBlk c α β x)
  map_add' x x' := by
    rw [pcBlk_add]
    rfl
  map_smul' a x := by
    rw [pcBlk_smul]
    rfl

theorem pcMap_apply (c α β : K) (x : Fin 2 → Fin 2 → K) :
    pcMap c α β x = blkVec (pcBlk c α β x) := rfl

theorem pcMap_injective (c α β : K) : Function.Injective (pcMap c α β) := by
  intro x x' h
  have h0 := congrArg blkOf h
  rw [pcMap_apply, pcMap_apply, blkOf_blkVec, blkOf_blkVec] at h0
  funext k j
  fin_cases k
  · exact congrFun (congrFun h0 0) j
  · exact congrFun (congrFun h0 2) j

theorem pc_ns_ts [Finite K] {R : GL (Fin (2 * 4)) K} {c α β : K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (wMat 1 (-c)))
    (hαβ : α ^ 2 - c * β ^ 2 = -1) :
    IsTS (oQ R) 4 (LinearMap.range (pcMap c α β)) := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (pcMap_injective c α β)]
    simp [Module.finrank_pi_fintype]
  · rintro _ ⟨x, rfl⟩
    rw [pcMap_apply, oQ_blkDiag_pc hR, Fin.sum_univ_four, pcBlk_zero, pcBlk_one, pcBlk_two,
      pcBlk_three, norm_lamMat hαβ, norm_lamMat hαβ]
    ring

theorem pcMap_jMat (c α β : K) (x : Fin 2 → Fin 2 → K) :
    blkDiag 4 (jMat c) *ᵥ pcMap c α β x = pcMap c α β fun k => jMat c *ᵥ x k := by
  rw [pcMap_apply, pcMap_apply, blkDiag_eq, blkDiagF_mulVec]
  congr 1
  funext i
  fin_cases i
  · rfl
  · change jMat c *ᵥ (lamMat c α β *ᵥ x 0) = lamMat c α β *ᵥ (jMat c *ᵥ x 0)
    rw [mulVec_mulVec, mulVec_mulVec, lamMat_comm]
  · rfl
  · change jMat c *ᵥ (lamMat c α β *ᵥ x 1) = lamMat c α β *ᵥ (jMat c *ᵥ x 1)
    rw [mulVec_mulVec, mulVec_mulVec, lamMat_comm]

theorem pc_ns_false [Finite K] (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c)
    {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (wMat 1 (-c)))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (jMat c))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (h : Sit (oQ R) B (oκ _ g) y) : False := by
  have hc0 : c ≠ 0 := fun h0 => hc ⟨0, by rw [h0, mul_zero]⟩
  obtain ⟨α, β, hαβ⟩ := exists_sq_sub_mul_sq hK hc0 (-1)
  have hW := pc_ns_ts hR hαβ
  have hA2 : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * g.val.left = c • 1 := by
    rw [hgA, blkDiag_eq, blkDiagF_mul, jMat_mul_self, ← blkDiag_eq (c • 1), blkDiag_smul,
      blkDiag_one']
  refine tri_false_of_ts h hg1 rfl hW ?_ (fun v hv l => no_eigen_of_sq hA2 hc hv l)
  have hle : subPerm g.val.left (LinearMap.range (pcMap c α β)) ≤
      LinearMap.range (pcMap c α β) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ pcMap c α β x ∈ _
    rw [hgA, pcMap_jMat]
    exact ⟨_, rfl⟩
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [subPerm_apply, LinearEquiv.finrank_map_eq]

end CFSG.ComponentClassification.Burgoyne.D4
