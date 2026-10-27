module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlPc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenOrth2

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Kl

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat diagGL coe_diagGL reflGL rotGL
  rotMat_apply_ne_zero)
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem false_of_k2_orth2 (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c) {n : ℕ} (hn : 5 ≤ n)
    [Fact (Irreducible (sqPoly c))] {w : Fin n → EAlg c} (hw : ∀ i, w i ≠ 0)
    (hw1 : ∀ i : Fin n, (i : ℕ) + 1 < n → w i = 1) {R : GL (Fin (2 * n)) K}
    (hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R)
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 c) * resMat (phiE c).toRingHom n (diagonal w))
    {M : Subgroup (GL (Fin (2 * n)) K)} (hd : K2Data R M) {gs : similarityPairs (oQ R)}
    (hσ : gs.val.right = 1)
    (hgA : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    (hQs : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ gs))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ gs)))) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  have hZ := commutator_iso_inf_centralizer_eq (φ := (phiE c).toRingHom)
    (σ := RingHom.id (EAlg c)) (r := AdjoinRoot.root (sqPoly c)) (phiE_injective c)
    (wOne_inv_mul hc0) (fun x => transpose_phiE_mul_wOne hc0 x) (phiE_root c)
    (fun M hM => phiE_mem_range hc0 hM) (diagonal w) hR hgA
  rw [uGrp_id_eq_iso hw] at hZ
  obtain ⟨hEf, hE⟩ := finite_ringChar_EAlg hK hc0
  have hinj := resGL_injective (phiE_injective c) n
  have hN : Group.IsSolvable (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ :
        Subgroup (GL (Fin (2 * n)) K)) ∨
      IsQuasisimple (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ :
        Subgroup (GL (Fin (2 * n)) K)) := by
    rw [hZ]
    rcases C.orth_block_cases hE (by omega : 3 ≤ n) (diagGL hw)
        (by rw [coe_diagGL]; exact diagonal_transpose _) with hsol | hqs | ⟨h4, -⟩
    · left
      exact Group.isSolvable_of_surjective
        (MonoidHom.subgroupMap_surjective (resGL (phiE c).toRingHom n) (C.omegaR (diagGL hw)))
    · right
      exact LocalCores.isQuasisimple_of_mulEquiv
        ((C.omegaR (diagGL hw)).equivMapOfInjective _ hinj) hqs
    · omega
  have hφa : ∀ a : K, (phiE c).toRingHom (algebraMap K (EAlg c) a) =
      algebraMap K (Matrix (Fin 2) (Fin 2) K) a := phiE_algebraMap c
  have hkron : ∀ X : GL (Fin n) K, (X : Matrix (Fin n) (Fin n) K)ᵀ * X = 1 →
      (∀ x y, (X : Matrix (Fin n) (Fin n) K) x y ≠ 0 → w x = w y) →
      kronGL K n X ∈ isoCent R gs.val.left := fun X hX hXw =>
    kronGL_mem_iso_inf (σ := RingHom.id (EAlg c)) hφa (fun _ => rfl)
      (fun x => transpose_phiE_mul_wOne hc0 x) (phiE_root c) hR hgA hX (map_mul_diagonal_comm hXw)
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set j₀ : Fin n := ⟨1, by omega⟩ with hj₀
  set k₀ : Fin n := ⟨2, by omega⟩ with hk₀
  have hij : i₀ ≠ j₀ := by simp [hi₀, hj₀, Fin.ext_iff]
  have h01 : (0 : K) ^ 2 + (1 : K) ^ 2 = 1 := by ring
  have hrefl : kronGL K n (reflGL i₀) ∈ isoCent R gs.val.left :=
    hkron _ (reflGL_orth i₀) fun x y h => by rw [reflGL_support i₀ h]
  have hrot : kronGL K n (rotGL i₀ j₀ hij h01) ∈ isoCent R gs.val.left := by
    refine hkron _ (rotGL_orth hij h01) fun x y h => ?_
    by_cases hxy : x = y
    · rw [hxy]
    have hi₀1 : (i₀ : ℕ) + 1 < n := by rw [hi₀]; simp only; omega
    have hj₀1 : (j₀ : ℕ) + 1 < n := by rw [hj₀]; simp only; omega
    rcases rotMat_apply_ne_zero hxy h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hx, hy, hw1 i₀ hi₀1, hw1 j₀ hj₀1]
    · rw [hx, hy, hw1 i₀ hi₀1, hw1 j₀ hj₀1]
  have hu : kronGL K n ⁅reflGL (K := K) i₀, rotGL i₀ j₀ hij h01⁆ ∈
      (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
    rw [map_commutatorElement]
    exact commutator_mem_commutator hrefl hrot
  have huv : ((kronGL K n ⁅reflGL (K := K) i₀, rotGL i₀ j₀ hij h01⁆ : GL (Fin (2 * n)) K) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K) = signMat K (pairSet {i₀, j₀}) := by
    rw [coe_kronGL, signMat_pair_eq_commutator hij h01, kronI_signMat]
  obtain ⟨huu, hu1, hun⟩ := signMat_pairSet_spec h2 (k := k₀)
    (by simp [hi₀, hk₀, Fin.ext_iff]) (by simp [hj₀, hk₀, Fin.ext_iff]) huv
  exact false_of_k2_isoCent hK hRs hd hσ hQs hQc hN hu huu hu1 hun

end CFSG.ComponentClassification.Burgoyne.DX.Kl
