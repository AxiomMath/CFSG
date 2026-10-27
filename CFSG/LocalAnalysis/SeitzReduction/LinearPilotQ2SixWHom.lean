module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWOne
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBHom

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix

@[expose] def kleinFiveA : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def kleinFiveB : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 1, 0; 0, 1, 1, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem kleinFiveA_mul_self : kleinFiveA * kleinFiveA = 1 := by
  decide +kernel

theorem kleinFiveB_mul_self : kleinFiveB * kleinFiveB = 1 := by
  decide +kernel

theorem kleinFive_mul_mul_mul : kleinFiveA * kleinFiveB * kleinFiveA * kleinFiveB = 1 := by
  decide +kernel

theorem kleinFiveA_submatrix :
    kleinFiveA.submatrix Fin.castSucc Fin.castSucc = kleinFourA := by
  decide +kernel

theorem kleinFiveB_submatrix :
    kleinFiveB.submatrix Fin.castSucc Fin.castSucc = kleinFourB := by
  decide +kernel

theorem kleinFiveA_castSucc_last (i : Fin 4) : kleinFiveA (Fin.castSucc i) (Fin.last 4) = 0 := by
  revert i
  decide +kernel

theorem kleinFiveA_last_castSucc (j : Fin 4) : kleinFiveA (Fin.last 4) (Fin.castSucc j) = 0 := by
  revert j
  decide +kernel

theorem kleinFiveB_castSucc_last (i : Fin 4) : kleinFiveB (Fin.castSucc i) (Fin.last 4) = 0 := by
  revert i
  decide +kernel

theorem kleinFiveB_last_castSucc (j : Fin 4) : kleinFiveB (Fin.last 4) (Fin.castSucc j) = 0 := by
  revert j
  decide +kernel

theorem mul_eq_zero_of_redFour_eq_zero {p q : ZMod 4} (hp : redFour p = 0) (hq : redFour q = 0) :
    p * q = 0 := by
  revert p q
  decide +kernel

theorem submatrix_castSucc_mul {m : ℕ} (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 4))
    (hA : ∀ i : Fin m, redFour (A (Fin.castSucc i) (Fin.last m)) = 0)
    (hB : ∀ j : Fin m, redFour (B (Fin.last m) (Fin.castSucc j)) = 0) :
    (A * B).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix Fin.castSucc Fin.castSucc * B.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  rw [submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
    mul_eq_zero_of_redFour_eq_zero (hA i) (hB j), add_zero, Matrix.mul_apply]
  rfl

theorem one_submatrix_castSucc {m : ℕ} :
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 4)).submatrix Fin.castSucc Fin.castSucc = 1 :=
  Matrix.submatrix_one _ (Fin.castSucc_injective m)

theorem not_exists_lift_kleinFive {A B : Matrix (Fin 5) (Fin 5) (ZMod 4)}
    (hA : A.map redFour = kleinFiveA) (hB : B.map redFour = kleinFiveB) (hAA : A * A = 1)
    (hBB : B * B = 1) (hAB : A * B = B * A) : False := by
  have hAc : ∀ i : Fin 4, redFour (A (Fin.castSucc i) (Fin.last 4)) = 0 := fun i => by
    have h := congrFun (congrFun hA (Fin.castSucc i)) (Fin.last 4)
    rw [Matrix.map_apply] at h
    rw [h, kleinFiveA_castSucc_last]
  have hAr : ∀ j : Fin 4, redFour (A (Fin.last 4) (Fin.castSucc j)) = 0 := fun j => by
    have h := congrFun (congrFun hA (Fin.last 4)) (Fin.castSucc j)
    rw [Matrix.map_apply] at h
    rw [h, kleinFiveA_last_castSucc]
  have hBc : ∀ i : Fin 4, redFour (B (Fin.castSucc i) (Fin.last 4)) = 0 := fun i => by
    have h := congrFun (congrFun hB (Fin.castSucc i)) (Fin.last 4)
    rw [Matrix.map_apply] at h
    rw [h, kleinFiveB_castSucc_last]
  have hBr : ∀ j : Fin 4, redFour (B (Fin.last 4) (Fin.castSucc j)) = 0 := fun j => by
    have h := congrFun (congrFun hB (Fin.last 4)) (Fin.castSucc j)
    rw [Matrix.map_apply] at h
    rw [h, kleinFiveB_last_castSucc]
  refine not_exists_lift_kleinFour (A := A.submatrix Fin.castSucc Fin.castSucc)
    (B := B.submatrix Fin.castSucc Fin.castSucc) ?_ ?_ ?_ ?_ ?_
  · rw [← kleinFiveA_submatrix, ← hA]
    rfl
  · rw [← kleinFiveB_submatrix, ← hB]
    rfl
  · rw [← submatrix_castSucc_mul A A hAc hAr, hAA, one_submatrix_castSucc]
  · rw [← submatrix_castSucc_mul B B hBc hBr, hBB, one_submatrix_castSucc]
  · rw [← submatrix_castSucc_mul A B hAc hBr, ← submatrix_castSucc_mul B A hBc hAr, hAB]

theorem homocyclicExclusionCardInput_five : HomocyclicExclusionCardInput 5 := by
  intro G _ _ W V L₁ hcomm hWc hVW hVc hV2 hWV hL₁W _ haut hfaith
  by_contra hcon
  obtain ⟨w₀, hw₀, hw₀1⟩ : ∃ w ∈ W, w * w ≠ 1 := by
    by_contra h'
    exact hcon fun w hw => by_contra fun h => h' ⟨w, hw, h⟩
  have hsq : ∀ v ∈ V, ∃ w ∈ W, w * w = v := by
    intro v hv
    by_cases hv1 : v = 1
    · exact ⟨1, one_mem _, by rw [hv1, one_mul]⟩
    obtain ⟨l, hl, hlv⟩ :=
      exists_conj_eq_of_forall_mulEquiv' hVc hV2 haut (hWV w₀ hw₀) hv hw₀1 hv1
    refine ⟨l * w₀ * l⁻¹, (mem_normalizer_iff.1 (hL₁W hl) w₀).1 hw₀, ?_⟩
    rw [← hlv]
    group
  obtain ⟨b⟩ := exists_elemBasis hVc hV2
  choose w hw hww using fun i : Fin 5 => hsq (b (Pi.single i 1)) (b.mem _)
  obtain ⟨Φ, hΦ⟩ := exists_z4Basis hcomm (by rw [hWc]; norm_num) hVW hV2 b hw hww
  obtain ⟨la, hla, hlav⟩ := b.exists_conj_eq_of_forall_mulEquiv haut kleinFiveA kleinFiveA
    kleinFiveA_mul_self kleinFiveA_mul_self
  obtain ⟨lb, hlb, hlbv⟩ := b.exists_conj_eq_of_forall_mulEquiv haut kleinFiveB kleinFiveB
    kleinFiveB_mul_self kleinFiveB_mul_self
  have hrel : ∀ g ∈ L₁, (∀ x, g * b x * g⁻¹ = b x) → g = 1 := fun g hg h =>
    hfaith g hg fun v hv => by
      obtain ⟨x, rfl⟩ := b.exists_eq hv
      exact h x
  have haa : la * la = 1 := hrel _ (mul_mem hla hla) fun x => by
    calc la * la * b x * (la * la)⁻¹ = la * (la * b x * la⁻¹) * la⁻¹ := by group
      _ = b (kleinFiveA *ᵥ (kleinFiveA *ᵥ x)) := by rw [hlav, hlav]
      _ = b x := by rw [Matrix.mulVec_mulVec, kleinFiveA_mul_self, Matrix.one_mulVec]
  have hbb : lb * lb = 1 := hrel _ (mul_mem hlb hlb) fun x => by
    calc lb * lb * b x * (lb * lb)⁻¹ = lb * (lb * b x * lb⁻¹) * lb⁻¹ := by group
      _ = b (kleinFiveB *ᵥ (kleinFiveB *ᵥ x)) := by rw [hlbv, hlbv]
      _ = b x := by rw [Matrix.mulVec_mulVec, kleinFiveB_mul_self, Matrix.one_mulVec]
  have habab : la * lb * la * lb = 1 :=
    hrel _ (mul_mem (mul_mem (mul_mem hla hlb) hla) hlb) fun x => by
      calc la * lb * la * lb * b x * (la * lb * la * lb)⁻¹ =
          la * (lb * (la * (lb * b x * lb⁻¹) * la⁻¹) * lb⁻¹) * la⁻¹ := by group
        _ = b (kleinFiveA *ᵥ (kleinFiveB *ᵥ (kleinFiveA *ᵥ (kleinFiveB *ᵥ x)))) := by
          rw [hlbv, hlav, hlbv, hlav]
        _ = b x := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
            kleinFive_mul_mul_mul, Matrix.one_mulVec]
  have hla' : la⁻¹ = la := inv_eq_of_mul_eq_one_right haa
  have hlb' : lb⁻¹ = lb := inv_eq_of_mul_eq_one_right hbb
  have hab : la * lb = lb * la := by
    have h1 : (la * lb)⁻¹ = la * lb := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact habab)
    rw [_root_.mul_inv_rev, hla', hlb'] at h1
    exact h1.symm
  exact not_exists_lift_kleinFive (Φ.map_redFour_conjMat b hΦ (hL₁W hla) hlav)
    (Φ.map_redFour_conjMat b hΦ (hL₁W hlb) hlbv) (Φ.conjMat_mul_self (hL₁W hla) haa)
    (Φ.conjMat_mul_self (hL₁W hlb) hbb) (Φ.conjMat_comm (hL₁W hla) (hL₁W hlb) hab)

theorem linearTwoWOneAtInput_six_of (hmove : LinearTwoMovesTAtInput 6)
    (hX : WOneOfXCardInput 5) : LinearTwoWOneAtInput 6 :=
  linearTwoWOneAtInput_of (by norm_num) hmove hX homocyclicExclusionCardInput_five

end CFSG.SeitzReduction.LinearPilot
