module

public import CFSG.ClassicalInvolution.RouteD.TypeF4PatternEigen
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.ClassicalInvolution.WeakCT.AutExtend

public section

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.Sp (blockMat blockMat_injective blockMat_mul)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.ClassicalInvolution.WeakCT (diagConj2)
open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.RouteD.SpAdapt

variable {F : Type} [Field F]

@[expose] def pv (y : Fin 2 → F) : Fin 3 ⊕ Fin 3 → F := fun a =>
  if a = Sum.inl 2 then y 0 else if a = Sum.inr 2 then y 1 else 0

@[expose] def IsPV (v : Fin 3 ⊕ Fin 3 → F) : Prop := ∀ a, a ∉ coords (2 : Fin 3) → v a = 0

@[expose] def blk (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![M (Sum.inl 2) (Sum.inl 2), M (Sum.inl 2) (Sum.inr 2);
    M (Sum.inr 2) (Sum.inl 2), M (Sum.inr 2) (Sum.inr 2)]

theorem pv_inl (y : Fin 2 → F) : pv y (Sum.inl 2) = y 0 := by simp [pv]

theorem pv_inr (y : Fin 2 → F) : pv y (Sum.inr 2) = y 1 := by simp [pv]

theorem pv_of_not_mem (y : Fin 2 → F) {a : Fin 3 ⊕ Fin 3} (ha : a ∉ coords (2 : Fin 3)) :
    pv y a = 0 := by
  rw [mem_coords, not_or] at ha
  simp [pv, ha.1, ha.2]

theorem isPV_pv (y : Fin 2 → F) : IsPV (pv y) := fun _ ha => pv_of_not_mem y ha

theorem pv_injective : Function.Injective (pv (F := F)) := by
  intro x y h
  funext i
  fin_cases i
  · simpa [pv_inl] using congrFun h (Sum.inl 2)
  · simpa [pv_inr] using congrFun h (Sum.inr 2)

theorem eq_pv_of_isPV {v : Fin 3 ⊕ Fin 3 → F} (hv : IsPV v) :
    v = pv ![v (Sum.inl 2), v (Sum.inr 2)] := by
  funext a
  by_cases ha : a ∈ coords (2 : Fin 3)
  · rcases mem_coords.1 ha with rfl | rfl
    · simp [pv_inl]
    · simp [pv_inr]
  · rw [hv a ha, pv_of_not_mem _ ha]

theorem blockMat_mulVec_pv (S : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) :
    (blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3)) S :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ pv y = pv (S *ᵥ y) := by
  funext a
  rcases a with a | a <;> fin_cases a <;>
    simp [blockMat, pv, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply,
      Fin.sum_univ_two]

theorem blockMat_mulVec_of_Vfour (S : Matrix (Fin 2) (Fin 2) F) {u : Fin 3 ⊕ Fin 3 → F}
    (hu : u ∈ Vfour F) :
    (blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3)) S :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) *ᵥ u = u :=
  mulVec_eq_self_of_isSupp (isSupp_blockMat 2 S) (fun t ht => by
    rcases mem_coords.1 ht with rfl | rfl
    · exact hu.1
    · exact hu.2)

theorem mat2_eq_of_mulVec_eq {M N : Matrix (Fin 2) (Fin 2) F}
    (h : ∀ y : Fin 2 → F, M *ᵥ y = N *ᵥ y) : M = N := by
  have : Matrix.toLin' M = Matrix.toLin' N := LinearMap.ext h
  exact Matrix.toLin'.injective this

theorem mat6_eq_of_mulVec_eq {M N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F}
    (h : ∀ y : Fin 3 ⊕ Fin 3 → F, M *ᵥ y = N *ᵥ y) : M = N := by
  have : Matrix.toLin' M = Matrix.toLin' N := LinearMap.ext h
  exact Matrix.toLin'.injective this

theorem mulVec_pv_of_preserves {M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F}
    (hM : ∀ v, IsPV v → IsPV (M *ᵥ v)) (y : Fin 2 → F) :
    M *ᵥ pv y = pv (blk M *ᵥ y) := by
  refine (eq_pv_of_isPV (hM _ (isPV_pv y))).trans (congrArg pv ?_)
  funext i
  fin_cases i
  · show (M *ᵥ pv y) (Sum.inl 2) = _
    simp [blk, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, pv, Fin.sum_univ_two]
  · show (M *ᵥ pv y) (Sum.inr 2) = _
    simp [blk, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, pv, Fin.sum_univ_two]

theorem blk_mul_blk {Am Bm : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F} (hAB : Am * Bm = 1)
    (hA : ∀ v, IsPV v → IsPV (Am *ᵥ v)) (hB : ∀ v, IsPV v → IsPV (Bm *ᵥ v)) :
    blk Am * blk Bm = 1 := by
  refine mat2_eq_of_mulVec_eq fun y => ?_
  apply pv_injective
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← mulVec_pv_of_preserves hA,
    ← mulVec_pv_of_preserves hB, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]

theorem conj_blockMat {Am Bm : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F} (hAB : Am * Bm = 1)
    (hAP : ∀ v, IsPV v → IsPV (Am *ᵥ v)) (hBP : ∀ v, IsPV v → IsPV (Bm *ᵥ v))
    (hBV : ∀ v ∈ Vfour F, Bm *ᵥ v ∈ Vfour F) (S : Matrix (Fin 2) (Fin 2) F) :
    Am * blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3)) S * Bm =
      blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3)) (blk Am * S * blk Bm) := by
  refine mat6_eq_of_mulVec_eq fun v => ?_
  obtain ⟨y, w, hw, rfl⟩ : ∃ (y : Fin 2 → F) (w : Fin 3 ⊕ Fin 3 → F), w ∈ Vfour F ∧
      v = pv y + w := by
    refine ⟨![v (Sum.inl 2), v (Sum.inr 2)], v - pv ![v (Sum.inl 2), v (Sum.inr 2)], ?_, by abel⟩
    exact ⟨by simp [pv_inl], by simp [pv_inr]⟩
  have hBw := hBV w hw
  have e1 : (Am * blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3)) S * Bm) *ᵥ pv y =
      pv ((blk Am * S * blk Bm) *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_pv_of_preserves hBP,
      blockMat_mulVec_pv, mulVec_pv_of_preserves hAP, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have e2 : (Am * blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3)) S * Bm) *ᵥ w = w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, blockMat_mulVec_of_Vfour S hBw,
      Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, e1, e2, blockMat_mulVec_pv,
    blockMat_mulVec_of_Vfour _ hw]

theorem map_fin_two (σ : F ≃+* F) (a b c d : F) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F).map σ = !![σ a, σ b; σ c, σ d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem scalar_of_twisted {C : Matrix (Fin 2) (Fin 2) F} (hC : IsUnit C.det) (σ : F ≃+* F)
    (h : ∀ t : SL(2, F), C * (t : Matrix (Fin 2) (Fin 2) F).map σ =
      (t : Matrix (Fin 2) (Fin 2) F) * C) :
    (∀ x, σ x = x) ∧ ∃ a : F, a ≠ 0 ∧ C = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c00, c01, c10, c11, rfl⟩ : ∃ c00 c01 c10 c11 : F, C = !![c00, c01; c10, c11] :=
    ⟨C 0 0, C 0 1, C 1 0, C 1 1, Matrix.eta_fin_two C⟩
  have hup : ∀ x : F, c10 * x = 0 ∧ c00 * σ x = x * c11 := fun x => by
    have := h (sl2Upper x)
    rw [CFSG.LieType.Steinberg.coe_sl2Upper, map_fin_two] at this
    simp only [map_one, map_zero, Matrix.mul_fin_two] at this
    have e1 := congrFun (congrFun this 0) 0
    have e2 := congrFun (congrFun this 0) 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at e1 e2
    refine ⟨by linear_combination -e1, by linear_combination e2⟩
  have hlo : ∀ x : F, c01 * σ x = 0 := fun x => by
    have := h (sl2Lower x)
    rw [CFSG.LieType.Steinberg.coe_sl2Lower, map_fin_two] at this
    simp only [map_one, map_zero, Matrix.mul_fin_two] at this
    have e1 := congrFun (congrFun this 0) 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one] at e1
    linear_combination e1
  have h10 : c10 = 0 := by simpa using (hup 1).1
  have h01 : c01 = 0 := by simpa using hlo 1
  have h00 : c00 = c11 := by simpa using (hup 1).2
  have hdet : c00 * c11 ≠ 0 := by
    have := hC
    rw [Matrix.det_fin_two_of, h10, h01] at this
    simpa using this.ne_zero
  have hc0 : c00 ≠ 0 := left_ne_zero_of_mul hdet
  refine ⟨fun x => ?_, c00, hc0, ?_⟩
  · have := (hup x).2
    rw [← h00] at this
    have := mul_left_cancel₀ hc0 (this.trans (mul_comm x c00))
    exact this
  · rw [h10, h01, ← h00]
    ext i j
    fin_cases i <;> fin_cases j <;> simp


theorem diagConj2_coe_neg_one (s : SL(2, F)) :
    ((diagConj2 (-1) 1 s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(-1 : F), 1] * (s : Matrix (Fin 2) (Fin 2) F) *
        Matrix.diagonal ![(-1 : F), 1] := by
  rw [CFSG.ClassicalInvolution.WeakCT.coe_diagConj2]
  simp

theorem blockA2_shape [Finite F] {A₂ B₂ : Matrix (Fin 2) (Fin 2) F} (hAB : A₂ * B₂ = 1)
    (hBA : B₂ * A₂ = 1) (σ : F ≃+* F) (γ : SL(2, F) ≃* SL(2, F))
    (h : ∀ s : SL(2, F), A₂ * ((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ * B₂ =
        ((γ (diagConj2 (-1) 1 s) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) :
    (∀ x, σ x = x) ∧ ∃ a : F, a ≠ 0 ∧ A₂ * A₂ = a ^ 2 • (1 : Matrix (Fin 2) (Fin 2) F) ∧
      ∃ p r : Fin 2 → F, A₂ *ᵥ p = (-a) • p ∧ A₂ *ᵥ r = a • r ∧ p 0 * r 1 - p 1 * r 0 ≠ 0 := by
  obtain ⟨G, κ, hG⟩ := CFSG.ClassicalInvolution.Phan.exists_toGL_eq_conj_map γ
  set Gm : Matrix (Fin 2) (Fin 2) F := (G : Matrix (Fin 2) (Fin 2) F) with hGm
  set Gi : Matrix (Fin 2) (Fin 2) F := ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hGi
  have hGG : Gm * Gi = 1 := G.mul_inv
  have hGG' : Gi * Gm = 1 := G.inv_mul
  have hcoe : ∀ s : SL(2, F), ((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      Gm * (s : Matrix (Fin 2) (Fin 2) F).map κ * Gi := by
    intro s
    have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) (hG s)
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h2
    exact h2
  set Dm : Matrix (Fin 2) (Fin 2) F := Matrix.diagonal ![(-1 : F), 1] with hDm
  have hDD : Dm * Dm = 1 := by
    rw [hDm, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hDκ : Dm.map κ = Dm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hDm]
  have hmapσ : ∀ M N : Matrix (Fin 2) (Fin 2) F, (M * N).map σ = M.map σ * N.map σ :=
    fun M N => CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.map_mul_ringEquiv σ M N
  have hmapκ : ∀ M N : Matrix (Fin 2) (Fin 2) F, (M * N).map κ = M.map κ * N.map κ :=
    fun M N => CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.map_mul_ringEquiv κ M N
  have hone : ∀ τ : F ≃+* F, (1 : Matrix (Fin 2) (Fin 2) F).map τ = 1 := fun τ => by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  set Nm : Matrix (Fin 2) (Fin 2) F := A₂ * Gm.map σ with hNm
  set N' : Matrix (Fin 2) (Fin 2) F := Gi.map σ * B₂ with hN'
  have hNN : Nm * N' = 1 := by
    rw [hNm, hN', Matrix.mul_assoc, ← Matrix.mul_assoc (Gm.map σ), ← hmapσ, hGG, hone,
      Matrix.one_mul, hAB]
  have hNN' : N' * Nm = 1 := by
    rw [hNm, hN', Matrix.mul_assoc, ← Matrix.mul_assoc B₂, hBA, Matrix.one_mul, ← hmapσ, hGG',
      hone]
  set P : Matrix (Fin 2) (Fin 2) F := Gm * Dm with hP
  set P' : Matrix (Fin 2) (Fin 2) F := Dm * Gi with hP'
  have hPP : P * P' = 1 := by
    calc P * P' = Gm * (Dm * Dm) * Gi := by simp only [hP, hP', Matrix.mul_assoc]
      _ = 1 := by rw [hDD, Matrix.mul_one, hGG]
  have hPP' : P' * P = 1 := by
    calc P' * P = Dm * (Gi * Gm) * Dm := by simp only [hP, hP', Matrix.mul_assoc]
      _ = 1 := by rw [hGG', Matrix.mul_one, hDD]
  have hsurj : ∀ t : SL(2, F), ∃ s : SL(2, F),
      (s : Matrix (Fin 2) (Fin 2) F).map κ = (t : Matrix (Fin 2) (Fin 2) F) := by
    intro t
    refine ⟨Matrix.SpecialLinearGroup.map (κ.symm : F →+* F) t, ?_⟩
    ext i j
    simp
  have hmain : ∀ t : SL(2, F), Nm * (t : Matrix (Fin 2) (Fin 2) F).map σ * N' = P * t * P' := by
    intro t
    obtain ⟨s, hs⟩ := hsurj t
    have e := h s
    rw [hcoe s, hcoe (diagConj2 (-1) 1 s), diagConj2_coe_neg_one, hmapσ, hmapσ, hs] at e
    rw [hmapκ, hmapκ, hDκ, hs] at e
    rw [hNm, hN', hP, hP']
    calc A₂ * Gm.map σ * (t : Matrix (Fin 2) (Fin 2) F).map σ * (Gi.map σ * B₂)
        = A₂ * (Gm.map σ * (t : Matrix (Fin 2) (Fin 2) F).map σ * Gi.map σ) * B₂ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [e]; simp only [Matrix.mul_assoc]
  have hC : IsUnit (P' * Nm).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact IsUnit.mul ⟨⟨P', P, hPP', hPP⟩, rfl⟩ ⟨⟨Nm, N', hNN, hNN'⟩, rfl⟩
  have hcomm : ∀ t : SL(2, F),
      (P' * Nm) * (t : Matrix (Fin 2) (Fin 2) F).map σ =
        (t : Matrix (Fin 2) (Fin 2) F) * (P' * Nm) := by
    intro t
    have e := hmain t
    calc P' * Nm * (t : Matrix (Fin 2) (Fin 2) F).map σ
        = P' * (Nm * (t : Matrix (Fin 2) (Fin 2) F).map σ * N' * Nm) := by
          rw [Matrix.mul_assoc (Nm * (t : Matrix (Fin 2) (Fin 2) F).map σ) N' Nm, hNN',
            Matrix.mul_one, Matrix.mul_assoc]
      _ = P' * (P * t * P' * Nm) := by rw [e]
      _ = (t : Matrix (Fin 2) (Fin 2) F) * (P' * Nm) := by
          calc P' * (P * (t : Matrix (Fin 2) (Fin 2) F) * P' * Nm)
              = (P' * P) * (t : Matrix (Fin 2) (Fin 2) F) * (P' * Nm) := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [hPP', Matrix.one_mul]
  obtain ⟨hσ, a, ha, hCa⟩ := scalar_of_twisted hC σ hcomm
  refine ⟨hσ, a, ha, ?_⟩
  have hmapid : ∀ M : Matrix (Fin 2) (Fin 2) F, M.map σ = M := fun M => by
    ext i j
    simp [hσ]
  have hA₂ : A₂ = a • (Gm * Dm * Gi) := by
    have h1 : Dm * Gi * A₂ * Gm = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
      have := hCa
      rw [hNm, hmapid] at this
      simpa only [hP', Matrix.mul_assoc] using this
    have h2 : Gi * A₂ * Gm = a • Dm := by
      calc Gi * A₂ * Gm = (Dm * Dm) * (Gi * A₂ * Gm) := by rw [hDD, Matrix.one_mul]
        _ = Dm * (Dm * Gi * A₂ * Gm) := by simp only [Matrix.mul_assoc]
        _ = a • Dm := by rw [h1]; simp
    calc A₂ = (Gm * Gi) * A₂ * (Gm * Gi) := by rw [hGG, Matrix.one_mul, Matrix.mul_one]
      _ = Gm * (Gi * A₂ * Gm) * Gi := by simp only [Matrix.mul_assoc]
      _ = a • (Gm * Dm * Gi) := by
        rw [h2]
        simp [Matrix.mul_assoc]
  have hDe0 : Dm *ᵥ ![1, 0] = (-1 : F) • ![1, 0] := by
    ext i
    fin_cases i <;> simp [hDm, Matrix.mulVec_diagonal]
  have hDe1 : Dm *ᵥ ![0, 1] = (1 : F) • ![0, 1] := by
    ext i
    fin_cases i <;> simp [hDm, Matrix.mulVec_diagonal]
  have hAG : A₂ * Gm = a • (Gm * Dm) := by
    rw [hA₂, Matrix.smul_mul]
    congr 1
    calc Gm * Dm * Gi * Gm = Gm * Dm * (Gi * Gm) := by rw [Matrix.mul_assoc]
      _ = Gm * Dm := by rw [hGG', Matrix.mul_one]
  refine ⟨?_, Gm *ᵥ ![1, 0], Gm *ᵥ ![0, 1], ?_, ?_, ?_⟩
  · rw [hA₂]
    calc (a • (Gm * Dm * Gi)) * (a • (Gm * Dm * Gi)) = a ^ 2 • (Gm * (Dm * Dm) * Gi) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
          congr 1
          calc Gm * Dm * Gi * (Gm * Dm * Gi) = Gm * Dm * (Gi * Gm) * Dm * Gi := by
                simp only [Matrix.mul_assoc]
            _ = Gm * (Dm * Dm) * Gi := by rw [hGG', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = a ^ 2 • 1 := by rw [hDD, Matrix.mul_one, hGG]
  · rw [Matrix.mulVec_mulVec, hAG, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hDe0,
      Matrix.mulVec_smul, smul_smul, mul_neg_one]
  · rw [Matrix.mulVec_mulVec, hAG, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hDe1,
      Matrix.mulVec_smul, smul_smul, mul_one]
  · have hdet : Gm.det ≠ 0 := by
      have := (Matrix.isUnit_iff_isUnit_det Gm).1 ⟨⟨Gm, Gi, hGG, hGG'⟩, rfl⟩
      exact this.ne_zero
    rw [Matrix.det_fin_two] at hdet
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    intro hh
    apply hdet
    linear_combination hh


@[expose] def longInvMat (F : Type) [Field F] : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  Matrix.diagonal (fun a => if a ∈ coords (2 : Fin 3) then (-1 : F) else 1)

theorem commD_preserves (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F}
    (hM : M * longInvMat F = longInvMat F * M) :
    (∀ v, IsPV v → IsPV (M *ᵥ v)) ∧ (∀ v ∈ Vfour F, M *ᵥ v ∈ Vfour F) := by
  set D : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F := longInvMat F with hD
  have hDv : ∀ (v : Fin 3 ⊕ Fin 3 → F) (a : Fin 3 ⊕ Fin 3), (D *ᵥ v) a =
      (if a ∈ coords (2 : Fin 3) then (-1 : F) else 1) * v a := by
    intro v a
    simp [hD, longInvMat, Matrix.mulVec_diagonal]
  have hcomm : ∀ v : Fin 3 ⊕ Fin 3 → F, D *ᵥ (M *ᵥ v) = M *ᵥ (D *ᵥ v) := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hM]
  constructor
  · intro v hv a ha
    have h1 : D *ᵥ v = -v := by
      funext b
      rw [hDv]
      by_cases hb : b ∈ coords (2 : Fin 3)
      · simp [hb]
      · simp [hb, hv b hb]
    have h2' := congrFun (hcomm v) a
    rw [h1, hDv, Matrix.mulVec_neg] at h2'
    simp only [ha, ite_false, one_mul, Pi.neg_apply] at h2'
    have : (2 : F) * (M *ᵥ v) a = 0 := by linear_combination h2'
    exact (mul_eq_zero.1 this).resolve_left h2
  · intro v hv
    have h1 : D *ᵥ v = v := by
      funext b
      rw [hDv]
      by_cases hb : b ∈ coords (2 : Fin 3)
      · rcases mem_coords.1 hb with rfl | rfl
        · simp [hb, hv.1]
        · simp [hb, hv.2]
      · simp [hb]
    have key : ∀ a ∈ coords (2 : Fin 3), (M *ᵥ v) a = 0 := by
      intro a ha
      have h2' := congrFun (hcomm v) a
      rw [h1, hDv] at h2'
      simp only [ha, ite_true] at h2'
      have : (2 : F) * (M *ᵥ v) a = 0 := by linear_combination -h2'
      exact (mul_eq_zero.1 this).resolve_left h2
    exact ⟨key _ (by simp [mem_coords]), key _ (by simp [mem_coords])⟩

theorem pv_smul (c : F) (y : Fin 2 → F) : pv (c • y) = c • pv y := by
  funext a
  by_cases h1 : a = Sum.inl 2
  · subst h1; simp [pv_inl]
  · by_cases h2 : a = Sum.inr 2
    · subst h2; simp [pv_inr]
    · have : a ∉ coords (2 : Fin 3) := by simp [mem_coords, h1, h2]
      simp [pv_of_not_mem _ this]

theorem form_pv (y z : Fin 2 → F) : form (pv y) (pv z) = y 0 * z 1 - y 1 * z 0 := by
  rw [form_apply]
  simp [Fintype.sum_sum_type, sgn, par, pv]
  ring

theorem core_three [Finite F] (h2 : (2 : F) ≠ 0)
    {Am Bm : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F}
    (hAB : Am * Bm = 1) (hBA : Bm * Am = 1) (σ : F ≃+* F) {m : F}
    (hsim : ∀ u v, form (Am *ᵥ u) (Am *ᵥ v) = m * form u v)
    (hD : Am * longInvMat F = longInvMat F * Am)
    (hsq : ∃ d : F, Am * Am.map σ = d • (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F))
    (γ : SL(2, F) ≃* SL(2, F))
    (hγm : ∀ s : SL(2, F), Am * blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3))
        (((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ) * Bm =
      blockMat (Sum.inl (2 : Fin 3)) (Sum.inr (2 : Fin 3))
        ((γ (diagConj2 (-1) 1 s) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) :
    (∀ x, σ x = x) ∧ ∃ κ : F, EigData Am κ ∧ (∀ v ∈ Vfour F, Am *ᵥ v ∈ Vfour F) ∧
      ∃ u₂ w₂ : Fin 3 ⊕ Fin 3 → F, IsPV u₂ ∧ IsPV w₂ ∧ Am *ᵥ u₂ = κ • u₂ ∧
        Am *ᵥ w₂ = (-κ) • w₂ ∧ form u₂ w₂ = 1 := by
  classical
  set D : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F := longInvMat F with hDdef
  have hBD : Bm * D = D * Bm := by
    calc Bm * D = Bm * D * (Am * Bm) := by rw [hAB, Matrix.mul_one]
      _ = Bm * (D * Am) * Bm := by simp only [Matrix.mul_assoc]
      _ = Bm * (Am * D) * Bm := by rw [hD]
      _ = (Bm * Am) * D * Bm := by simp only [Matrix.mul_assoc]
      _ = D * Bm := by rw [hBA, Matrix.one_mul]
  obtain ⟨hAP, hAV⟩ := commD_preserves h2 hD
  obtain ⟨hBP, hBV⟩ := commD_preserves h2 hBD
  have hblk := blk_mul_blk hAB hAP hBP
  have hblk' := blk_mul_blk hBA hBP hAP
  have hrel : ∀ s : SL(2, F), blk Am * ((γ s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).map σ *
      blk Bm = ((γ (diagConj2 (-1) 1 s) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := fun s =>
    blockMat_injective Sum.inl_ne_inr (by rw [← conj_blockMat hAB hAP hBP hBV, hγm s])
  obtain ⟨hσ, a, ha, hasq, p, r, hp, hr, hdet⟩ := blockA2_shape hblk hblk' σ γ hrel
  have hmap : Am.map σ = Am := by
    ext i j
    simp [hσ]
  obtain ⟨d, hd⟩ := hsq
  rw [hmap] at hd
  have hda : d = a ^ 2 := by
    have h1 : (Am * Am) *ᵥ pv ![1, 0] = d • pv ![1, 0] := by rw [hd, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, mulVec_pv_of_preserves hAP, mulVec_pv_of_preserves hAP,
      Matrix.mulVec_mulVec, hasq, ← pv_smul] at h1
    have h2' := pv_injective h1
    have := congrFun h2' 0
    simpa using this.symm
  have hsq' : Am * Am = (a ^ 2) • (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
    rw [hd, hda]
  have hAp : Am *ᵥ pv p = (-a) • pv p := by
    rw [mulVec_pv_of_preserves hAP, hp, pv_smul]
  have hAr : Am *ᵥ pv r = a • pv r := by
    rw [mulVec_pv_of_preserves hAP, hr, pv_smul]
  have hform : form (pv r) (pv p) ≠ 0 := by
    rw [form_pv]
    intro h0
    apply hdet
    linear_combination -h0
  have hm : m = -a ^ 2 := by
    have h1 := hsim (pv r) (pv p)
    rw [hAr, hAp, form_smul_left, form_smul_right] at h1
    have h3 : (m + a ^ 2) * form (pv r) (pv p) = 0 := by linear_combination -h1
    have := (mul_eq_zero.1 h3).resolve_right hform
    linear_combination this
  refine ⟨hσ, a, ⟨h2, ha, hsq', fun u v => by rw [hsim, hm]⟩, hAV, pv r,
    (form (pv r) (pv p))⁻¹ • pv p, isPV_pv r, ?_, hAr, ?_, ?_⟩
  · intro b hb
    simp [pv_of_not_mem p hb]
  · rw [Matrix.mulVec_smul, hAp, smul_comm]
  · rw [form_smul_right, inv_mul_cancel₀ hform]

end CFSG.ClassicalInvolution.RouteD.SpAdapt
