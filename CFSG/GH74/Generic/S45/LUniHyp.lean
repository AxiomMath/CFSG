module

public import CFSG.GH74.Generic.S45.LUniFix
public import CFSG.GH74.Generic.S45.LUniSymp

public section

namespace CFSG.GH74.Generic.S45.Uni

open Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p s : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p s K) {n : ℕ}

@[expose] noncomputable def outerVec (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => x i * h.bar (y j)

theorem outerVec_mulVec (x y z : Fin n → K) :
    outerVec h x y *ᵥ z = stdHermForm h n y z • x := by
  funext i
  simp only [outerVec, mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul, stdHermForm_apply]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

section Hyp

variable {Ep Em : Matrix (Fin n) (Fin n) K}
  (hswap : ∀ z w, stdHermForm h n (Ep *ᵥ z) w = stdHermForm h n z (Em *ᵥ w))

include hswap

theorem swap_right (a b : Fin n → K) :
    stdHermForm h n a (Ep *ᵥ b) = stdHermForm h n (Em *ᵥ a) b := by
  rw [hh_comm h (Ep *ᵥ b) a, hswap b a, ← hh_comm h b (Em *ᵥ a)]

theorem exists_eig_hyp_pair (hEp2 : Ep * Ep = Ep) (hEm2 : Em * Em = Em) (hne : Ep ≠ 0) :
    ∃ e f : Fin n → K, Ep *ᵥ e = e ∧ Em *ᵥ f = f ∧ stdHermForm h n e f = 1 := by
  have hEpp : ∀ v, Ep *ᵥ (Ep *ᵥ v) = Ep *ᵥ v := fun v => by rw [mulVec_mulVec, hEp2]
  have hEmm : ∀ v, Em *ᵥ (Em *ᵥ v) = Em *ᵥ v := fun v => by rw [mulVec_mulVec, hEm2]
  have : ∃ z, Ep *ᵥ z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (matrix_ext_mulVec fun z => by rw [hcon z, zero_mulVec])
  obtain ⟨z, hz⟩ := this
  set e := Ep *ᵥ z with he
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hz (funext hcon)
  have hw : stdHermForm h n e (Pi.single i 1) ≠ 0 := by
    rw [hh_single_right]
    simpa using hi
  set f₀ := Em *ᵥ (Pi.single i 1 : Fin n → K) with hf₀
  have hef₀ : stdHermForm h n e f₀ = stdHermForm h n e (Pi.single i 1) := by
    rw [hf₀, ← hswap e, he, hEpp z]
  have hne0 : stdHermForm h n e f₀ ≠ 0 := by rw [hef₀]; exact hw
  refine ⟨e, (stdHermForm h n e f₀)⁻¹ • f₀, hEpp z, ?_, ?_⟩
  · rw [mulVec_smul, hf₀, hEmm]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne0]

theorem sub_orth_f {e f : Fin n → K} (hff : Em *ᵥ f = f) (hef : stdHermForm h n e f = 1)
    (z : Fin n → K) : stdHermForm h n f ((Ep - outerVec h e f) *ᵥ z) = 0 := by
  have hfe : stdHermForm h n f e = 1 := by rw [hh_comm h e f, hef, map_one]
  have h1 : stdHermForm h n f (Ep *ᵥ z) = stdHermForm h n f z := by
    rw [swap_right h hswap, hff]
  rw [sub_mulVec, outerVec_mulVec, map_sub, map_smul, h1, hfe, smul_eq_mul, mul_one, sub_self]

theorem sub_orth_e {e f : Fin n → K} (hee : Ep *ᵥ e = e) (hef : stdHermForm h n e f = 1)
    (z : Fin n → K) : stdHermForm h n e ((Em - outerVec h f e) *ᵥ z) = 0 := by
  have h1 : stdHermForm h n e (Em *ᵥ z) = stdHermForm h n e z := by
    rw [← hswap e z, hee]
  rw [sub_mulVec, outerVec_mulVec, map_sub, map_smul, h1, hef, smul_eq_mul, mul_one, sub_self]

theorem sub_swap {e f : Fin n → K} (z w : Fin n → K) :
    stdHermForm h n ((Ep - outerVec h e f) *ᵥ z) w =
      stdHermForm h n z ((Em - outerVec h f e) *ᵥ w) := by
  rw [sub_mulVec, sub_mulVec, outerVec_mulVec, outerVec_mulVec]
  simp only [map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, hswap]
  rw [hh_comm h f z]
  ring

theorem sub_idem_p {e f : Fin n → K} (hEp2 : Ep * Ep = Ep) (hee : Ep *ᵥ e = e)
    (hff : Em *ᵥ f = f) (hef : stdHermForm h n e f = 1) :
    (Ep - outerVec h e f) * (Ep - outerVec h e f) = Ep - outerVec h e f := by
  apply matrix_ext_mulVec
  intro z
  have h0 := sub_orth_f h hswap hff hef z
  rw [← mulVec_mulVec, sub_mulVec Ep (outerVec h e f) ((Ep - outerVec h e f) *ᵥ z),
    outerVec_mulVec, h0, zero_smul, sub_zero, sub_mulVec Ep (outerVec h e f) z, outerVec_mulVec,
    mulVec_sub, mulVec_smul, hee, mulVec_mulVec, hEp2]

theorem sub_idem_m {e f : Fin n → K} (hEm2 : Em * Em = Em) (hee : Ep *ᵥ e = e)
    (hff : Em *ᵥ f = f) (hef : stdHermForm h n e f = 1) :
    (Em - outerVec h f e) * (Em - outerVec h f e) = Em - outerVec h f e := by
  apply matrix_ext_mulVec
  intro z
  have h0 := sub_orth_e h hswap hee hef z
  rw [← mulVec_mulVec, sub_mulVec Em (outerVec h f e) ((Em - outerVec h f e) *ᵥ z),
    outerVec_mulVec, h0, zero_smul, sub_zero, sub_mulVec Em (outerVec h f e) z, outerVec_mulVec,
    mulVec_sub, mulVec_smul, hff, mulVec_mulVec, hEm2]

theorem sub_ne_zero (hn : 3 ≤ n) {e f : Fin n → K} (hsum : ∀ z, Ep *ᵥ z + Em *ᵥ z = z) :
    Ep - outerVec h e f ≠ 0 := by
  intro h0
  have hEp : ∀ z, Ep *ᵥ z = stdHermForm h n f z • e := by
    intro z
    have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ z) h0
    simp only [sub_mulVec, outerVec_mulVec, zero_mulVec] at this
    exact sub_eq_zero.1 this
  have hEm : ∀ w, Em *ᵥ w = stdHermForm h n e w • f := by
    intro w
    have h1 : (Em - outerVec h f e) *ᵥ w = 0 := by
      apply eq_zero_of_hh_zero h
      intro z
      rw [← sub_swap h hswap z w, h0, zero_mulVec, map_zero, LinearMap.zero_apply]
    have := h1
    rw [sub_mulVec, outerVec_mulVec] at this
    exact sub_eq_zero.1 this
  obtain ⟨w, hw0, hw1, hw2⟩ := exists_orth_pair h hn e f
  apply hw0
  rw [← hsum w, hEp, hEm, hw1, hw2]
  simp

theorem exists_hyp_frame (hn : 3 ≤ n) (hEp2 : Ep * Ep = Ep) (hEm2 : Em * Em = Em)
    (hsum : ∀ z, Ep *ᵥ z + Em *ᵥ z = z) (hEpEm : ∀ z, Ep *ᵥ (Em *ᵥ z) = 0)
    (hEmEp : ∀ z, Em *ᵥ (Ep *ᵥ z) = 0) (hne : Ep ≠ 0) :
    ∃ e f e₂ f₂ : Fin n → K, Ep *ᵥ e = e ∧ Em *ᵥ f = f ∧ Ep *ᵥ e₂ = e₂ ∧ Em *ᵥ f₂ = f₂ ∧
      stdHermForm h n e f = 1 ∧ stdHermForm h n e₂ f₂ = 1 ∧ stdHermForm h n e e = 0 ∧
      stdHermForm h n f f = 0 ∧ stdHermForm h n e₂ e₂ = 0 ∧ stdHermForm h n f₂ f₂ = 0 ∧
      stdHermForm h n e e₂ = 0 ∧ stdHermForm h n f f₂ = 0 ∧ stdHermForm h n e f₂ = 0 ∧
      stdHermForm h n f e₂ = 0 := by
  obtain ⟨e, f, hee, hff, hef⟩ := exists_eig_hyp_pair h hswap hEp2 hEm2 hne
  have hswap₂ := sub_swap h hswap (e := e) (f := f)
  have hEp₂2 := sub_idem_p h hswap hEp2 hee hff hef
  have hEm₂2 := sub_idem_m h hswap hEm2 hee hff hef
  have hne₂ : Ep - outerVec h e f ≠ 0 := sub_ne_zero h hswap hn hsum
  obtain ⟨e₂, f₂, hee₂, hff₂, hef₂⟩ := exists_eig_hyp_pair h hswap₂ hEp₂2 hEm₂2 hne₂
  have R1 : stdHermForm h n f e₂ = 0 := by
    have := sub_orth_f h hswap hff hef e₂
    rwa [hee₂] at this
  have R2 : stdHermForm h n e f₂ = 0 := by
    have := sub_orth_e h hswap hee hef f₂
    rwa [hff₂] at this
  have R3 : Ep *ᵥ e₂ = e₂ := by
    have := hee₂
    rw [sub_mulVec, outerVec_mulVec, R1, zero_smul, sub_zero] at this
    exact this
  have R3' : Em *ᵥ f₂ = f₂ := by
    have := hff₂
    rw [sub_mulVec, outerVec_mulVec, R2, zero_smul, sub_zero] at this
    exact this
  have hEme : Em *ᵥ e = 0 := by
    have := hEmEp e
    rwa [hee] at this
  have hEpf : Ep *ᵥ f = 0 := by
    have := hEpEm f
    rwa [hff] at this
  have hEme₂ : Em *ᵥ e₂ = 0 := by
    have := hEmEp e₂
    rwa [R3] at this
  have hEpf₂ : Ep *ᵥ f₂ = 0 := by
    have := hEpEm f₂
    rwa [R3'] at this
  refine ⟨e, f, e₂, f₂, hee, hff, R3, R3', hef, hef₂, ?_, ?_, ?_, ?_, ?_, ?_, R2, R1⟩
  ·
    have := hswap e e
    rwa [hee, hEme, map_zero] at this
  · have := hswap f f
    rw [hEpf, hff, map_zero, LinearMap.zero_apply] at this
    exact this.symm
  · have := hswap e₂ e₂
    rwa [R3, hEme₂, map_zero] at this
  · have := hswap f₂ f₂
    rw [hEpf₂, R3', map_zero, LinearMap.zero_apply] at this
    exact this.symm
  · have := swap_right h hswap e e₂
    rw [R3, hEme, map_zero, LinearMap.zero_apply] at this
    exact this
  · have := hswap f f₂
    rw [hEpf, R3', map_zero, LinearMap.zero_apply] at this
    exact this.symm

end Hyp

section Frame

@[expose] noncomputable def frameMat (e e₂ g g₂ : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => ![e i, e₂ i, g i, g₂ i] j

@[expose] def frameGram : Matrix (Fin 4) (Fin 4) K := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem frameGram_mul_self : (frameGram : Matrix (Fin 4) (Fin 4) K) * frameGram = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frameGram, Matrix.mul_apply, Fin.sum_univ_four]

theorem frameGram_star : ((frameGram : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ = frameGram := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frameGram]

theorem frameMat_star_mul {e e₂ g g₂ : Fin 4 → K}
    (hef : stdHermForm h 4 e g = 1) (hef₂ : stdHermForm h 4 e₂ g₂ = 1)
    (hee : stdHermForm h 4 e e = 0) (hgg : stdHermForm h 4 g g = 0)
    (hee₂ : stdHermForm h 4 e₂ e₂ = 0) (hgg₂ : stdHermForm h 4 g₂ g₂ = 0)
    (hee' : stdHermForm h 4 e e₂ = 0) (hgg' : stdHermForm h 4 g g₂ = 0)
    (heg₂ : stdHermForm h 4 e g₂ = 0) (hge₂ : stdHermForm h 4 g e₂ = 0) :
    ((frameMat e e₂ g g₂).map h.bar)ᵀ * frameMat e e₂ g g₂ = frameGram := by
  have hc : ∀ x y : Fin 4 → K, stdHermForm h 4 y x = h.bar (stdHermForm h 4 x y) :=
    fun x y => hh_comm h x y
  have key : ∀ i j : Fin 4, (((frameMat e e₂ g g₂).map h.bar)ᵀ * frameMat e e₂ g g₂) i j =
      stdHermForm h 4 (fun k => frameMat e e₂ g g₂ k i) (fun k => frameMat e e₂ g g₂ k j) := by
    intro i j
    simp [Matrix.mul_apply, stdHermForm_apply]
  have h1 : stdHermForm h 4 e₂ e = 0 := by rw [hc e e₂, hee', map_zero]
  have h2 : stdHermForm h 4 e₂ g = 0 := by rw [hc g e₂, hge₂, map_zero]
  have h3 : stdHermForm h 4 g e = 1 := by rw [hc e g, hef, map_one]
  have h4 : stdHermForm h 4 g₂ e = 0 := by rw [hc e g₂, heg₂, map_zero]
  have h5 : stdHermForm h 4 g₂ e₂ = 1 := by rw [hc e₂ g₂, hef₂, map_one]
  have h6 : stdHermForm h 4 g₂ g = 0 := by rw [hc g g₂, hgg', map_zero]
  ext i j
  rw [key]
  fin_cases i <;> fin_cases j <;> simp [frameMat, frameGram, hef, hef₂, hee, hgg, hee₂, hgg₂, hee',
    hgg', heg₂, hge₂, h1, h2, h3, h4, h5, h6]

@[expose] noncomputable def frameDiag (α : K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![α, α⁻¹, h.bar α⁻¹, h.bar α]

theorem frameDiag_unitary {α : K} (hα0 : α ≠ 0) :
    frameGram * ((frameDiag h α).map h.bar)ᵀ * frameGram * frameDiag h α = 1 := by
  have hbα0 : h.bar α ≠ 0 := by simpa [h.bar_eq_zero_iff] using hα0
  have e1 : ((frameDiag h α).map h.bar)ᵀ =
      Matrix.diagonal ![h.bar α, h.bar α⁻¹, α⁻¹, α] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frameDiag, h.bar_bar]
  have e2 : ∀ x : Fin 4 → K, (frameGram : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal x * frameGram =
      Matrix.diagonal ![x 2, x 3, x 0, x 1] := by
    intro x
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [frameGram, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul_diagonal]
  rw [e1, e2]
  simp only [frameDiag, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hα0, hbα0]

theorem class1b_of_frame (h2 : (2 : K) ≠ 0) {α : K} (hα4 : α ^ 4 = -1)
    {A : Matrix (Fin 4) (Fin 4) K} {l : K} {e e₂ g g₂ : Fin 4 → K}
    (hef : stdHermForm h 4 e g = 1) (hef₂ : stdHermForm h 4 e₂ g₂ = 1)
    (hee : stdHermForm h 4 e e = 0) (hgg : stdHermForm h 4 g g = 0)
    (hee₂ : stdHermForm h 4 e₂ e₂ = 0) (hgg₂ : stdHermForm h 4 g₂ g₂ = 0)
    (hee' : stdHermForm h 4 e e₂ = 0) (hgg' : stdHermForm h 4 g g₂ = 0)
    (heg₂ : stdHermForm h 4 e g₂ = 0) (hge₂ : stdHermForm h 4 g e₂ = 0)
    (hAe : A *ᵥ e = l • e) (hAe₂ : A *ᵥ e₂ = l • e₂) (hAg : A *ᵥ g = (-l) • g)
    (hAg₂ : A *ᵥ g₂ = (-l) • g₂) :
    ∃ c : Matrix (Fin 4) (Fin 4) K, (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧
      (∀ l' : K, c * c ≠ l' • 1) ∧ c * c * (c * c) = -1 ∧ A * c = c * A := by
  set P := frameMat e e₂ g g₂ with hP
  set G : Matrix (Fin 4) (Fin 4) K := frameGram with hG
  have hPP : (P.map h.bar)ᵀ * P = G :=
    frameMat_star_mul h hef hef₂ hee hgg hee₂ hgg₂ hee' hgg' heg₂ hge₂
  have hGG : G * G = 1 := frameGram_mul_self
  set Q : Matrix (Fin 4) (Fin 4) K := G * (P.map h.bar)ᵀ with hQ
  have hQP : Q * P = 1 := by
    rw [hQ, Matrix.mul_assoc, hPP, hGG]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hα4
    exact one_ne_zero (by linear_combination hα4 : (1 : K) = 0)
  have hbα0 : h.bar α ≠ 0 := by simpa [h.bar_eq_zero_iff] using hα0
  set D := frameDiag h α with hD
  have hDG : G * (D.map h.bar)ᵀ * G * D = 1 := frameDiag_unitary h hα0
  have hGstar : (G.map h.bar)ᵀ = G := frameGram_star h
  have hbα4 : (h.bar α) ^ 4 = -1 := by rw [← map_pow, hα4, map_neg, map_one]
  have hinv4 : ∀ x : K, x * x * (x * x) = -1 → x⁻¹ * x⁻¹ * (x⁻¹ * x⁻¹) = -1 := by
    intro x hx
    calc x⁻¹ * x⁻¹ * (x⁻¹ * x⁻¹) = (x * x * (x * x))⁻¹ := by simp
      _ = -1 := by rw [hx]; simp
  have hD4 : D * D * (D * D) = -1 := by
    rw [hD, frameDiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.neg_apply]
    · linear_combination hα4
    · exact hinv4 α (by linear_combination hα4)
    · exact hinv4 (h.bar α) (by linear_combination hbα4)
    · linear_combination hbα4
  refine ⟨P * D * Q, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hQstar : (Q.map h.bar)ᵀ = P * G := by
      rw [hQ, Matrix.map_mul, transpose_mul, ustar_ustar h P, hGstar]
    have e : ((P * D * Q).map h.bar)ᵀ = P * G * (D.map h.bar)ᵀ * (P.map h.bar)ᵀ := by
      rw [Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul, hQstar]
      simp only [Matrix.mul_assoc]
    rw [e]
    calc P * G * (D.map h.bar)ᵀ * (P.map h.bar)ᵀ * (P * D * Q) =
        P * (G * (D.map h.bar)ᵀ * ((P.map h.bar)ᵀ * P) * D) * Q := by
          simp only [Matrix.mul_assoc]
      _ = P * (G * (D.map h.bar)ᵀ * G * D) * Q := by rw [hPP]
      _ = 1 := by rw [hDG, Matrix.mul_one, hPQ]
  ·
    have hdD : D.det = 1 := by
      simp [hD, frameDiag, Matrix.det_diagonal, Fin.prod_univ_four, hα0, hbα0]
    have hdPQ : P.det * Q.det = 1 := by rw [← det_mul, hPQ, det_one]
    rw [det_mul, det_mul, hdD]
    linear_combination hdPQ
  ·
    intro l' hl
    have hcc : P * D * Q * (P * D * Q) = P * (D * D) * Q := by
      calc P * D * Q * (P * D * Q) = P * D * (Q * P) * D * Q := by simp only [Matrix.mul_assoc]
        _ = P * (D * D) * Q := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P D D]
    have hDD : D * D = l' • 1 := by
      calc D * D = (Q * P) * (D * D) * (Q * P) := by rw [hQP, Matrix.one_mul, Matrix.mul_one]
        _ = Q * (P * (D * D) * Q) * P := by simp only [Matrix.mul_assoc]
        _ = Q * (P * D * Q * (P * D * Q)) * P := by rw [hcc]
        _ = l' • 1 := by rw [hl, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQP]
    have h00 := congrFun (congrFun hDD 0) 0
    have h11 := congrFun (congrFun hDD 1) 1
    simp [hD, frameDiag] at h00 h11
    have hee : α⁻¹ * α⁻¹ = α * α := h11.trans h00.symm
    have h4 : α * α * (α * α) = 1 := by
      calc α * α * (α * α) = (α * α) * (α⁻¹ * α⁻¹) := by rw [hee]
        _ = 1 := by field_simp
    exact h2 (by linear_combination hα4 - h4)
  ·
    have hcc : P * D * Q * (P * D * Q) = P * (D * D) * Q := by
      calc P * D * Q * (P * D * Q) = P * D * (Q * P) * D * Q := by simp only [Matrix.mul_assoc]
        _ = P * (D * D) * Q := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P D D]
    calc P * D * Q * (P * D * Q) * (P * D * Q * (P * D * Q)) =
        P * (D * D) * Q * (P * (D * D) * Q) := by rw [hcc]
      _ = P * ((D * D) * (Q * P) * (D * D)) * Q := by simp only [Matrix.mul_assoc]
      _ = P * (D * D * (D * D)) * Q := by rw [hQP, Matrix.mul_one]
      _ = -1 := by rw [hD4, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hPQ]
  ·
    have hAP : A * P = P * Matrix.diagonal ![l, l, -l, -l] := by
      ext i j
      rw [Matrix.mul_diagonal]
      fin_cases j
      · have := congrFun hAe i
        simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
        simpa [hP, frameMat, Matrix.mul_apply, mul_comm] using this
      · have := congrFun hAe₂ i
        simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
        simpa [hP, frameMat, Matrix.mul_apply, mul_comm] using this
      · have := congrFun hAg i
        simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
        simpa [hP, frameMat, Matrix.mul_apply, mul_comm] using this
      · have := congrFun hAg₂ i
        simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
        simpa [hP, frameMat, Matrix.mul_apply, mul_comm] using this
    have hA : A = P * Matrix.diagonal ![l, l, -l, -l] * Q := by
      calc A = A * (P * Q) := by rw [hPQ, Matrix.mul_one]
        _ = (A * P) * Q := by rw [Matrix.mul_assoc]
        _ = P * Matrix.diagonal ![l, l, -l, -l] * Q := by rw [hAP]
    have hΛD : Matrix.diagonal ![l, l, -l, -l] * D = D * Matrix.diagonal ![l, l, -l, -l] := by
      rw [hD, frameDiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    rw [hA]
    calc P * Matrix.diagonal ![l, l, -l, -l] * Q * (P * D * Q) =
        P * (Matrix.diagonal ![l, l, -l, -l] * D) * Q := by
          rw [show P * Matrix.diagonal ![l, l, -l, -l] * Q * (P * D * Q) =
            P * Matrix.diagonal ![l, l, -l, -l] * (Q * P) * D * Q by simp only [Matrix.mul_assoc],
            hQP, Matrix.mul_one, Matrix.mul_assoc P (Matrix.diagonal ![l, l, -l, -l]) D]
      _ = P * (D * Matrix.diagonal ![l, l, -l, -l]) * Q := by rw [hΛD]
      _ = P * D * Q * (P * Matrix.diagonal ![l, l, -l, -l] * Q) := by
          rw [show P * D * Q * (P * Matrix.diagonal ![l, l, -l, -l] * Q) =
            P * D * (Q * P) * Matrix.diagonal ![l, l, -l, -l] * Q by simp only [Matrix.mul_assoc],
            hQP, Matrix.mul_one, Matrix.mul_assoc P D (Matrix.diagonal ![l, l, -l, -l])]

include h in
theorem exists_pow_four_eq_neg_one (hp : p ≠ 2) : ∃ a : K, a ^ 4 = -1 := by
  classical
  have : Finite K := h.finite
  have hodd : Odd (p ^ s) := (h.prime.odd_of_ne_two hp).pow
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ s) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, h.card_eq_sq]
  have h8 : 8 ∣ orderOf g := by
    rw [hord]
    obtain ⟨m, hm⟩ := hodd
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self m
    refine ⟨r, ?_⟩
    rw [hm]
    have : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  have hne : orderOf g ≠ 0 := by
    rw [hord]
    have : 1 < (p ^ s) ^ 2 := by
      have := h.one_lt_pow
      nlinarith
    omega
  have ho8 : orderOf (g ^ (orderOf g / 8)) = 8 := orderOf_pow_orderOf_div hne h8
  set a : Kˣ := g ^ (orderOf g / 8) with ha
  have h4ne : a ^ 4 ≠ 1 := by
    intro h4
    have := orderOf_dvd_of_pow_eq_one h4
    rw [ho8] at this
    omega
  have h4sq : (a ^ 4) ^ 2 = 1 := by
    rw [← pow_mul]
    have h8' := pow_orderOf_eq_one a
    rw [ho8] at h8'
    exact h8'
  refine ⟨(a : K), ?_⟩
  have h4K : ((a : K) ^ 4) * ((a : K) ^ 4) = 1 := by
    have := congrArg (fun x : Kˣ => (x : K)) h4sq
    simpa [sq] using this
  rcases mul_self_eq_one_iff.1 h4K with h1 | h1
  · exact absurd (Units.ext (by simpa using h1)) h4ne
  · exact h1

end Frame

section Assembly

theorem fixed_class1b_four (hp : p ≠ 2) (A : Matrix (Fin 4) (Fin 4) K) (l : K)
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A = (l * l) • 1) (hN : h.bar l * l = -1) :
    FixConcl h 4 A id := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_ne h hp
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hN
    exact one_ne_zero (by linear_combination hN : (1 : K) = 0)
  set S : Matrix (Fin 4) (Fin 4) K := l⁻¹ • A with hS
  have hAS : A = l • S := by rw [hS, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  have hSS : S * S = 1 := by
    rw [hS, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAA, smul_smul]
    have : l⁻¹ * l⁻¹ * (l * l) = 1 := by field_simp
    rw [this, one_smul]
  have hAstar : (A.map h.bar)ᵀ = (l * l)⁻¹ • A := by
    have e : (A.map h.bar)ᵀ * (A * A) = (l * l) • (A.map h.bar)ᵀ := by
      rw [hAA, Matrix.mul_smul, Matrix.mul_one]
    have e' : (A.map h.bar)ᵀ * (A * A) = A := by
      rw [← Matrix.mul_assoc, hAu, Matrix.one_mul]
    have hll : l * l ≠ 0 := mul_ne_zero hl0 hl0
    calc (A.map h.bar)ᵀ = (l * l)⁻¹ • ((l * l) • (A.map h.bar)ᵀ) := by
          rw [smul_smul, inv_mul_cancel₀ hll, one_smul]
      _ = (l * l)⁻¹ • A := by rw [← e, e']
  have hbl : h.bar l⁻¹ = -l := by
    have h1 : h.bar l = -l⁻¹ := by
      calc h.bar l = h.bar l * l * l⁻¹ := by field_simp
        _ = -1 * l⁻¹ := by rw [hN]
        _ = -l⁻¹ := by ring
    rw [map_inv₀, h1, inv_neg, inv_inv]
  have hSstar : (S.map h.bar)ᵀ = -S := by
    rw [hS, ustar_smul h, hbl, hAstar, smul_smul]
    have : -l * (l * l)⁻¹ = -l⁻¹ := by field_simp
    rw [this, neg_smul]
  have hSa : ∀ z w, stdHermForm h 4 (S *ᵥ z) w = -stdHermForm h 4 z (S *ᵥ w) := by
    intro z w
    rw [hh_mulVec_left h, hSstar, Matrix.neg_mulVec, map_neg]
  have hswap : ∀ z w, stdHermForm h 4 (eigProj S 1 *ᵥ z) w =
      stdHermForm h 4 z (eigProj S (-1) *ᵥ w) := by
    intro z w
    have h2b : h.bar ((2 : K)⁻¹) = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
    rw [eigProj_mulVec, eigProj_mulVec]
    simp only [map_smulₛₗ, map_add, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, h2b,
      hSa, RingHom.id_apply, map_neg, one_smul, neg_smul]
  have hSz : ∀ z, S *ᵥ (S *ᵥ z) = z := fun z => by rw [mulVec_mulVec, hSS, one_mulVec]
  have hEp2 := eigProj_idem h2 (by norm_num : (1 : K) * 1 = 1) hSS
  have hEm2 := eigProj_idem h2 (by norm_num : (-1 : K) * -1 = 1) hSS
  have hsum : ∀ z, eigProj S 1 *ᵥ z + eigProj S (-1) *ᵥ z = z := by
    intro z
    rw [eigProj_mulVec, eigProj_mulVec, ← smul_add]
    have e : (z + (1 : K) • S *ᵥ z) + (z + (-1 : K) • S *ᵥ z) = (2 : K) • z := by module
    rw [e, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hEpEm : ∀ z, eigProj S 1 *ᵥ (eigProj S (-1) *ᵥ z) = 0 := by
    intro z
    simp only [eigProj_mulVec, mulVec_smul, mulVec_add, hSz]
    module
  have hEmEp : ∀ z, eigProj S (-1) *ᵥ (eigProj S 1 *ᵥ z) = 0 := by
    intro z
    simp only [eigProj_mulVec, mulVec_smul, mulVec_add, hSz]
    module
  have hne : eigProj S 1 ≠ 0 := by
    intro h0
    have h1 : (1 : Matrix (Fin 4) (Fin 4) K) + S = 0 := by
      have := congrArg (fun M => (2 : K) • M) h0
      simp only [eigProj, smul_smul, mul_inv_cancel₀ h2, one_smul, smul_zero] at this
      exact this
    have hSneg : S = -1 := eq_neg_of_add_eq_zero_right h1
    rw [hSneg] at hSstar
    have := congrFun (congrFun hSstar 0) 0
    simp at this
    exact h2 (by linear_combination -this)
  obtain ⟨e, g, e₂, g₂, hEe, hEg, hEe₂, hEg₂, hef, hef₂, hee, hgg, hee₂, hgg₂, hee', hgg', heg₂,
    hge₂⟩ := exists_hyp_frame h hswap (by norm_num) hEp2 hEm2 hsum hEpEm hEmEp hne
  have hAv : ∀ (v : Fin 4 → K) (ε : K), ε * ε = 1 → eigProj S ε *ᵥ v = v →
      A *ᵥ v = (l * ε) • v := by
    intro v ε hεε hv
    rw [hAS, smul_mulVec, eig_of_fixed h2 hεε hv, smul_smul]
  have hAe : A *ᵥ e = l • e := by simpa using hAv e 1 (by norm_num) hEe
  have hAe₂ : A *ᵥ e₂ = l • e₂ := by simpa using hAv e₂ 1 (by norm_num) hEe₂
  have hAg : A *ᵥ g = (-l) • g := by simpa using hAv g (-1) (by norm_num) hEg
  have hAg₂ : A *ᵥ g₂ = (-l) • g₂ := by simpa using hAv g₂ (-1) (by norm_num) hEg₂
  obtain ⟨α, hα⟩ := exists_pow_four_eq_neg_one h hp
  obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ := class1b_of_frame h h2 hα hef hef₂ hee hgg hee₂ hgg₂ hee'
    hgg' heg₂ hge₂ hAe hAe₂ hAg hAg₂
  exact ⟨c, hc1, hc2, hc3, Or.inr ⟨⟨2, rfl⟩, hc4⟩, hc5⟩

theorem fixed_class2alt (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) K)
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = (-1 : K) • 1) :
    FixConcl h n A (fun M => M.map h.bar) := by
  obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ := exists_class2_alt h h2 hn hAu hAA
  exact ⟨c, hc1, hc2, hc3, Or.inl hc4, hc5⟩

end Assembly

end CFSG.GH74.Generic.S45.Uni
