module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutMixE
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutDb
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

section Gram

variable {F : Type} [Field F]

@[expose] def ip (G : Matrix (Fin 4) (Fin 4) F) (x y : Fin 4 → F) : F := x ⬝ᵥ (G *ᵥ y)

theorem ip_comm {G : Matrix (Fin 4) (Fin 4) F} (hGs : Gᵀ = G) (x y : Fin 4 → F) : ip G x y = ip G y x := by
  unfold ip
  rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.vecMul_transpose, hGs]

theorem ip_g_left {G g : Matrix (Fin 4) (Fin 4) F} (hGg : G * g = gᵀ * G) (x y : Fin 4 → F) :
    ip G (g *ᵥ x) y = ip G x (g *ᵥ y) := by
  unfold ip
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← hGg,
    ← Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]

theorem ip_gg {G g : Matrix (Fin 4) (Fin 4) F} (hGg : G * g = gᵀ * G) (hgg : g * g = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F))
    (x y : Fin 4 → F) : ip G (g *ᵥ x) (g *ᵥ y) = - ip G x y := by
  rw [ip_g_left hGg, Matrix.mulVec_mulVec, hgg, Matrix.smul_mulVec, Matrix.one_mulVec, neg_one_smul]
  unfold ip
  rw [Matrix.mulVec_neg, dotProduct_neg]

@[expose] def frameP (g : Matrix (Fin 4) (Fin 4) F) (v w : Fin 4 → F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.of fun r c => ![v, g *ᵥ v, w, g *ᵥ w] c r

theorem gram_apply (G : Matrix (Fin 4) (Fin 4) F) (P : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4) :
    (Pᵀ * G * P) i j = ip G (fun r => P r i) (fun r => P r j) := by
  simp only [Matrix.mul_apply, ip, dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

theorem gram_frameP {G g : Matrix (Fin 4) (Fin 4) F} (hGs : Gᵀ = G) (hGg : G * g = gᵀ * G)
    (hgg : g * g = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F)) (v w : Fin 4 → F) :
    (frameP g v w)ᵀ * G * frameP g v w =
      !![ip G v v, ip G v (g *ᵥ v), ip G v w, ip G v (g *ᵥ w);
         ip G v (g *ᵥ v), -ip G v v, ip G v (g *ᵥ w), -ip G v w;
         ip G v w, ip G v (g *ᵥ w), ip G w w, ip G w (g *ᵥ w);
         ip G v (g *ᵥ w), -ip G v w, ip G w (g *ᵥ w), -ip G w w] := by
  have hc : ∀ i, (fun r => frameP g v w r i) = ![v, g *ᵥ v, w, g *ᵥ w] i := fun i => by
    ext r; simp [frameP]
  have f10 : ip G (g *ᵥ v) v = ip G v (g *ᵥ v) := ip_comm hGs _ _
  have f11 : ip G (g *ᵥ v) (g *ᵥ v) = -ip G v v := ip_gg hGg hgg v v
  have f12 : ip G (g *ᵥ v) w = ip G v (g *ᵥ w) := by rw [ip_g_left hGg]
  have f13 : ip G (g *ᵥ v) (g *ᵥ w) = -ip G v w := ip_gg hGg hgg v w
  have f20 : ip G w v = ip G v w := ip_comm hGs _ _
  have f21 : ip G w (g *ᵥ v) = ip G v (g *ᵥ w) := by rw [ip_comm hGs, ip_g_left hGg]
  have f30 : ip G (g *ᵥ w) v = ip G v (g *ᵥ w) := ip_comm hGs _ _
  have f31 : ip G (g *ᵥ w) (g *ᵥ v) = -ip G v w := by rw [ip_gg hGg hgg, ip_comm hGs]
  have f32 : ip G (g *ᵥ w) w = ip G w (g *ᵥ w) := ip_comm hGs _ _
  have f33 : ip G (g *ᵥ w) (g *ᵥ w) = -ip G w w := ip_gg hGg hgg w w
  ext i j
  rw [gram_apply, hc, hc]
  fin_cases i <;> fin_cases j <;> simp [f10, f11, f12, f13, f20, f21, f30, f31, f32, f33]

theorem aniso2 [Finite F] (hF4 : Nat.card F % 4 = 3) {x y : F} (h : x * x + y * y = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    exact ⟨mul_self_eq_zero.1 (by simpa using h), rfl⟩
  · exfalso
    apply not_isSquare_neg_one hF4
    refine ⟨x / y, ?_⟩
    field_simp
    linear_combination -h

theorem det_gram_witt (a b t1 t2 : F) :
    (!![0, 0, a, b; 0, 0, b, -a; a, b, t1, t2; b, -a, t2, -t1] : Matrix (Fin 4) (Fin 4) F).det = (a * a + b * b) ^ 2 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem witt_aux [Finite F] (hF4 : Nat.card F % 4 = 3) {G g B : Matrix (Fin 4) (Fin 4) F} (hGs : Gᵀ = G)
    (hGg : G * g = gᵀ * G) (hgg : g * g = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F)) (hGB : G * B = 1)
    (hGd : ¬ IsSquare G.det) (v : Fin 4 → F) (hv : v ≠ 0) (h1 : ip G v v = 0) (h2 : ip G v (g *ᵥ v) = 0) : False := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  set w : Fin 4 → F := B *ᵥ Pi.single j 1 with hw
  set a := ip G v w with ha
  have ha' : a = v j := by
    rw [ha, hw]
    unfold ip
    rw [Matrix.mulVec_mulVec, hGB, Matrix.one_mulVec]
    simp [dotProduct_single]
  set b := ip G v (g *ᵥ w) with hb
  have hgram := gram_frameP hGs hGg hgg v w
  rw [h1, h2] at hgram
  have hdet := congrArg Matrix.det hgram
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  simp only [neg_zero] at hdet
  rw [det_gram_witt] at hdet
  have hne : a * a + b * b ≠ 0 := fun h => hj (by rw [← ha']; exact (aniso2 hF4 h).1)
  have hP : (frameP g v w).det ≠ 0 := by
    intro h0
    rw [h0] at hdet
    have h3 : (a * a + b * b) ^ 2 = 0 := by rw [ha, hb]; simpa using hdet.symm
    exact hne ((pow_eq_zero_iff two_ne_zero).1 h3)
  apply hGd
  refine ⟨(a * a + b * b) / (frameP g v w).det, ?_⟩
  field_simp
  linear_combination hdet

theorem exists_orth (G g : Matrix (Fin 4) (Fin 4) F) (e : Fin 4 → F) :
    ∃ u : Fin 4 → F, u ≠ 0 ∧ ip G e u = 0 ∧ ip G (g *ᵥ e) u = 0 := by
  set M : Matrix (Fin 4) (Fin 4) F := Matrix.of ![e ᵥ* G, (g *ᵥ e) ᵥ* G, 0, 0] with hM
  have hdet : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 2 (by intro j; simp [hM])
  obtain ⟨u, hu, hMu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have h0 : (M *ᵥ u) 0 = (e ᵥ* G) ⬝ᵥ u := by simp [hM, Matrix.mulVec, dotProduct]
  have h1 : (M *ᵥ u) 1 = ((g *ᵥ e) ᵥ* G) ⬝ᵥ u := by simp [hM, Matrix.mulVec, dotProduct]
  refine ⟨u, hu, ?_, ?_⟩
  · have := congrFun hMu 0
    rw [h0] at this
    unfold ip
    rw [Matrix.dotProduct_mulVec]
    simpa using this
  · have := congrFun hMu 1
    rw [h1] at this
    unfold ip
    rw [Matrix.dotProduct_mulVec]
    simpa using this

theorem ip_conj (P G : Matrix (Fin 4) (Fin 4) F) (x y : Fin 4 → F) : ip (Pᵀ * G * P) x y = ip G (P *ᵥ x) (P *ᵥ y) := by
  unfold ip
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem exists_isotropic [Finite F] (hF4 : Nat.card F % 4 = 3) {G : Matrix (Fin 4) (Fin 4) F} (hGs : Gᵀ = G)
    (hGd : G.det ≠ 0) : ∃ e : Fin 4 → F, e ≠ 0 ∧ ip G e e = 0 := by
  have hK := ringChar_ne_two_of_card_mod hF4
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  obtain ⟨Q, hQ⟩ := GenLocL5Sign.exists_orthogonal_congr hK G hGs
  set Δ : Matrix (Fin 4) (Fin 4) F := (Q : Matrix (Fin 4) (Fin 4) F)ᵀ * G * (Q : Matrix (Fin 4) (Fin 4) F) with hΔ
  have hQd : (Q : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit).ne_zero
  have hΔd : Δ.det ≠ 0 := by
    rw [hΔ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hQd hGd) hQd
  have hΔdiag : Δ = Matrix.diagonal (fun i => Δ i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [hQ i j hij]; simp [hij]
  have hd : ∀ i, Δ i i ≠ 0 := fun i h => by
    apply hΔd
    rw [hΔdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  obtain ⟨x, y, hxy⟩ := CFSG.ComponentClassification.CatalogueBOddQuadratic.exists_weighted_ternary_zero hodd
    (hd 0) (hd 1) (Δ 2 2)
  set w : Fin 4 → F := ![x, y, 1, 0] with hw
  refine ⟨(Q : Matrix (Fin 4) (Fin 4) F) *ᵥ w, ?_, ?_⟩
  · intro h0
    have hw0 : w = 0 := by
      have := congrArg (fun z => ((Q⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ z) h0
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rw [coe_inv_mul Q, Matrix.one_mulVec] at this
      exact this
    have := congrFun hw0 2
    simp [hw] at this
  · have e1 : ip G ((Q : Matrix (Fin 4) (Fin 4) F) *ᵥ w) ((Q : Matrix (Fin 4) (Fin 4) F) *ᵥ w) = ip Δ w w :=
      (ip_conj _ G w w).symm
    rw [e1]
    unfold ip
    rw [hΔdiag]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hw, Matrix.diagonal_apply]
    linear_combination hxy

theorem frameP_mul_C0 {g : Matrix (Fin 4) (Fin 4) F} (hgg : g * g = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F))
    (v w : Fin 4 → F) :
    g * frameP g v w = frameP g v w * bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] := by
  have e1 : g *ᵥ (g *ᵥ v) = -v := by
    rw [Matrix.mulVec_mulVec, hgg, Matrix.smul_mulVec, Matrix.one_mulVec, neg_one_smul]
  have e2 : g *ᵥ (g *ᵥ w) = -w := by
    rw [Matrix.mulVec_mulVec, hgg, Matrix.smul_mulVec, Matrix.one_mulVec, neg_one_smul]
  ext i j
  fin_cases j
  · simp [frameP, bd2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mulVec, dotProduct]
  · have := congrFun e1 i
    simp [Matrix.mulVec, dotProduct] at this
    simp [frameP, bd2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mulVec, dotProduct]
    simpa [Fin.sum_univ_four] using this
  · simp [frameP, bd2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mulVec, dotProduct]
  · have := congrFun e2 i
    simp [Matrix.mulVec, dotProduct] at this
    simp [frameP, bd2, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mulVec, dotProduct]
    simpa [Fin.sum_univ_four] using this

theorem ext_frame [Finite F] (hF4 : Nat.card F % 4 = 3) (B g : Matrix (Fin 4) (Fin 4) F) (hBt : Bᵀ = B)
    (hBd : B.det ≠ 0) (hBns : ¬ IsSquare B.det) (hgg : g * g = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F))
    (hgB : g * B = B * gᵀ) :
    ∃ (P : GL (Fin 4) F) (κ : F) (B2 : Matrix (Fin 2) (Fin 2) F), κ ≠ 0 ∧
      B = (P : Matrix (Fin 4) (Fin 4) F) * bd2 (κ • !![0, 1; 1, 0]) B2 * (P : Matrix (Fin 4) (Fin 4) F)ᵀ ∧
      g * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] := by
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hBd
  set G := B⁻¹ with hG
  have hGB : G * B = 1 := Matrix.nonsing_inv_mul B hBu
  have hBG : B * G = 1 := Matrix.mul_nonsing_inv B hBu
  have hGs : Gᵀ = G := by rw [hG, Matrix.transpose_nonsing_inv, hBt]
  have hGg : G * g = gᵀ * G := by
    calc G * g = G * g * (B * G) := by rw [hBG, Matrix.mul_one]
      _ = G * (g * B) * G := by simp only [Matrix.mul_assoc]
      _ = G * (B * gᵀ) * G := by rw [hgB]
      _ = (G * B) * gᵀ * G := by simp only [Matrix.mul_assoc]
      _ = gᵀ * G := by rw [hGB, Matrix.one_mul]
  have hdd : G.det * B.det = 1 := by rw [← Matrix.det_mul, hGB, Matrix.det_one]
  have hGd : G.det ≠ 0 := left_ne_zero_of_mul_eq_one hdd
  have hGns : ¬ IsSquare G.det := fun hsq => hBns (by
    have : B.det = (G.det)⁻¹ := eq_inv_of_mul_eq_one_right hdd
    rw [this]
    exact hsq.inv)
  obtain ⟨e, he0, he⟩ := exists_isotropic hF4 hGs hGd
  have hc : ip G e (g *ᵥ e) ≠ 0 := fun h => witt_aux hF4 hGs hGg hgg hGB hGns e he0 he h
  obtain ⟨u, hu0, hu1, hu2⟩ := exists_orth G g e
  have hst : ip G u u * ip G u u + ip G u (g *ᵥ u) * ip G u (g *ᵥ u) ≠ 0 := fun h =>
    witt_aux hF4 hGs hGg hgg hGB hGns u hu0 (aniso2 hF4 h).1 (aniso2 hF4 h).2
  have hb : ip G e (g *ᵥ u) = 0 := by rw [← ip_g_left hGg]; exact hu2
  have hgram := gram_frameP hGs hGg hgg e u
  rw [he, hu1, hb] at hgram
  have hgram2 : (frameP g e u)ᵀ * G * frameP g e u =
      bd2 (ip G e (g *ᵥ e) • !![0, 1; 1, 0]) !![ip G u u, ip G u (g *ᵥ u); ip G u (g *ᵥ u), -ip G u u] := by
    rw [hgram]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [bd2]
  set c := ip G e (g *ᵥ e) with hcdef
  set s := ip G u u with hsdef
  set t := ip G u (g *ᵥ u) with htdef
  set P0 := frameP g e u with hP0def
  have hdetc : (c • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F)).det = -(c * c) := by
    simp [Matrix.det_fin_two]
  have hdetA : (!![s, t; t, -s] : Matrix (Fin 2) (Fin 2) F).det = -(s * s + t * t) := by
    simp [Matrix.det_fin_two]
    ring
  have hdetGram : (P0ᵀ * G * P0).det = (c * c) * (s * s + t * t) := by
    rw [hgram2, bd2_det, hdetc, hdetA]; ring
  have hdetP : P0.det ≠ 0 := by
    intro h0
    have : (P0ᵀ * G * P0).det = 0 := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0]; simp
    rw [hdetGram] at this
    exact mul_ne_zero (mul_ne_zero hc hc) hst this
  set A : Matrix (Fin 2) (Fin 2) F := !![s, t; t, -s] with hA
  have hAdet : A.det ≠ 0 := by rw [hdetA]; exact neg_ne_zero.2 hst
  set B2 := A⁻¹ with hB2
  have hAB : A * B2 = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hAdet)
  set J : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0] with hJ
  have hJJ : J * J = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hJ, Matrix.mul_apply, Fin.sum_univ_two]
  set Mi := bd2 (c⁻¹ • J) B2 with hMi
  have hGramMi : (P0ᵀ * G * P0) * Mi = 1 := by
    rw [hgram2, hMi, bd2_mul, smul_mul_smul_comm, hJJ, mul_inv_cancel₀ hc, one_smul, hAB, bd2_one]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P0 hdetP, c⁻¹, B2, inv_ne_zero hc, ?_, ?_⟩
  · show B = P0 * Mi * P0ᵀ
    have h1 : P0ᵀ * (G * P0 * Mi) = 1 := by rw [← hGramMi]; simp only [Matrix.mul_assoc]
    have h2 : (G * P0 * Mi) * P0ᵀ = 1 := mul_eq_one_comm.1 h1
    have h3 : G * (P0 * Mi * P0ᵀ) = 1 := by rw [← h2]; simp only [Matrix.mul_assoc]
    calc B = B * (G * (P0 * Mi * P0ᵀ)) := by rw [h3, Matrix.mul_one]
      _ = (B * G) * (P0 * Mi * P0ᵀ) := (Matrix.mul_assoc B G (P0 * Mi * P0ᵀ)).symm
      _ = P0 * Mi * P0ᵀ := by rw [hBG, Matrix.one_mul]
  · exact frameP_mul_C0 hgg e u

end Gram

section GenExt

variable {F : Type} [Field F]

theorem bd2_transpose (A B : Matrix (Fin 2) (Fin 2) F) : (bd2 A B)ᵀ = bd2 Aᵀ Bᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd2]

theorem planar_eq_bd2 (r : SL(2, F)) : (planar r : Matrix (Fin 4) (Fin 4) F) = bd2 (r : Matrix (Fin 2) (Fin 2) F) 1 := by
  rw [coe_planar]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd2]

theorem planar_form_bd2 (r : SL(2, F)) (X Y : Matrix (Fin 2) (Fin 2) F) :
    (planar r : Matrix (Fin 4) (Fin 4) F) * bd2 X Y * (planar r : Matrix (Fin 4) (Fin 4) F)ᵀ =
      bd2 ((r : Matrix (Fin 2) (Fin 2) F) * X * (r : Matrix (Fin 2) (Fin 2) F)ᵀ) Y := by
  rw [planar_eq_bd2, bd2_transpose, bd2_mul, bd2_mul]
  simp

theorem C0J (κ : F) : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * (κ • !![0, 1; 1, 0]) =
    Matrix.diagonal ![-κ, κ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem dgS_form (κ : F) (s : Fˣ) :
    (dgS s : Matrix (Fin 2) (Fin 2) F) * (κ • !![0, 1; 1, 0]) * (dgS s : Matrix (Fin 2) (Fin 2) F)ᵀ =
      κ • !![0, 1; 1, 0] := by
  have hs : (s : F) * (s : F)⁻¹ = 1 := mul_inv_cancel₀ s.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dgS, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination κ * hs

theorem rE_comm_C0 (α0 α1 β0 β1 γ0 γ1 δ0 δ1 : F) :
    rE α0 α1 β0 β1 γ0 γ1 δ0 δ1 * bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] =
      bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] * rE α0 α1 β0 β1 γ0 γ1 δ0 δ1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rE, bd2, Matrix.mul_apply, Fin.sum_univ_four]

theorem gen_Ext_core [Finite F] (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) (κ : F)
    (B2 : Matrix (Fin 2) (Fin 2) F) (Γ : Subgroup SL(4, F))
    (hB : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * bd2 (κ • !![0, 1; 1, 0]) B2 *
      (x : Matrix (Fin 4) (Fin 4) F)ᵀ = bd2 (κ • !![0, 1; 1, 0]) B2 → x ∈ Γ)
    (hM : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * (bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] *
      bd2 (κ • !![0, 1; 1, 0]) B2) * (x : Matrix (Fin 4) (Fin 4) F)ᵀ =
      bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] * bd2 (κ • !![0, 1; 1, 0]) B2 → x ∈ Γ)
    (hC : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] =
      bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] * (x : Matrix (Fin 4) (Fin 4) F) → x ∈ Γ) : Γ = ⊤ := by
  have hK := ringChar_ne_two_of_card_mod hF4
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  have hodd : Nat.card F % 2 = 1 := by omega
  obtain ⟨ρ, hρ4, hρ1, hρ5⟩ := exists_rho hF4 h7
  have hD : ∀ s : Fˣ, planarHom (dgS s) ∈ Γ := fun s => hB _ (by
    rw [planarHom_apply, planar_form_bd2, dgS_form])
  have hG : ∀ σ : Fˣ, planarHom (hypS h2 1 σ) ∈ Γ := fun σ => hM _ (by
    rw [planarHom_apply, bd2_mul, planar_form_bd2, C0J]
    have := hypS_form h2 1 σ (-κ) κ (by simp)
    rw [this])
  obtain ⟨h01, h10⟩ := plane_top hodd h2 1 ρ hρ4 hρ1 hρ5 Γ hD hG
  have hu : (1 : F) * 1 - 1 * 1 - 1 * (-1) + 0 * 2 = 1 := by ring
  have hv : (1 : F) * 1 + 1 * 1 - 1 * 2 - 0 * (-1) = 0 := by ring
  have hr : rEsl 1 1 1 0 (-1) 2 1 1 hu hv ∈ Γ := hC _ (rE_comm_C0 1 1 1 0 (-1) 2 1 1)
  refine mix_E Γ h01 h10 1 1 1 0 (-1) 2 1 1 hu hv hr ?_ ?_ ?_
  · intro h
    exact h2 (by linear_combination h)
  · intro h
    have := (aniso2 hF4 h).1
    exact one_ne_zero (by linear_combination this)
  · intro h
    have := (aniso2 hF4 h).1
    exact one_ne_zero (by linear_combination -this)

end GenExt

section ClassExtThm

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem classExt (F : Type) [Field F] [Finite F] : ClassExt F := by
  intro hF4 h7 B g hBt hdet hBd hgg hgB Γ h1 h2 h3
  obtain ⟨P, κ, B2, hκ, hBP, hgP⟩ := ext_frame hF4 B g hBt hdet hBd hgg hgB
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul P
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F)
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  have hPt : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have hPt' : Pmᵀ * Piᵀ = 1 := by rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
  have eg : Pi * g * Pm = bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] := by
    rw [Matrix.mul_assoc, hgP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have eB : Pi * B * Piᵀ = bd2 (κ • !![0, 1; 1, 0]) B2 := by
    rw [hBP]
    calc Pi * (Pm * bd2 (κ • !![0, 1; 1, 0]) B2 * Pmᵀ) * Piᵀ =
        (Pi * Pm) * bd2 (κ • !![0, 1; 1, 0]) B2 * (Pmᵀ * Piᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPiP, hPt', Matrix.one_mul, Matrix.mul_one]
  have egB : Pi * (g * B) * Piᵀ = bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] * bd2 (κ • !![0, 1; 1, 0]) B2 := by
    rw [← eg, ← eB]
    calc Pi * (g * B) * Piᵀ = Pi * g * (Pm * Pi) * B * Piᵀ := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine top_of_conj Γ P (gen_Ext_core hF4 h7 κ B2 (Γ.comap (slConjugation 4 F P).toMonoidHom) ?_ ?_ ?_)
  · intro x hx
    show (slConjugation 4 F P).toMonoidHom x ∈ Γ
    exact h2 _ ((conj_form_iff P x B).2 (by rw [eB]; exact hx))
  · intro x hx
    show (slConjugation 4 F P).toMonoidHom x ∈ Γ
    exact h3 _ ((conj_form_iff P x (g * B)).2 (by rw [egB]; exact hx))
  · intro x hx
    show (slConjugation 4 F P).toMonoidHom x ∈ Γ
    exact h1 _ ((conj_commute_iff P x g).2 (by rw [eg]; exact hx))

end ClassExtThm

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
