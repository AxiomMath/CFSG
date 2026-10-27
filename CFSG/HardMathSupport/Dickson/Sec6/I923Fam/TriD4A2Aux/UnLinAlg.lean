module

public import CFSG.LieType.Steinberg.PartB
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

public section

open CFSG.LieType.Steinberg Matrix

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

variable {k : Type*} [Field k]

@[expose] def tauMat (ε : k ≃+* k) (κ : kˣ) (N : Matrix (Fin 2) (Fin 2) k) :
    Matrix (Fin 2) (Fin 2) k :=
  !![ε (N 1 1), ε (N 1 0) * ((κ⁻¹ : kˣ) : k); (κ : k) * ε (N 0 1), ε (N 0 0)]

theorem tauMat_det (ε : k ≃+* k) (κ : kˣ) (N : Matrix (Fin 2) (Fin 2) k) :
    (tauMat ε κ N).det = ε N.det := by
  simp only [tauMat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_sub, map_mul]
  have : (κ : k) * ((κ⁻¹ : kˣ) : k) = 1 := by simp
  linear_combination (-(ε (N 0 1) * ε (N 1 0))) * this

theorem tauMat_mul (ε : k ≃+* k) (κ : kˣ) (N N' : Matrix (Fin 2) (Fin 2) k) :
    tauMat ε κ (N * N') = tauMat ε κ N * tauMat ε κ N' := by
  have hκ0 : (κ : k) ≠ 0 := κ.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tauMat, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul] <;> field_simp <;> ring

@[expose] def tauHat (ε : k ≃+* k) (κ : kˣ) :
    Matrix.SpecialLinearGroup (Fin 2) k →* Matrix.SpecialLinearGroup (Fin 2) k where
  toFun N := ⟨tauMat ε κ (N : Matrix (Fin 2) (Fin 2) k), by rw [tauMat_det, N.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tauMat]
  map_mul' N N' := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact tauMat_mul ε κ _ _

theorem coe_tauHat (ε : k ≃+* k) (κ : kˣ) (N : Matrix.SpecialLinearGroup (Fin 2) k) :
    ((tauHat ε κ N : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      tauMat ε κ (N : Matrix (Fin 2) (Fin 2) k) := rfl

theorem sl2U_coe (c : k) :
    ((sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, c; 0, 1] := rfl

theorem sl2L_coe (c : k) :
    ((sl2Lower c : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![1, 0; c, 1] := rfl

theorem tauHat_upper (ε : k ≃+* k) (κ : kˣ) (a : k) :
    tauHat ε κ (sl2Upper a) = sl2Lower ((κ : k) * ε a) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_tauHat, tauMat, sl2U_coe, sl2L_coe]

theorem tauHat_lower (ε : k ≃+* k) (κ : kˣ) (a : k) :
    tauHat ε κ (sl2Lower a) = sl2Upper (((κ⁻¹ : kˣ) : k) * ε a) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_tauHat, tauMat, sl2U_coe, sl2L_coe, mul_comm]

@[expose] def bMat (t w : k) : Matrix (Fin 2) (Fin 2) k := !![1, -(1 / (2 * w)); 0, t / w]

@[expose] def bInv (t w : k) : Matrix (Fin 2) (Fin 2) k := !![1, 1 / (2 * t); 0, w / t]

theorem bMat_mul_bInv {t w : k} (ht : t ≠ 0) (hw : w ≠ 0) (h2 : (2 : k) ≠ 0) :
    bMat t w * bInv t w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, bInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

theorem bInv_mul_bMat {t w : k} (ht : t ≠ 0) (hw : w ≠ 0) (h2 : (2 : k) ≠ 0) :
    bInv t w * bMat t w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, bInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

@[expose] def phiHom (F : Subfield k) {t w : k} (ht : t ≠ 0) (hw : w ≠ 0) (h2 : (2 : k) ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) k where
  toFun N := ⟨bMat t w * ((Matrix.SpecialLinearGroup.map F.subtype N :
      Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * bInv t w, by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one, mul_comm,
      ← Matrix.det_mul, bInv_mul_bMat ht hw h2, Matrix.det_one]⟩
  map_one' := by
    apply Subtype.ext
    simp [bMat_mul_bInv ht hw h2]
  map_mul' N M := by
    apply Subtype.ext
    have h := bInv_mul_bMat ht hw h2
    show bMat t w * ((Matrix.SpecialLinearGroup.map F.subtype (N * M) :
        Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * bInv t w =
      (bMat t w * ((Matrix.SpecialLinearGroup.map F.subtype N :
        Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * bInv t w) *
      (bMat t w * ((Matrix.SpecialLinearGroup.map F.subtype M :
        Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * bInv t w)
    simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul]
    calc bMat t w * (↑(Matrix.SpecialLinearGroup.map F.subtype N) *
          ↑(Matrix.SpecialLinearGroup.map F.subtype M)) * bInv t w
        = bMat t w * ↑(Matrix.SpecialLinearGroup.map F.subtype N) * (bInv t w * bMat t w) *
          ↑(Matrix.SpecialLinearGroup.map F.subtype M) * bInv t w := by
          rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem coe_phiHom (F : Subfield k) {t w : k} (ht : t ≠ 0) (hw : w ≠ 0) (h2 : (2 : k) ≠ 0)
    (N : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((phiHom F ht hw h2 N : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      bMat t w * (N.1.map F.subtype) * bInv t w := rfl

theorem tauMat_fixed_aux (ε : k ≃+* k) {κ : kˣ} {t : k} (ht : t ≠ 0) (hκ : (κ : k) = t * ε t)
    {w : k} (hw : w ≠ 0) (hεw : ε w = -w) (h2 : (2 : k) ≠ 0) {a b c d : k} (ha : ε a = a)
    (hb : ε b = b) (hc : ε c = c) (hd : ε d = d) :
    tauMat ε κ (!![1, 0; t, 1] * (bMat t w * !![a, b; c, d] * bInv t w) * !![1, 0; -t, 1]) =
      !![1, 0; t, 1] * (bMat t w * !![a, b; c, d] * bInv t w) * !![1, 0; -t, 1] := by
  have hεt : ε t ≠ 0 := (map_ne_zero ε).2 ht
  have hκ0 : (κ : k) ≠ 0 := κ.ne_zero
  have hκi : ((κ⁻¹ : kˣ) : k) = (κ : k)⁻¹ := by simp
  have h2ε : ε (2 : k) = 2 := map_ofNat ε 2
  simp only [bMat, bInv, tauMat, Matrix.mul_fin_two, hκi, hκ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [map_add, map_mul, map_div₀, map_sub, map_neg, ha, hb, hc, hd, hεw, h2ε] <;>
    field_simp <;> ring

theorem sl2Lower_inv' (a : k) : (sl2Lower a)⁻¹ = sl2Lower (-a) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, sl2L_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem tauHat_phi (ε : k ≃+* k) {κ t : kˣ} (hκ : (κ : k) = t * ε t) {w : k} (hw : w ≠ 0)
    (hεw : ε w = -w) (h2 : (2 : k) ≠ 0) (F : Subfield k) (hF : ∀ a ∈ F, ε a = a)
    (N : Matrix.SpecialLinearGroup (Fin 2) F) :
    tauHat ε κ (sl2Lower (t : k) * phiHom F t.ne_zero hw h2 N * (sl2Lower (t : k))⁻¹) =
      sl2Lower (t : k) * phiHom F t.ne_zero hw h2 N * (sl2Lower (t : k))⁻¹ := by
  apply Subtype.ext
  rw [coe_tauHat, sl2Lower_inv']
  simp only [Matrix.SpecialLinearGroup.coe_mul, sl2L_coe, coe_phiHom]
  have hN : N.1.map F.subtype =
      !![((N 0 0 : F) : k), ((N 0 1 : F) : k); ((N 1 0 : F) : k), ((N 1 1 : F) : k)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hN]
  exact tauMat_fixed_aux ε t.ne_zero hκ hw hεw h2 (hF _ (N 0 0).2) (hF _ (N 0 1).2)
    (hF _ (N 1 0).2) (hF _ (N 1 1).2)

@[expose] def diagSL (F : Subfield k) (a : ↥F) (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩

theorem coe_phiHom_diagSL (F : Subfield k) {t w : k} (ht : t ≠ 0) (hw : w ≠ 0) (h2 : (2 : k) ≠ 0)
    (a : ↥F) (ha : a ≠ 0) :
    ((phiHom F ht hw h2 (diagSL F a ha) : Matrix.SpecialLinearGroup (Fin 2) k) :
        Matrix (Fin 2) (Fin 2) k) =
      !![(a : k), ((a : k) - (a : k)⁻¹) / (2 * t); 0, (a : k)⁻¹] := by
  have ha' : (a : k) ≠ 0 := fun h => ha (Subtype.ext h)
  rw [coe_phiHom]
  have hN : (diagSL F a ha).1.map F.subtype = !![(a : k), 0; 0, (a : k)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagSL]
  rw [hN]
  simp only [bMat, bInv, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

theorem exists_finset_card_four_subfield {p : ℕ} [CharP k p] (hp5 : 5 ≤ p) (F : Subfield k) :
    ∃ s : Finset ↥F, s.card = 4 := by
  classical
  have hinj : Function.Injective (fun i : Fin 4 => ((i : ℕ) : ↥F)) := by
    intro i j h
    have h' : ((i : ℕ) : k) = ((j : ℕ) : k) := by
      have := congrArg F.subtype h
      simpa using this
    have := (CharP.natCast_eq_natCast k p).1 h'
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt this (by omega) (by omega))
  exact ⟨Finset.univ.map ⟨_, hinj⟩, by simp⟩

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
