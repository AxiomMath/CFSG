module

public import CFSG.CGT.Stroth77.Extension210Basic

public section

namespace CFSG.CGT.Stroth77

theorem hk0_t111 : 1 ≤ (Type321.k) 0 := by decide

set_option maxHeartbeats 4000000 in
theorem classify_t111 (V W U R : Torus (Type321.k) →+ Torus (Type321.k))
    (hrels : SigmaFourRels V W U R)
    (hV0 : (2 : ℤ) • V (gen (Type321.k) 0) = Torus.ofInt (Type321.k) ![-6, 2, -2])
    (hV1 : V (gen (Type321.k) 1) = Torus.ofInt (Type321.k) ![4, 1, 6])
    (hV2 : V (gen (Type321.k) 2) = Torus.ofInt (Type321.k) ![-28, 22, -7])
    (hW0 : (2 : ℤ) • W (gen (Type321.k) 0) = Torus.ofInt (Type321.k) ![2, 2, 4])
    (hW1 : W (gen (Type321.k) 1) = Torus.ofInt (Type321.k) ![0, 3, 0])
    (hW2 : W (gen (Type321.k) 2) = Torus.ofInt (Type321.k) ![-20, -6, -5])
    (hU0 : (2 : ℤ) • U (gen (Type321.k) 0) = Torus.ofInt (Type321.k) ![6, 0, 0])
    (hU1 : U (gen (Type321.k) 1) = Torus.ofInt (Type321.k) ![0, 0, 1])
    (hU2 : U (gen (Type321.k) 2) = Torus.ofInt (Type321.k) ![0, 1, 0])
    (hR0 : (2 : ℤ) • R (gen (Type321.k) 0) = Torus.ofInt (Type321.k) ![2, 0, 0])
    (hR1 : R (gen (Type321.k) 1) = Torus.ofInt (Type321.k) ![0, 0, 1])
    (hR2 : R (gen (Type321.k) 2) = Torus.ofInt (Type321.k) ![-4, -1, -1]) :
    ∃ zv : Fin 3 → ℤ, ∃ hz : (2 : ℤ) • Torus.ofInt (Type321.k) zv = 0, Even (zv 0) ∧
      ((shearHomIdx2R (Type321.k) (hk0_t111) zv hz (V (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 0))) = Torus.ofInt (Type321.k) ![-3, 1, -1] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (W (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 0))) = Torus.ofInt (Type321.k) ![1, 1, 2] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (U (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 0))) = Torus.ofInt (Type321.k) ![-1, 0, 0] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (R (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 0))) = Torus.ofInt (Type321.k) ![1, 0, 0] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (V (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 1))) = Torus.ofInt (Type321.k) ![4, 1, 6] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (W (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 1))) = Torus.ofInt (Type321.k) ![0, 3, 0] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (U (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 1))) = Torus.ofInt (Type321.k) ![0, 0, 1] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (R (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 1))) = Torus.ofInt (Type321.k) ![0, 0, 1] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (V (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 2))) = Torus.ofInt (Type321.k) ![84, 22, -7] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (W (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 2))) = Torus.ofInt (Type321.k) ![28, -6, -5] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (U (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 2))) = Torus.ofInt (Type321.k) ![0, 1, 0] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (R (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 2))) = Torus.ofInt (Type321.k) ![4, -1, -1]) ∨
       (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (V (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 0))) = Torus.ofInt (Type321.k) ![-3, 5, -1] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (W (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 0))) = Torus.ofInt (Type321.k) ![1, 1, -2] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (U (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 0))) = Torus.ofInt (Type321.k) ![3, 0, 0] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (R (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 0))) = Torus.ofInt (Type321.k) ![1, 0, 0] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (V (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 1))) = Torus.ofInt (Type321.k) ![4, 1, 6] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (W (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 1))) = Torus.ofInt (Type321.k) ![0, 3, 0] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (U (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 1))) = Torus.ofInt (Type321.k) ![0, 0, 1] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (R (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 1))) = Torus.ofInt (Type321.k) ![0, 0, 1] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (V (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 2))) = Torus.ofInt (Type321.k) ![20, 38, 9] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (W (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 2))) = Torus.ofInt (Type321.k) ![28, -6, -5] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (U (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 2))) = Torus.ofInt (Type321.k) ![0, 1, 0] ∧
        shearHomIdx2R (Type321.k) (hk0_t111) zv hz (R (shearHomIdx2R (Type321.k) (hk0_t111) zv hz (gen (Type321.k) 2))) = Torus.ofInt (Type321.k) ![4, -1, -1])) := by
  have hk : ∀ i, 1 ≤ (Type321.k) i := fun i => by fin_cases i <;> decide
  obtain ⟨eV, heV, hVe⟩ := exists_bits_Idx2R hk (h := ![-3, 1, -1]) (y := V (gen _ 0))
    (by rw [hV0]; congr 1; decide)
  obtain ⟨xV, yV, zV, rfl⟩ : ∃ a b c, eV = ![a, b, c] :=
    ⟨eV 0, eV 1, eV 2, by funext i; fin_cases i <;> rfl⟩
  have bxV : xV = 0 ∨ xV = 1 := heV 0
  have byV : yV = 0 ∨ yV = 1 := heV 1
  have bzV : zV = 0 ∨ zV = 1 := heV 2
  have hV0' : V (gen _ 0) = Torus.ofInt _ ![-3 + xV * 4, 1 + yV * 4, -1 + zV * 4] := by
    rw [hVe]; congr 1; funext i; fin_cases i <;> simp [Type321.k]
  have eV' := endo_ofInt_vec_Idx2R V hV0' hV1 hV2
  obtain ⟨eW, heW, hWe⟩ := exists_bits_Idx2R hk (h := ![1, 1, 2]) (y := W (gen _ 0))
    (by rw [hW0]; congr 1; decide)
  obtain ⟨xW, yW, zW, rfl⟩ : ∃ a b c, eW = ![a, b, c] :=
    ⟨eW 0, eW 1, eW 2, by funext i; fin_cases i <;> rfl⟩
  have bxW : xW = 0 ∨ xW = 1 := heW 0
  have byW : yW = 0 ∨ yW = 1 := heW 1
  have bzW : zW = 0 ∨ zW = 1 := heW 2
  have hW0' : W (gen _ 0) = Torus.ofInt _ ![1 + xW * 4, 1 + yW * 4, 2 + zW * 4] := by
    rw [hWe]; congr 1; funext i; fin_cases i <;> simp [Type321.k]
  have eW' := endo_ofInt_vec_Idx2R W hW0' hW1 hW2
  obtain ⟨eU, heU, hUe⟩ := exists_bits_Idx2R hk (h := ![3, 0, 0]) (y := U (gen _ 0))
    (by rw [hU0]; congr 1; decide)
  obtain ⟨xU, yU, zU, rfl⟩ : ∃ a b c, eU = ![a, b, c] :=
    ⟨eU 0, eU 1, eU 2, by funext i; fin_cases i <;> rfl⟩
  have bxU : xU = 0 ∨ xU = 1 := heU 0
  have byU : yU = 0 ∨ yU = 1 := heU 1
  have bzU : zU = 0 ∨ zU = 1 := heU 2
  have hU0' : U (gen _ 0) = Torus.ofInt _ ![3 + xU * 4, 0 + yU * 4, 0 + zU * 4] := by
    rw [hUe]; congr 1; funext i; fin_cases i <;> simp [Type321.k]
  have eU' := endo_ofInt_vec_Idx2R U hU0' hU1 hU2
  obtain ⟨eR, heR, hRe⟩ := exists_bits_Idx2R hk (h := ![1, 0, 0]) (y := R (gen _ 0))
    (by rw [hR0]; congr 1; decide)
  obtain ⟨xR, yR, zR, rfl⟩ : ∃ a b c, eR = ![a, b, c] :=
    ⟨eR 0, eR 1, eR 2, by funext i; fin_cases i <;> rfl⟩
  have bxR : xR = 0 ∨ xR = 1 := heR 0
  have byR : yR = 0 ∨ yR = 1 := heR 1
  have bzR : zR = 0 ∨ zR = 1 := heR 2
  have hR0' : R (gen _ 0) = Torus.ofInt _ ![1 + xR * 4, 0 + yR * 4, 0 + zR * 4] := by
    rw [hRe]; congr 1; funext i; fin_cases i <;> simp [Type321.k]
  have eR' := endo_ofInt_vec_Idx2R R hR0' hR1 hR2
  have c1 : xV = 0 := by
    have r := DFunLike.congr_fun hrels.uv_sq (gen (Type321.k) 0)
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, gen_zero_eq_ofInt_Idx2R, eV', eW',
      eU', eR', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_mul, zero_mul, add_zero, zero_add, Torus.ofInt_eq_ofInt_iff] at r
    have r0 := Int.ModEq.dvd (r 0)
    have r1 := Int.ModEq.dvd (r 1)
    have r2 := Int.ModEq.dvd (r 2)
    clear r
    try norm_num [Type321.k] at r0
    try ring_nf at r0
    try norm_num [Type321.k] at r1
    try ring_nf at r1
    try norm_num [Type321.k] at r2
    try ring_nf at r2
    omega
  subst xV
  have c2 : xW = 0 := by
    have r := DFunLike.congr_fun hrels.t_sq (gen (Type321.k) 0)
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, gen_zero_eq_ofInt_Idx2R, eV', eW',
      eU', eR', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_mul, zero_mul, add_zero, zero_add, Torus.ofInt_eq_ofInt_iff] at r
    have r0 := Int.ModEq.dvd (r 0)
    have r1 := Int.ModEq.dvd (r 1)
    have r2 := Int.ModEq.dvd (r 2)
    clear r
    try norm_num [Type321.k] at r0
    try ring_nf at r0
    try norm_num [Type321.k] at r1
    try ring_nf at r1
    try norm_num [Type321.k] at r2
    try ring_nf at r2
    omega
  subst xW
  have c3 : xR = 0 := by
    have r := DFunLike.congr_fun hrels.rho_cube (gen (Type321.k) 0)
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, gen_zero_eq_ofInt_Idx2R, eV', eW',
      eU', eR', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_mul, zero_mul, add_zero, zero_add, Torus.ofInt_eq_ofInt_iff] at r
    have r0 := Int.ModEq.dvd (r 0)
    have r1 := Int.ModEq.dvd (r 1)
    have r2 := Int.ModEq.dvd (r 2)
    clear r
    try norm_num [Type321.k] at r0
    try ring_nf at r0
    try norm_num [Type321.k] at r1
    try ring_nf at r1
    try norm_num [Type321.k] at r2
    try ring_nf at r2
    omega
  subst xR
  have c4 : zU = yU := by
    have r := DFunLike.congr_fun hrels.u_sq (gen (Type321.k) 0)
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, gen_zero_eq_ofInt_Idx2R, eV', eW',
      eU', eR', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_mul, zero_mul, add_zero, zero_add, Torus.ofInt_eq_ofInt_iff] at r
    have r0 := Int.ModEq.dvd (r 0)
    have r1 := Int.ModEq.dvd (r 1)
    have r2 := Int.ModEq.dvd (r 2)
    clear r
    try norm_num [Type321.k] at r0
    try ring_nf at r0
    try norm_num [Type321.k] at r1
    try ring_nf at r1
    try norm_num [Type321.k] at r2
    try ring_nf at r2
    omega
  subst zU
  have c5 : yR = yU := by
    have r := DFunLike.congr_fun hrels.u_rho (gen (Type321.k) 0)
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, gen_zero_eq_ofInt_Idx2R, eV', eW',
      eU', eR', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_mul, zero_mul, add_zero, zero_add, Torus.ofInt_eq_ofInt_iff] at r
    have r0 := Int.ModEq.dvd (r 0)
    have r1 := Int.ModEq.dvd (r 1)
    have r2 := Int.ModEq.dvd (r 2)
    clear r
    try norm_num [Type321.k] at r0
    try ring_nf at r0
    try norm_num [Type321.k] at r1
    try ring_nf at r1
    try norm_num [Type321.k] at r2
    try ring_nf at r2
    omega
  subst yR
  have c6 : (yV + zV + zW) % 2 = 0 ∧ yW = zV := by
    have r := DFunLike.congr_fun hrels.uv_rho (gen (Type321.k) 0)
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, gen_zero_eq_ofInt_Idx2R, eV', eW',
      eU', eR', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_mul, zero_mul, add_zero, zero_add, Torus.ofInt_eq_ofInt_iff] at r
    have r0 := Int.ModEq.dvd (r 0)
    have r1 := Int.ModEq.dvd (r 1)
    have r2 := Int.ModEq.dvd (r 2)
    clear r
    try norm_num [Type321.k] at r0
    try ring_nf at r0
    try norm_num [Type321.k] at r1
    try ring_nf at r1
    try norm_num [Type321.k] at r2
    try ring_nf at r2
    exact ⟨by omega, by omega⟩
  obtain ⟨c6, c7⟩ := c6
  subst yW
  have c8 : (yV + zV + xU) % 2 = 1 := by
    have r := DFunLike.congr_fun hrels.uv_comm_u (gen (Type321.k) 0)
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, gen_zero_eq_ofInt_Idx2R, eV', eW',
      eU', eR', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_mul, zero_mul, add_zero, zero_add, Torus.ofInt_eq_ofInt_iff] at r
    have r0 := Int.ModEq.dvd (r 0)
    have r1 := Int.ModEq.dvd (r 1)
    have r2 := Int.ModEq.dvd (r 2)
    clear r
    try norm_num [Type321.k] at r0
    try ring_nf at r0
    try norm_num [Type321.k] at r1
    try ring_nf at r1
    try norm_num [Type321.k] at r2
    try ring_nf at r2
    omega
  have hz : (2 : ℤ) • Torus.ofInt (Type321.k) ![4 * zV, 4 * zR, 4 * (zR + yU)] = 0 := by
    rw [← Torus.ofInt_zsmul, Torus.ofInt_eq_zero_iff]
    intro i; fin_cases i <;> norm_num [Type321.k] <;> omega
  have hz0 : Even ((![4 * zV, 4 * zR, 4 * (zR + yU)] : Fin 3 → ℤ) 0) := ⟨2 * zV, by simp; ring⟩
  refine ⟨![4 * zV, 4 * zR, 4 * (zR + yU)], hz, hz0, ?_⟩
  have s0 := shearHomIdx2R_ofInt hk0_t111 _ hz
  simp only [gen_zero_eq_ofInt_Idx2R, gen_one_eq_ofInt_Idx2R, gen_two_eq_ofInt_Idx2R, s0, eV', eW', eU', eR',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, zero_mul, mul_zero, mul_one, add_zero, zero_add,
    Torus.ofInt_eq_ofInt_iff]
  rcases bxU with hxU | hxU <;> subst xU
  ·
    refine Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro i <;> fin_cases i <;>
      (rw [Int.modEq_iff_dvd]; norm_num [Type321.k] <;> (try ring_nf) <;> omega)
  ·
    refine Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro i <;> fin_cases i <;>
      (rw [Int.modEq_iff_dvd]; norm_num [Type321.k] <;> (try ring_nf) <;> omega)

end CFSG.CGT.Stroth77
