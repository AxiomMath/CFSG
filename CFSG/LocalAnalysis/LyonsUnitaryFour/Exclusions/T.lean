module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.SignedDegreeTools
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.ExclusionArithmeticPrime
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι}
  {N : ℕ} {P : ℚ}

omit [DecidableEq ι] in
theorem lyons_signedDegree_ne_T (hD : LyonsSignedDegreeData B row f p N P) :
    B.val.map row ≠ lyonsConfiguration .T := by
  intro hM
  have hcount : ∀ R, (B.val.map row).count R = (lyonsConfiguration .T).count R :=
    fun R => by rw [hM]
  obtain ⟨xa, hxa, hrxa, huxa⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 0, 0, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨xb, hxb, hrxb, huxb⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 0, 1, 1, 0)) (by rw [hcount]; decide)
  obtain ⟨xc, hxc, hrxc, huxc⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 1, 0, 0, 1)) (by rw [hcount]; decide)
  obtain ⟨xd, hxd, hrxd, huxd⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 1, 1, 0, 0)) (by rw [hcount]; decide)
  obtain ⟨ζ1, hz1, hrz1, huz1⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 1, 2, 1, 2)) (by rw [hcount]; decide)
  obtain ⟨ζ2, hz2, hrz2, huz2⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (-1, 1, 2, 1, 2, 1)) (by rw [hcount]; decide)
  obtain ⟨ha, hha, hrha, huha⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (0, 1, 0, 1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨hb, hhb, hrhb, huhb⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (0, 1, 1, 0, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨hc, hhc, hrhc, huhc⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (0, 1, 1, 1, 0, 1)) (by rw [hcount]; decide)
  obtain ⟨hd, hhd, hrhd, huhd⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (0, 1, 1, 1, 1, 0)) (by rw [hcount]; decide)
  obtain ⟨ka, hka, hrka, huka⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 0, 0, 0, 0, 1)) (by rw [hcount]; decide)
  obtain ⟨kb, hkb, hrkb, hukb⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 0, 0, 0, 1, 0)) (by rw [hcount]; decide)
  obtain ⟨kc, hkc, hrkc, hukc⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 0, 0, 1, 0, 0)) (by rw [hcount]; decide)
  obtain ⟨kd, hkd, hrkd, hukd⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 0, 1, 0, 0, 0)) (by rw [hcount]; decide)
  obtain ⟨χp, hp', hrp, hup⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := principalRow) (by rw [hcount]; decide)
  obtain ⟨χv, hv, hrv, huv⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (1, 1, 2, 2, 2, 2)) (by rw [hcount]; decide)
  obtain ⟨χw, hw, hrw, huw⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (2, 2, 1, 1, 1, 1)) (by rw [hcount]; decide)
  obtain ⟨τ, hτ, hτrow⟩ := hD.galois
  have hfxc : f xc = f xa := degree_rotate_eq τ hτ hτrow hxa (by rw [hrxc, hrxa]; decide)
    (fun φ hφ e => huxc φ hφ (e.trans hrxc))
  have hfxd : f xd = f xa := (degree_rotate_eq τ hτ hτrow hxc (by rw [hrxd, hrxc]; decide)
    (fun φ hφ e => huxd φ hφ (e.trans hrxd))).trans hfxc
  have hfxb : f xb = f xa := (degree_rotate_eq τ hτ hτrow hxd (by rw [hrxb, hrxd]; decide)
    (fun φ hφ e => huxb φ hφ (e.trans hrxb))).trans hfxd
  have hfz2 : f ζ2 = f ζ1 := degree_rotate_eq τ hτ hτrow hz1 (by rw [hrz2, hrz1]; decide)
    (fun φ hφ e => huz2 φ hφ (e.trans hrz2))
  have hfhb : f hb = f ha := degree_rotate_eq τ hτ hτrow hha (by rw [hrhb, hrha]; decide)
    (fun φ hφ e => huhb φ hφ (e.trans hrhb))
  have hfhc : f hc = f ha := (degree_rotate_eq τ hτ hτrow hhb (by rw [hrhc, hrhb]; decide)
    (fun φ hφ e => huhc φ hφ (e.trans hrhc))).trans hfhb
  have hfhd : f hd = f ha := (degree_rotate_eq τ hτ hτrow hhc (by rw [hrhd, hrhc]; decide)
    (fun φ hφ e => huhd φ hφ (e.trans hrhd))).trans hfhc
  have hfkd : f kd = f ka := degree_rotate_eq τ hτ hτrow hka (by rw [hrkd, hrka]; decide)
    (fun φ hφ e => hukd φ hφ (e.trans hrkd))
  have hfkc : f kc = f ka := (degree_rotate_eq τ hτ hτrow hkd (by rw [hrkc, hrkd]; decide)
    (fun φ hφ e => hukc φ hφ (e.trans hrkc))).trans hfkd
  have hfkb : f kb = f ka := (degree_rotate_eq τ hτ hτrow hkc (by rw [hrkb, hrkc]; decide)
    (fun φ hφ e => hukb φ hφ (e.trans hrkb))).trans hfkc
  have fxa := rowFiber_eq_singleton hxa hrxa huxa
  have fxb := rowFiber_eq_singleton hxb hrxb huxb
  have fxc := rowFiber_eq_singleton hxc hrxc huxc
  have fxd := rowFiber_eq_singleton hxd hrxd huxd
  have fz1 := rowFiber_eq_singleton hz1 hrz1 huz1
  have fz2 := rowFiber_eq_singleton hz2 hrz2 huz2
  have fha := rowFiber_eq_singleton hha hrha huha
  have fhb := rowFiber_eq_singleton hhb hrhb huhb
  have fhc := rowFiber_eq_singleton hhc hrhc huhc
  have fhd := rowFiber_eq_singleton hhd hrhd huhd
  have fka := rowFiber_eq_singleton hka hrka huka
  have fkb := rowFiber_eq_singleton hkb hrkb hukb
  have fkc := rowFiber_eq_singleton hkc hrkc hukc
  have fkd := rowFiber_eq_singleton hkd hrkd hukd
  have fv := rowFiber_eq_singleton hv hrv huv
  have fw := rowFiber_eq_singleton hw hrw huw
  have fp : rowFiber B row principalRow = {p} :=
    rowFiber_eq_singleton hD.principal_mem hD.principal_row fun ψ hψ e =>
      (hup ψ hψ e).trans (hup p hD.principal_mem hD.principal_row).symm
  have expand : ∀ (G : LyonsRow → ℚ) (H : ι → ℚ), ∑ χ ∈ B, G (row χ) * H χ =
      G (-1, 1, 0, 0, 1, 1) * H xa + G (-1, 1, 0, 1, 1, 0) * H xb +
        G (-1, 1, 1, 0, 0, 1) * H xc + G (-1, 1, 1, 1, 0, 0) * H xd +
        G (-1, 1, 1, 2, 1, 2) * H ζ1 + G (-1, 1, 2, 1, 2, 1) * H ζ2 +
        G (0, 1, 0, 1, 1, 1) * H ha + G (0, 1, 1, 0, 1, 1) * H hb +
        G (0, 1, 1, 1, 0, 1) * H hc + G (0, 1, 1, 1, 1, 0) * H hd +
        G (1, 0, 0, 0, 0, 1) * H ka + G (1, 0, 0, 0, 1, 0) * H kb +
        G (1, 0, 0, 1, 0, 0) * H kc + G (1, 0, 1, 0, 0, 0) * H kd +
        G (1, 1, 0, 0, 0, 0) * H p + G (1, 1, 2, 2, 2, 2) * H χv +
        G (2, 2, 1, 1, 1, 1) * H χw := by
    intro G H
    rw [sum_mul_row_eq hM G H]
    simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [fxa, fxb, fxc, fxd, fz1, fz2, fha, fhb, fhc, fhd, fka, fkb, fkc, fkd,
      show ((1, 1, 0, 0, 0, 0) : LyonsRow) = principalRow from rfl, fp, fv, fw]
    simp only [Finset.sum_singleton]
    ring
  have hfp : (f p : ℚ) = 1 := by rw [hD.principal_degree]; simp
  have e_u := hD.degree_sum_rat 0
  have e_a := hD.degree_sum_rat 1
  have e_b := hD.degree_sum_rat 2
  rw [expand (fun R => ((R.toVec 0 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_u
  rw [expand (fun R => ((R.toVec 1 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_a
  rw [expand (fun R => ((R.toVec 2 : ℤ) : ℚ)) (fun χ => (f χ : ℚ))] at e_b
  have r_u := hD.reciprocal_sum 0
  have r_a := hD.reciprocal_sum 1
  have r_b := hD.reciprocal_sum 2
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 0 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_u
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 1 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_a
  rw [expand (fun R => ((R.fourierSum : ℚ) ^ 2 * (R.toVec 2 : ℚ)))
    (fun χ => ((f χ : ℚ))⁻¹)] at r_b
  simp only [LyonsRow.toVec, LyonsRow.fourierSum, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.isValue, Int.cast_neg, Int.cast_one, Int.cast_ofNat, Int.cast_zero,
    hfp, hfxb, hfxc, hfxd, hfz2, hfhb, hfhc, hfhd, hfkb, hfkc, hfkd] at e_u e_a e_b r_u r_a r_b
  norm_num at e_u e_a e_b r_u r_a r_b
  have cx : f xa ≡ 51 [ZMOD 64] := by
    have := hD.residue hxa hrxa
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have ch : f ha ≡ 52 [ZMOD 64] := by
    have := hD.residue hha hrha
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have ck : f ka ≡ 1 [ZMOD 64] := by
    have := hD.residue hka hrka
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cz : f ζ1 ≡ 39 [ZMOD 64] := by
    have := hD.residue hz1 hrz1
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cv : f χv ≡ 41 [ZMOD 64] := by
    have := hD.residue hv hrv
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have cw : f χw ≡ 54 [ZMOD 64] := by
    have := hD.residue hw hrw
    simp only [LyonsRow.fourierSum] at this
    rw [Int.ModEq]; omega
  have nv : f χv < 0 → f χv ≤ -87 := fun hneg => by
    have := hD.neg_bound hv hrv hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have nw : f χw < 0 → f χw ≤ -138 := fun hneg => by
    have := hD.neg_bound hw hrw hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have hk : 12 ≤ |f ka| := hD.degree_ge ka hka (hD.ne_principal hrka (by decide))
  have hpx := hD.prime_le_of_unique hxa (hD.ne_principal hrxa (by decide))
    (unique_degree_of_unique_row hrxa huxa)
  have hph := hD.prime_le_of_unique hha (hD.ne_principal hrha (by decide))
    (unique_degree_of_unique_row hrha huha)
  have hpk := hD.prime_le_of_unique hka (hD.ne_principal hrka (by decide))
    (unique_degree_of_unique_row hrka huka)
  have hpw := hD.prime_le_of_unique hw (hD.ne_principal hrw (by decide))
    (unique_degree_of_unique_row hrw huw)
  apply lyons_T_arithmetic (f xa) (f ha) (f ka) (f ζ1) (f χv) (f χw) hk cx ch ck cz cv cw nv nw
  · intro q hqp hdvd
    rcases hdvd with hdvd | hdvd
    · exact ⟨hpx ζ1 hz1 q hqp hdvd, hph ζ1 hz1 q hqp hdvd, hpk ζ1 hz1 q hqp hdvd,
        hpw ζ1 hz1 q hqp hdvd⟩
    · exact ⟨hpx χv hv q hqp hdvd, hph χv hv q hqp hdvd, hpk χv hv q hqp hdvd,
        hpw χv hv q hqp hdvd⟩
  · simp only [div_eq_mul_inv]
    linear_combination r_u + r_a - r_b
  · simp only [div_eq_mul_inv]
    linear_combination -r_u + 2 * r_a - 2 * r_b
  · have : (1 - 2 * f ζ1 - f χv + f χw : ℚ) = 0 := by
      linear_combination e_u / 4 + 3 * e_a / 4 - e_b
    exact_mod_cast this
  · have : (1 : ℚ) + 36 / f xa + 64 / f ha + 98 / f ζ1 + 81 / f χv + 72 / f χw = P := by
      simp only [div_eq_mul_inv]
      linear_combination r_a
    rw [this]
    exact hD.P_pos

end CFSG.LyonsUnitaryFour
