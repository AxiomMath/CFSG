module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Exclusions.SignedDegreeTools
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Enumeration.NumericalUV
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {row : ι → LyonsRow} {f : ι → ℤ} {p : ι}
  {N : ℕ} {P : ℚ}

theorem lyons_signedDegree_U_endpoint (hD : LyonsSignedDegreeData B row f p N P)
    (hM : B.val.map row = lyonsConfiguration .U) :
    P = 128 / 195 ∧ ∃ χ ∈ B, row χ = (0, 0, 1, 1, 1, 1) ∧ |f χ| = 12 ∧
      ∀ ψ ∈ B, row ψ = row χ → ψ = χ := by
  have hcount : ∀ R, (B.val.map row).count R = (lyonsConfiguration .U).count R :=
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
  obtain ⟨χ7, h7, hr7, hu7⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (0, 0, 1, 1, 1, 1)) (by rw [hcount]; decide)
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
  obtain ⟨χ6, h6p, hfibP⟩ := rowFiber_eq_pair_principal hD.principal_mem hD.principal_row
    (by rw [hcount]; decide)
  have m6 : χ6 ∈ B ∧ row χ6 = principalRow := mem_rowFiber.mp (by rw [hfibP]; simp)
  obtain ⟨χ5, h5, hr5, hu5⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (2, 2, 2, 2, 2, 2)) (by rw [hcount]; decide)
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
  have f7 := rowFiber_eq_singleton h7 hr7 hu7
  have fha := rowFiber_eq_singleton hha hrha huha
  have fhb := rowFiber_eq_singleton hhb hrhb huhb
  have fhc := rowFiber_eq_singleton hhc hrhc huhc
  have fhd := rowFiber_eq_singleton hhd hrhd huhd
  have fka := rowFiber_eq_singleton hka hrka huka
  have fkb := rowFiber_eq_singleton hkb hrkb hukb
  have fkc := rowFiber_eq_singleton hkc hrkc hukc
  have fkd := rowFiber_eq_singleton hkd hrkd hukd
  have f5 := rowFiber_eq_singleton h5 hr5 hu5
  have hp6 : p ∉ ({χ6} : Finset ι) := by simpa using fun h => h6p h.symm
  have expand : ∀ (G : LyonsRow → ℚ) (H : ι → ℚ), ∑ χ ∈ B, G (row χ) * H χ =
      G (-1, 1, 0, 0, 1, 1) * H xa + G (-1, 1, 0, 1, 1, 0) * H xb +
        G (-1, 1, 1, 0, 0, 1) * H xc + G (-1, 1, 1, 1, 0, 0) * H xd +
        G (-1, 1, 1, 2, 1, 2) * H ζ1 + G (-1, 1, 2, 1, 2, 1) * H ζ2 +
        G (0, 0, 1, 1, 1, 1) * H χ7 +
        G (0, 1, 0, 1, 1, 1) * H ha + G (0, 1, 1, 0, 1, 1) * H hb +
        G (0, 1, 1, 1, 0, 1) * H hc + G (0, 1, 1, 1, 1, 0) * H hd +
        G (1, 0, 0, 0, 0, 1) * H ka + G (1, 0, 0, 0, 1, 0) * H kb +
        G (1, 0, 0, 1, 0, 0) * H kc + G (1, 0, 1, 0, 0, 0) * H kd +
        G (1, 1, 0, 0, 0, 0) * (H p + H χ6) + G (2, 2, 2, 2, 2, 2) * H χ5 := by
    intro G H
    rw [sum_mul_row_eq hM G H]
    simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [fxa, fxb, fxc, fxd, fz1, fz2, f7, fha, fhb, fhc, fhd, fka, fkb, fkc, fkd,
      show ((1, 1, 0, 0, 0, 0) : LyonsRow) = principalRow from rfl, hfibP, f5,
      Finset.sum_insert hp6]
    simp only [Finset.sum_singleton]
    ring
  have hfp : ((f p : ℚ))⁻¹ = 1 := by rw [hD.principal_degree]; simp
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
    hfp, hfxb, hfxc, hfxd, hfz2, hfhb, hfhc, hfhd, hfkb, hfkc, hfkd] at r_u r_a r_b
  norm_num at r_u r_a r_b
  have res : ∀ χ ∈ B, ∀ R : LyonsRow, row χ = R → ∀ r : ℤ,
      -(3 * R.fourierSum + 60 * R.1) ≡ r [ZMOD 64] → f χ ≡ r [ZMOD 64] := by
    intro χ hχ R hR r hr
    have := hD.residue hχ hR
    rw [Int.ModEq] at hr ⊢
    omega
  have big : ∀ χ ∈ B, ∀ R : LyonsRow, row χ = R → R ≠ principalRow → 12 ≤ |f χ| :=
    fun χ hχ R hR hRp => hD.degree_ge χ hχ (hD.ne_principal hR hRp)
  have n₅ : f χ5 < 0 → f χ5 ≤ -150 := fun hneg => by
    have := hD.neg_bound h5 hr5 hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have hpa := hD.prime_le_of_unique hxa (hD.ne_principal hrxa (by decide))
    (unique_degree_of_unique_row hrxa huxa)
  have hph := hD.prime_le_of_unique hha (hD.ne_principal hrha (by decide))
    (unique_degree_of_unique_row hrha huha)
  have hpk := hD.prime_le_of_unique hka (hD.ne_principal hrka (by decide))
    (unique_degree_of_unique_row hrka huka)
  have hpz := hD.prime_le_of_unique hz1 (hD.ne_principal hrz1 (by decide))
    (unique_degree_of_unique_row hrz1 huz1)
  have hp7 := hD.prime_le_of_unique h7 (hD.ne_principal hr7 (by decide))
    (unique_degree_of_unique_row hr7 hu7)
  have hall : ∀ ψ ∈ B, ∀ q : ℕ, q.Prime → q ∣ (f ψ).natAbs →
      (q : ℤ) ≤ |f xa| + 1 ∧ (q : ℤ) ≤ |f ha| + 1 ∧ (q : ℤ) ≤ |f ka| + 1 ∧
        (q : ℤ) ≤ |f ζ1| + 1 ∧ (q : ℤ) ≤ |f χ7| + 1 := fun ψ hψ q hq hdvd =>
    ⟨hpa ψ hψ q hq hdvd, hph ψ hψ q hq hdvd, hpk ψ hψ q hq hdvd, hpz ψ hψ q hq hdvd,
      hp7 ψ hψ q hq hdvd⟩
  have hsol := lyons_configuration_U_exact_numerical_solution (f xa) (f ha) (f ka) (f ζ1)
    (f χ5) (f χ6) (f χ7)
    (big xa hxa _ hrxa (by decide)) (big ha hha _ hrha (by decide))
    (big ka hka _ hrka (by decide)) (big ζ1 hz1 _ hrz1 (by decide))
    (big χ5 h5 _ hr5 (by decide)) (hD.degree_ge χ6 m6.1 h6p) (big χ7 h7 _ hr7 (by decide))
    (res xa hxa _ hrxa 51 (by decide)) (res ha hha _ hrha 52 (by decide))
    (res ka hka _ hrka 1 (by decide)) (res ζ1 hz1 _ hrz1 39 (by decide))
    (res χ5 h5 _ hr5 42 (by decide)) (res χ6 m6.1 _ m6.2 1 (by decide))
    (res χ7 h7 _ hr7 52 (by decide)) n₅
    (fun q hq hdvd => by
      rcases hdvd with hdvd | hdvd | hdvd | hdvd | hdvd | hdvd | hdvd
      · exact hall xa hxa q hq hdvd
      · exact hall ha hha q hq hdvd
      · exact hall ka hka q hq hdvd
      · exact hall ζ1 hz1 q hq hdvd
      · exact hall χ5 h5 q hq hdvd
      · exact hall χ6 m6.1 q hq hdvd
      · exact hall χ7 h7 q hq hdvd)
    (by simp only [div_eq_mul_inv]; linear_combination r_u)
    (by simp only [div_eq_mul_inv]; linear_combination r_a - r_b)
    (by
      have : (1 : ℚ) + 36 / f xa + 64 / f ha + 98 / f ζ1 + 200 / f χ5 + 1 / f χ6 = P := by
        simp only [div_eq_mul_inv]
        linear_combination r_a
      rw [this]
      exact hD.P_pos)
  obtain ⟨e1, e2, -, e4, e5, e6, e7⟩ := hsol
  refine ⟨?_, χ7, h7, hr7, by rw [e7]; rfl, fun ψ hψ hrow => hu7 ψ hψ (hrow.trans hr7)⟩
  rw [← r_a, e1, e2, e4, e5, e6]
  norm_num

theorem lyons_signedDegree_V_endpoint (hD : LyonsSignedDegreeData B row f p N P)
    (hM : B.val.map row = lyonsConfiguration .V) :
    P = 128 / 195 ∧ ∃ χ ∈ B, row χ = (0, 0, 1, 1, 1, 1) ∧ |f χ| = 12 ∧
      ∀ ψ ∈ B, row ψ = row χ → ψ = χ := by
  have hcount : ∀ R, (B.val.map row).count R = (lyonsConfiguration .V).count R :=
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
  obtain ⟨χ7, h7, hr7, hu7⟩ := exists_unique_of_count_eq_one (B := B) (row := row)
    (R := (0, 0, 1, 1, 1, 1)) (by rw [hcount]; decide)
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
  obtain ⟨χ6, h6p, hfibP⟩ := rowFiber_eq_pair_principal hD.principal_mem hD.principal_row
    (by rw [hcount]; decide)
  have m6 : χ6 ∈ B ∧ row χ6 = principalRow := mem_rowFiber.mp (by rw [hfibP]; simp)
  have hcard4 : (rowFiber B row (1, 1, 1, 1, 1, 1)).card = 3 + 1 := by
    rw [card_rowFiber, hcount]; decide
  obtain ⟨t1, T3, ht1T3, hinsert, hT3card⟩ := Finset.card_eq_succ.mp hcard4
  obtain ⟨t2, t3, t4, h23, h24, h34, hT3⟩ := Finset.card_eq_three.mp hT3card
  rw [hT3] at hinsert ht1T3
  have ht2 : t2 ∉ ({t3, t4} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h23, h24⟩
  have mt : ∀ t ∈ ({t1, t2, t3, t4} : Finset ι), t ∈ B ∧ row t = (1, 1, 1, 1, 1, 1) :=
    fun t ht => mem_rowFiber.mp (by rw [← hinsert]; simpa using ht)
  have mt1 := mt t1 (by simp)
  have mt2 := mt t2 (by simp)
  have mt3 := mt t3 (by simp)
  have mt4 := mt t4 (by simp)
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
  have f7 := rowFiber_eq_singleton h7 hr7 hu7
  have fha := rowFiber_eq_singleton hha hrha huha
  have fhb := rowFiber_eq_singleton hhb hrhb huhb
  have fhc := rowFiber_eq_singleton hhc hrhc huhc
  have fhd := rowFiber_eq_singleton hhd hrhd huhd
  have fka := rowFiber_eq_singleton hka hrka huka
  have fkb := rowFiber_eq_singleton hkb hrkb hukb
  have fkc := rowFiber_eq_singleton hkc hrkc hukc
  have fkd := rowFiber_eq_singleton hkd hrkd hukd
  have hp6 : p ∉ ({χ6} : Finset ι) := by simpa using fun h => h6p h.symm
  have expand : ∀ (G : LyonsRow → ℚ) (H : ι → ℚ), ∑ χ ∈ B, G (row χ) * H χ =
      G (-1, 1, 0, 0, 1, 1) * H xa + G (-1, 1, 0, 1, 1, 0) * H xb +
        G (-1, 1, 1, 0, 0, 1) * H xc + G (-1, 1, 1, 1, 0, 0) * H xd +
        G (-1, 1, 1, 2, 1, 2) * H ζ1 + G (-1, 1, 2, 1, 2, 1) * H ζ2 +
        G (0, 0, 1, 1, 1, 1) * H χ7 +
        G (0, 1, 0, 1, 1, 1) * H ha + G (0, 1, 1, 0, 1, 1) * H hb +
        G (0, 1, 1, 1, 0, 1) * H hc + G (0, 1, 1, 1, 1, 0) * H hd +
        G (1, 0, 0, 0, 0, 1) * H ka + G (1, 0, 0, 0, 1, 0) * H kb +
        G (1, 0, 0, 1, 0, 0) * H kc + G (1, 0, 1, 0, 0, 0) * H kd +
        G (1, 1, 0, 0, 0, 0) * (H p + H χ6) +
        G (1, 1, 1, 1, 1, 1) * (H t1 + (H t2 + (H t3 + H t4))) := by
    intro G H
    rw [sum_mul_row_eq hM G H]
    simp only [LyonsLabel.rows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    rw [fxa, fxb, fxc, fxd, fz1, fz2, f7, fha, fhb, fhc, fhd, fka, fkb, fkc, fkd,
      show ((1, 1, 0, 0, 0, 0) : LyonsRow) = principalRow from rfl, hfibP, ← hinsert,
      Finset.sum_insert hp6, Finset.sum_insert ht1T3, Finset.sum_insert ht2, Finset.sum_pair h34]
    simp only [Finset.sum_singleton]
    ring
  have hfp : ((f p : ℚ))⁻¹ = 1 := by rw [hD.principal_degree]; simp
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
    Matrix.cons_val_two, Fin.isValue, Int.cast_neg, Int.cast_one, Int.cast_zero, hfp, hfxb,
    hfxc, hfxd, hfz2, hfhb, hfhc, hfhd, hfkb, hfkc, hfkd] at r_u r_a r_b
  norm_num at r_u r_a r_b
  have res : ∀ χ ∈ B, ∀ R : LyonsRow, row χ = R → ∀ r : ℤ,
      -(3 * R.fourierSum + 60 * R.1) ≡ r [ZMOD 64] → f χ ≡ r [ZMOD 64] := by
    intro χ hχ R hR r hr
    have := hD.residue hχ hR
    rw [Int.ModEq] at hr ⊢
    omega
  have big : ∀ χ ∈ B, ∀ R : LyonsRow, row χ = R → R ≠ principalRow → 12 ≤ |f χ| :=
    fun χ hχ R hR hRp => hD.degree_ge χ hχ (hD.ne_principal hR hRp)
  have nt : ∀ t ∈ ({t1, t2, t3, t4} : Finset ι), f t < 0 → f t ≤ -75 := fun t ht hneg => by
    have := hD.neg_bound (mt t ht).1 (mt t ht).2 hneg
    simp only [LyonsRow.fourierSum] at this
    omega
  have hpa := hD.prime_le_of_unique hxa (hD.ne_principal hrxa (by decide))
    (unique_degree_of_unique_row hrxa huxa)
  have hph := hD.prime_le_of_unique hha (hD.ne_principal hrha (by decide))
    (unique_degree_of_unique_row hrha huha)
  have hpk := hD.prime_le_of_unique hka (hD.ne_principal hrka (by decide))
    (unique_degree_of_unique_row hrka huka)
  have hpz := hD.prime_le_of_unique hz1 (hD.ne_principal hrz1 (by decide))
    (unique_degree_of_unique_row hrz1 huz1)
  have hp7 := hD.prime_le_of_unique h7 (hD.ne_principal hr7 (by decide))
    (unique_degree_of_unique_row hr7 hu7)
  have hall : ∀ ψ ∈ B, ∀ q : ℕ, q.Prime → q ∣ (f ψ).natAbs →
      (q : ℤ) ≤ |f xa| + 1 ∧ (q : ℤ) ≤ |f ha| + 1 ∧ (q : ℤ) ≤ |f ka| + 1 ∧
        (q : ℤ) ≤ |f ζ1| + 1 ∧ (q : ℤ) ≤ |f χ7| + 1 := fun ψ hψ q hq hdvd =>
    ⟨hpa ψ hψ q hq hdvd, hph ψ hψ q hq hdvd, hpk ψ hψ q hq hdvd, hpz ψ hψ q hq hdvd,
      hp7 ψ hψ q hq hdvd⟩
  have hsol := lyons_configuration_V_exact_numerical_solution (f xa) (f ha) (f ka) (f ζ1)
    (f χ6) (f χ7) (f t1) (f t2) (f t3) (f t4)
    (big xa hxa _ hrxa (by decide)) (big ha hha _ hrha (by decide))
    (big ka hka _ hrka (by decide)) (big ζ1 hz1 _ hrz1 (by decide))
    (hD.degree_ge χ6 m6.1 h6p) (big χ7 h7 _ hr7 (by decide))
    (big t1 mt1.1 _ mt1.2 (by decide)) (big t2 mt2.1 _ mt2.2 (by decide))
    (big t3 mt3.1 _ mt3.2 (by decide)) (big t4 mt4.1 _ mt4.2 (by decide))
    (res xa hxa _ hrxa 51 (by decide)) (res ha hha _ hrha 52 (by decide))
    (res χ7 h7 _ hr7 52 (by decide)) (res ka hka _ hrka 1 (by decide))
    (res χ6 m6.1 _ m6.2 1 (by decide)) (res ζ1 hz1 _ hrz1 39 (by decide))
    (res t1 mt1.1 _ mt1.2 53 (by decide)) (res t2 mt2.1 _ mt2.2 53 (by decide))
    (res t3 mt3.1 _ mt3.2 53 (by decide)) (res t4 mt4.1 _ mt4.2 53 (by decide))
    (nt t1 (by simp)) (nt t2 (by simp)) (nt t3 (by simp)) (nt t4 (by simp))
    (fun q hq hdvd => by
      rcases hdvd with hdvd | hdvd | hdvd | hdvd | hdvd | hdvd | hdvd | hdvd | hdvd | hdvd
      · exact hall xa hxa q hq hdvd
      · exact hall ha hha q hq hdvd
      · exact hall ka hka q hq hdvd
      · exact hall ζ1 hz1 q hq hdvd
      · exact hall χ6 m6.1 q hq hdvd
      · exact hall χ7 h7 q hq hdvd
      · exact hall t1 mt1.1 q hq hdvd
      · exact hall t2 mt2.1 q hq hdvd
      · exact hall t3 mt3.1 q hq hdvd
      · exact hall t4 mt4.1 q hq hdvd)
    (by simp only [div_eq_mul_inv]; linear_combination r_u)
    (by simp only [div_eq_mul_inv]; linear_combination r_a - r_b)
    (by
      have : (1 : ℚ) + 36 / f xa + 64 / f ha + 98 / f ζ1 +
          (25 / f t1 + 25 / f t2 + 25 / f t3 + 25 / f t4) + 1 / f χ6 = P := by
        simp only [div_eq_mul_inv]
        linear_combination r_a
      rw [this]
      exact hD.P_pos)
  obtain ⟨⟨e1, e2, -, e4, e6, e7⟩, ⟨g1, g2, g3, g4⟩⟩ := hsol
  refine ⟨?_, χ7, h7, hr7, by rw [e7]; rfl, fun ψ hψ hrow => hu7 ψ hψ (hrow.trans hr7)⟩
  rw [← r_a, e1, e2, e4, e6, g1, g2, g3, g4]
  norm_num

theorem lyons_signedDegree_UV_endpoint (hD : LyonsSignedDegreeData B row f p N P)
    (hM : B.val.map row = lyonsConfiguration .U ∨ B.val.map row = lyonsConfiguration .V) :
    P = 128 / 195 ∧ ∃ χ ∈ B, row χ = (0, 0, 1, 1, 1, 1) ∧ |f χ| = 12 ∧
      ∀ ψ ∈ B, row ψ = row χ → ψ = χ := by
  rcases hM with hM | hM
  · exact lyons_signedDegree_U_endpoint hD hM
  · exact lyons_signedDegree_V_endpoint hD hM

end CFSG.LyonsUnitaryFour
