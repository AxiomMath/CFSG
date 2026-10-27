module

public import CFSG.CGT.Stroth77.Section224Extension

public section

namespace CFSG.CGT.Stroth77

open Matrix

theorem even_iff_modEq_zero_two {a : ℤ} : Even a ↔ a ≡ 0 [ZMOD 2] := by
  rw [Int.modEq_zero_iff_dvd, even_iff_two_dvd]

theorem even_iff_even_of_modEq_two {a b : ℤ} (h : a ≡ b [ZMOD 2]) : Even a ↔ Even b := by
  rw [even_iff_modEq_zero_two, even_iff_modEq_zero_two]
  exact ⟨fun ha => h.symm.trans ha, fun hb => h.trans hb⟩

theorem int_modEq_two_of_even_sub {a b : ℤ} (h : Even (b - a)) : a ≡ b [ZMOD 2] :=
  Int.modEq_iff_dvd.mpr (even_iff_two_dvd.mp h)

theorem mulVec_modEq_two {M M' : IntMat} {v w : Fin 3 → ℤ}
    (hM : ∀ i j, M i j ≡ M' i j [ZMOD 2]) (hv : ∀ i, v i ≡ w i [ZMOD 2]) (i : Fin 3) :
    (M *ᵥ v) i ≡ (M' *ᵥ w) i [ZMOD 2] := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  exact (((hM i 0).mul_right (v 0)).add ((hM i 1).mul_right (v 1))).add
    ((hM i 2).mul_right (v 2)) |>.trans
    ((((Int.ModEq.refl (M' i 0)).mul (hv 0)).add
      ((Int.ModEq.refl (M' i 1)).mul (hv 1))).add
      ((Int.ModEq.refl (M' i 2)).mul (hv 2)))

theorem theta_eq_iff_even (m : ℕ) (hm : 2 ≤ m) (M : IntMat)
    (hM : Compat (Type100.k m) M) {q : Torus (Type100.k m)} (Q : Fin 3 → ℤ)
    (hQ : q = Torus.ofInt (Type100.k m) Q) :
    (∃ d, theta m d = matAct (Type100.k m) M hM q - q) ↔
      ∀ i, Even ((M *ᵥ Q - Q) i) := by
  constructor
  · intro h i
    exact even_matVec_sub_of_theta_eq m hm M hM h Q hQ i
  · intro h
    let E : Fin 3 → ℤ := fun i => (M *ᵥ Q - Q) i / 2
    have hE : (2 : ℤ) • E = M *ᵥ Q - Q := by
      funext i
      simpa [E, Pi.smul_apply, smul_eq_mul] using Int.two_mul_ediv_two_of_even (h i)
    have hv : (2 : ℤ) • Torus.ofInt (Type100.k m) E =
        matAct (Type100.k m) M hM q - q := by
      rw [← Torus.ofInt_zsmul, hE, hQ, matAct_ofInt, Torus.ofInt_sub]
    exact exists_theta_eq_of_two_zsmul m hm ⟨Torus.ofInt (Type100.k m) E, hv⟩

theorem theta_matAct_iff_of_modEq_two (m : ℕ) (hm : 2 ≤ m) {M M' : IntMat}
    (hM : Compat (Type100.k m) M) (hM' : Compat (Type100.k m) M')
    (hmod : ∀ i j, M i j ≡ M' i j [ZMOD 2]) (q : Torus (Type100.k m)) :
    (∃ d, theta m d = matAct (Type100.k m) M hM q - q) ↔
      (∃ d, theta m d = matAct (Type100.k m) M' hM' q - q) := by
  obtain ⟨Q, hQ⟩ := Torus.exists_ofInt q
  rw [theta_eq_iff_even m hm M hM Q hQ.symm, theta_eq_iff_even m hm M' hM' Q hQ.symm]
  constructor
  · intro h i
    have hdiff : (M *ᵥ Q - Q) i ≡ (M' *ᵥ Q - Q) i [ZMOD 2] :=
      (mulVec_modEq_two hmod (fun _ => Int.ModEq.refl _) i).sub (Int.ModEq.refl (Q i))
    exact (even_iff_even_of_modEq_two hdiff).mp (h i)
  · intro h i
    have hdiff : (M *ᵥ Q - Q) i ≡ (M' *ᵥ Q - Q) i [ZMOD 2] :=
      (mulVec_modEq_two hmod (fun _ => Int.ModEq.refl _) i).sub (Int.ModEq.refl (Q i))
    exact (even_iff_even_of_modEq_two hdiff).mpr (h i)

theorem ofCols_modTwo {c a b c' a' b' : Fin 3 → ℤ}
    (hc : ∀ i, c i ≡ c' i [ZMOD 2]) (ha : ∀ i, a i ≡ a' i [ZMOD 2])
    (hb : ∀ i, b i ≡ b' i [ZMOD 2]) :
    ∀ i j, ofCols c a b i j ≡ ofCols c' a' b' i j [ZMOD 2] := by
  intro i j
  fin_cases j
  · simpa [ofCols_apply] using hc i
  · simpa [ofCols_apply] using ha i
  · simpa [ofCols_apply] using hb i

theorem uMat_last_col_modTwo {cu cu' : Fin 3 → ℤ} {κ κ' : ℤ}
    (hcu : ∀ i, cu i ≡ cu' i [ZMOD 2]) (hκ : κ ≡ κ' [ZMOD 2]) :
    ∀ i, (((![0, 1, 0] : Fin 3 → ℤ) - κ • cu) i ≡
      ((![0, 1, 0] : Fin 3 → ℤ) - κ' • cu') i [ZMOD 2]) := by
  intro i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact (Int.ModEq.refl ((![0, 1, 0] : Fin 3 → ℤ) i)).sub (hκ.mul (hcu i))

theorem uMat_modTwo_type100 {cu : Fin 3 → ℤ} {κ : ℤ}
    (hcu : ∀ i, cu i ≡ (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2])
    (hκ : κ ≡ 0 [ZMOD 2]) :
    ∀ i j, uMat cu κ i j ≡ Type100.uM i j [ZMOD 2] := by
  change ∀ i j, ofCols cu ![κ, 0, 1]
      (((![0, 1, 0] : Fin 3 → ℤ) - κ • cu)) i j ≡
    ofCols (![1, 0, 0] : Fin 3 → ℤ) ![0, 0, 1]
      (((![0, 1, 0] : Fin 3 → ℤ) - (0 : ℤ) • (![1, 0, 0] : Fin 3 → ℤ))) i j [ZMOD 2]
  refine ofCols_modTwo hcu ?_ (uMat_last_col_modTwo hcu hκ)
  intro i
  fin_cases i
  · simpa using hκ
  · exact Int.ModEq.refl _
  · exact Int.ModEq.refl _

theorem tM_modTwo_type100 {c₁ c₂ A : Fin 3 → ℤ} {ρ : IntMat}
    (hc₁ : ∀ i, c₁ i ≡ (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2])
    (hc₂ : ∀ i, c₂ i ≡ (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2])
    (hA : ∀ i, A i ≡ (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2])
    (hρ : ρ = Type100.ρM) :
    ∀ i j, ofCols c₁ c₂ (ρ *ᵥ A) i j ≡ Type100.tM i j [ZMOD 2] := by
  have hcol : ∀ i, (ρ *ᵥ A) i ≡ (Type100.ρM *ᵥ (![2, 1, 2] : Fin 3 → ℤ)) i [ZMOD 2] := by
    subst hρ
    intro i
    exact mulVec_modEq_two (fun _ _ => Int.ModEq.refl _) hA i
  simpa only [Type100.tM, Type100.uvA] using ofCols_modTwo hc₁ hc₂ hcol

theorem uvM_modTwo_type100 {u A : Fin 3 → ℤ} {ρ tM : IntMat}
    (hu : ∀ i, u i ≡ (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2])
    (hA : ∀ i, A i ≡ (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2])
    (hρ : ρ = Type100.ρM)
    (ht : ∀ i j, tM i j ≡ Type100.tM i j [ZMOD 2]) :
    ∀ i j, ofCols u A (ρ *ᵥ (tM *ᵥ A)) i j ≡ Type100.uvM i j [ZMOD 2] := by
  have hcol : ∀ i, (ρ *ᵥ (tM *ᵥ A)) i ≡
      (Type100.ρM *ᵥ (Type100.tM *ᵥ (![2, 1, 2] : Fin 3 → ℤ))) i [ZMOD 2] := by
    subst hρ
    have htA : ∀ i, (tM *ᵥ A) i ≡ (Type100.tM *ᵥ (![2, 1, 2] : Fin 3 → ℤ)) i [ZMOD 2] :=
      fun i => mulVec_modEq_two ht hA i
    intro i
    exact mulVec_modEq_two (fun _ _ => Int.ModEq.refl _) htA i
  simpa only [Type100.uvM, Type100.uvA, Type100.tM] using ofCols_modTwo hu hA hcol

theorem modTwo_t100 (m : ℕ) :
    (∀ i j, (StrothTypeIndex.t100 m).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t100 m).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t100 m).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t100 m).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) :=
  ⟨fun _ _ => Int.ModEq.refl _, fun _ _ => Int.ModEq.refl _,
    fun _ _ => Int.ModEq.refl _, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t101 (s : ℕ) :
    (∀ i j, (StrothTypeIndex.t101 s).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t101 s).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t101 s).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t101 s).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  have hA : ∀ i, Type101.uvA s i ≡ (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type101.uvA]
  have hc₂ : ∀ i, (![0, -1 + 2 ^ (s + 1), 0] : Fin 3 → ℤ) i ≡
      (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have htM : ∀ i j, Type101.tM s i j ≡ Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![1, 2, 0]) (c₂ := ![0, -1 + 2 ^ (s + 1), 0])
      (A := Type101.uvA s) (ρ := Type101.ρM s) (fun i => Int.ModEq.refl _) hc₂ hA rfl
    simpa only [Type101.tM] using h
  have huvM : ∀ i j, Type101.uvM s i j ≡ Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-3, -2, -2]) (A := Type101.uvA s)
      (ρ := Type101.ρM s) (tM := Type101.tM s) (fun i => Int.ModEq.refl _) hA rfl htM
    simpa only [Type101.uvM] using h
  have huM : ∀ i j, Type101.uM s i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![1, 0, 0]) (κ := 0)
      (fun i => Int.ModEq.refl _) (Int.ModEq.refl (0 : ℤ))
    simpa only [Type101.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t110 (t : ℕ) :
    (∀ i j, (StrothTypeIndex.t110 t).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t110 t).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t110 t).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t110 t).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  have hu : ∀ i, (![-3, -2 + 2 ^ (t + 2), -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have hc₁ : ∀ i, (![1, 2, 2 ^ (t + 2)] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have htM : ∀ i j, Type110.tM t i j ≡ Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![1, 2, 2 ^ (t + 2)]) (c₂ := ![0, -1, 0])
      (A := Type110.uvA t) (ρ := Type110.ρM t)
      hc₁ (fun i => Int.ModEq.refl _) (fun i => Int.ModEq.refl _) rfl
    simpa only [Type110.tM] using h
  have huvM : ∀ i j, Type110.uvM t i j ≡ Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-3, -2 + 2 ^ (t + 2), -2]) (A := Type110.uvA t)
      (ρ := Type110.ρM t) (tM := Type110.tM t)
      hu (fun i => Int.ModEq.refl _) rfl htM
    simpa only [Type110.uvM] using h
  have hcu : ∀ i, (![1 + 2 ^ (t + 1), 0, 0] : Fin 3 → ℤ) i ≡
      (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have huM : ∀ i j, Type110.uM t i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![1 + 2 ^ (t + 1), 0, 0]) (κ := 0)
      hcu (Int.ModEq.refl (0 : ℤ))
    simpa only [Type110.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t111 (t : ℕ) :
    (∀ i j, (StrothTypeIndex.t111 t).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t111 t).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t111 t).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t111 t).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  have hu : ∀ i, (![-3, -2 + 2 ^ (t + 2), -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have hA : ∀ i, Type111.uvA t i ≡ (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type111.uvA]
  have hc₁ : ∀ i, (![1, 2, 2 ^ (t + 2)] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have hc₂ : ∀ i, (![0, -1 + 2 ^ (t + 2), 0] : Fin 3 → ℤ) i ≡
      (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have htM : ∀ i j, Type111.tM t i j ≡ Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![1, 2, 2 ^ (t + 2)])
      (c₂ := ![0, -1 + 2 ^ (t + 2), 0]) (A := Type111.uvA t) (ρ := Type111.ρM t)
      hc₁ hc₂ hA rfl
    simpa only [Type111.tM] using h
  have huvM : ∀ i j, Type111.uvM t i j ≡ Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-3, -2 + 2 ^ (t + 2), -2]) (A := Type111.uvA t)
      (ρ := Type111.ρM t) (tM := Type111.tM t)
      hu hA rfl htM
    simpa only [Type111.uvM] using h
  have hcu : ∀ i, (![1 + 2 ^ (t + 1), 0, 0] : Fin 3 → ℤ) i ≡
      (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have huM : ∀ i j, Type111.uM t i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![1 + 2 ^ (t + 1), 0, 0]) (κ := 0)
      hcu (Int.ModEq.refl (0 : ℤ))
    simpa only [Type111.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t120 (m : ℕ) (hm : 3 ≤ m) :
    (∀ i j, (StrothTypeIndex.t120 m hm).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t120 m hm).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t120 m hm).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t120 m hm).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  obtain ⟨hi, hF, -⟩ := Type120.data m (by omega)
  have hu : ∀ i, (![-Type120.iV (m + 1), 2, -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have hA : ∀ i, Type120.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) i ≡
      (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type120.uvA]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type120.uvA, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type120.uvA]
  have hc₁ : ∀ i, (![4 - Type120.iV (m + 1), 2, 4] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have hc₂ : ∀ i,
      (![4 * Type120.GV (m + 1) * Type120.iV (m + 1), -7 * Type120.iV (m + 1),
        -8 * Type120.iV (m + 1)] : Fin 3 → ℤ) i ≡ (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have htM : ∀ i j,
      Type120.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) i j ≡
        Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![4 - Type120.iV (m + 1), 2, 4])
      (c₂ := ![4 * Type120.GV (m + 1) * Type120.iV (m + 1), -7 * Type120.iV (m + 1),
        -8 * Type120.iV (m + 1)])
      (A := Type120.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1))) (ρ := Type120.ρM)
      hc₁ hc₂ hA rfl
    simpa only [Type120.tM] using h
  have huvM : ∀ i j,
      Type120.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) i j ≡
        Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-Type120.iV (m + 1), 2, -2])
      (A := Type120.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1))) (ρ := Type120.ρM)
      (tM := Type120.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)))
      hu hA rfl htM
    simpa only [Type120.uvM] using h
  have hcu : ∀ i, (![-1, 0, 0] : Fin 3 → ℤ) i ≡ (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have hκ : (-4 * Type120.FV (m + 1) : ℤ) ≡ 0 [ZMOD 2] := by
    apply int_modEq_two_of_even_sub
    simp +decide [parity_simps]
  have huM : ∀ i j, Type120.uM (Type120.FV (m + 1)) i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![-1, 0, 0]) (κ := -4 * Type120.FV (m + 1)) hcu hκ
    simpa only [Type120.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t121 (m : ℕ) (hm : 3 ≤ m) :
    (∀ i j, (StrothTypeIndex.t121 m hm).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t121 m hm).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t121 m hm).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t121 m hm).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  obtain ⟨hi, hF, -, hK, -⟩ := Type121.data m (by omega)
  have hu : ∀ i, (![-Type120.iV (m + 1), 2, -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
  have hA : ∀ i, Type121.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m) i ≡
      (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type121.uvA]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type121.uvA, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type121.uvA, hK]
  have hc₁ : ∀ i, (![4 - Type120.iV (m + 1), 2, 4] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have hc₂ : ∀ i,
      (![4 * Type120.GV (m + 1) * Type120.iV (m + 1),
        -7 * Type120.iV (m + 1) + 2 ^ m,
        -8 * Type120.iV (m + 1)] : Fin 3 → ℤ) i ≡ (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi, hK]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have htM : ∀ i j,
      Type121.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![4 - Type120.iV (m + 1), 2, 4])
      (c₂ := ![4 * Type120.GV (m + 1) * Type120.iV (m + 1),
        -7 * Type120.iV (m + 1) + 2 ^ m, -8 * Type120.iV (m + 1)])
      (A := Type121.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m))
      (ρ := Type121.ρM) hc₁ hc₂ hA rfl
    simpa only [Type121.tM] using h
  have huvM : ∀ i j,
      Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-Type120.iV (m + 1), 2, -2])
      (A := Type121.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m))
      (ρ := Type121.ρM)
      (tM := Type121.tM (Type120.iV (m + 1)) (Type120.FV (m + 1))
        (Type120.GV (m + 1)) (2 ^ m))
      hu hA rfl htM
    simpa only [Type121.uvM] using h
  have hcu : ∀ i, (![-1, 0, 0] : Fin 3 → ℤ) i ≡ (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have hκ : (-4 * Type120.FV (m + 1) : ℤ) ≡ 0 [ZMOD 2] := by
    apply int_modEq_two_of_even_sub
    simp +decide [parity_simps]
  have huM : ∀ i j, Type121.uM (Type120.FV (m + 1)) i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![-1, 0, 0]) (κ := -4 * Type120.FV (m + 1)) hcu hκ
    simpa only [Type121.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t130 (m : ℕ) (hm : 3 ≤ m) :
    (∀ i j, (StrothTypeIndex.t130 m hm).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t130 m hm).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t130 m hm).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t130 m hm).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := Type130.data m (by omega)
  have hu : ∀ i, (![-Type120.iV (m + 1), 2 + 2 ^ m, -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hK]
    · exact Int.ModEq.refl _
  have hA : ∀ i, Type130.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) i ≡
      (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type130.uvA]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type130.uvA, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type130.uvA]
  have hc₁ : ∀ i, (![4 - Type120.iV (m + 1), 2, 4 + 2 ^ m] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hK]
  have hc₂ : ∀ i,
      (![4 * Type120.GV (m + 1) * Type120.iV (m + 1), -7 * Type120.iV (m + 1),
        -8 * Type120.iV (m + 1)] : Fin 3 → ℤ) i ≡ (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have htM : ∀ i j,
      Type130.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![4 - Type120.iV (m + 1), 2, 4 + 2 ^ m])
      (c₂ := ![4 * Type120.GV (m + 1) * Type120.iV (m + 1), -7 * Type120.iV (m + 1),
        -8 * Type120.iV (m + 1)])
      (A := Type130.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1))) (ρ := Type130.ρM)
      hc₁ hc₂ hA rfl
    simpa only [Type130.tM] using h
  have huvM : ∀ i j,
      Type130.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-Type120.iV (m + 1), 2 + 2 ^ m, -2])
      (A := Type130.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1))) (ρ := Type130.ρM)
      (tM := Type130.tM (Type120.iV (m + 1)) (Type120.FV (m + 1))
        (Type120.GV (m + 1)) (2 ^ m))
      hu hA rfl htM
    simpa only [Type130.uvM] using h
  have hcu : ∀ i, (![-1 + 2 ^ (m - 1), 0, 0] : Fin 3 → ℤ) i ≡
      (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hJ]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have hκ : (-4 * Type120.FV (m + 1) : ℤ) ≡ 0 [ZMOD 2] := by
    apply int_modEq_two_of_even_sub
    simp +decide [parity_simps]
  have huM : ∀ i j,
      Type130.uM (Type120.FV (m + 1)) (2 ^ (m - 1)) i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![-1 + 2 ^ (m - 1), 0, 0])
      (κ := -4 * Type120.FV (m + 1)) hcu hκ
    simpa only [Type130.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

theorem modTwo_t131 (m : ℕ) (hm : 3 ≤ m) :
    (∀ i j, (StrothTypeIndex.t131 m hm).action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t131 m hm).action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t131 m hm).action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
    (∀ i j, (StrothTypeIndex.t131 m hm).action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
  obtain ⟨hi, hF, -, hK, hJ, -⟩ := Type131.data m (by omega)
  have hu : ∀ i, (![-Type120.iV (m + 1), 2 + 2 ^ m, -2] : Fin 3 → ℤ) i ≡
      (![-3, -2, -2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hK]
    · exact Int.ModEq.refl _
  have hA : ∀ i, Type131.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m) i ≡
      (![2, 1, 2] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type131.uvA]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type131.uvA, hi]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, Type131.uvA, hK]
  have hc₁ : ∀ i, (![4 - Type120.iV (m + 1), 2, 4 + 2 ^ m] : Fin 3 → ℤ) i ≡
      (![1, 2, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi]
    · exact Int.ModEq.refl _
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hK]
  have hc₂ : ∀ i,
      (![4 * Type120.GV (m + 1) * Type120.iV (m + 1),
        -7 * Type120.iV (m + 1) + 2 ^ m,
        -8 * Type120.iV (m + 1)] : Fin 3 → ℤ) i ≡ (![0, -1, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hi, hK]
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps]
  have htM : ∀ i j,
      Type131.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.tM i j [ZMOD 2] := by
    have h := tM_modTwo_type100 (c₁ := ![4 - Type120.iV (m + 1), 2, 4 + 2 ^ m])
      (c₂ := ![4 * Type120.GV (m + 1) * Type120.iV (m + 1),
        -7 * Type120.iV (m + 1) + 2 ^ m, -8 * Type120.iV (m + 1)])
      (A := Type131.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m))
      (ρ := Type131.ρM) hc₁ hc₂ hA rfl
    simpa only [Type131.tM] using h
  have huvM : ∀ i j,
      Type131.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m) i j ≡
        Type100.uvM i j [ZMOD 2] := by
    have h := uvM_modTwo_type100 (u := ![-Type120.iV (m + 1), 2 + 2 ^ m, -2])
      (A := Type131.uvA (Type120.iV (m + 1)) (Type120.FV (m + 1)) (2 ^ m))
      (ρ := Type131.ρM)
      (tM := Type131.tM (Type120.iV (m + 1)) (Type120.FV (m + 1))
        (Type120.GV (m + 1)) (2 ^ m))
      hu hA rfl htM
    simpa only [Type131.uvM] using h
  have hcu : ∀ i, (![-1 + 2 ^ (m - 1), 0, 0] : Fin 3 → ℤ) i ≡
      (![1, 0, 0] : Fin 3 → ℤ) i [ZMOD 2] := by
    intro i
    fin_cases i
    · apply int_modEq_two_of_even_sub
      simp +decide [parity_simps, hJ]
    · exact Int.ModEq.refl _
    · exact Int.ModEq.refl _
  have hκ : (-4 * Type120.FV (m + 1) : ℤ) ≡ 0 [ZMOD 2] := by
    apply int_modEq_two_of_even_sub
    simp +decide [parity_simps]
  have huM : ∀ i j,
      Type131.uM (Type120.FV (m + 1)) (2 ^ (m - 1)) i j ≡ Type100.uM i j [ZMOD 2] := by
    have h := uMat_modTwo_type100 (cu := ![-1 + 2 ^ (m - 1), 0, 0])
      (κ := -4 * Type120.FV (m + 1)) hcu hκ
    simpa only [Type131.uM] using h
  exact ⟨huvM, htM, huM, fun _ _ => Int.ModEq.refl _⟩

@[expose] def thetaType : (τ : StrothTypeIndex) → Torus τ.k →+ Torus τ.k
  | StrothTypeIndex.t100 m => theta m
  | StrothTypeIndex.t101 s => theta (s + 1)
  | StrothTypeIndex.t110 t => theta (t + 2)
  | StrothTypeIndex.t111 t => theta (t + 2)
  | StrothTypeIndex.t120 m _ => theta m
  | StrothTypeIndex.t121 m _ => theta m
  | StrothTypeIndex.t130 m _ => theta m
  | StrothTypeIndex.t131 m _ => theta m
  | _ => 0

theorem square_class_dichotomy_uniform (τ : StrothTypeIndex) (hk : ∀ i, 2 ≤ τ.k i)
    (hrel : τ.m + 1 = τ.n) (q : Torus τ.k)
    (huv : ∃ d, thetaType τ d = matAct τ.k τ.action.uv τ.action.compat_uv q - q)
    (ht : ∃ d, thetaType τ d = matAct τ.k τ.action.t τ.action.compat_t q - q)
    (hu : ∃ d, thetaType τ d = matAct τ.k τ.action.u τ.action.compat_u q - q)
    (hρ : ∃ d, thetaType τ d = matAct τ.k τ.action.ρ τ.action.compat_ρ q - q) :
    (∃ d, thetaType τ d = q) ∨ (∃ d, thetaType τ d = q - gen τ.k 0) := by
  cases τ with
  | t100 m =>
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type100.k] using hk 0
    exact square_class_dichotomy m hm2 q huv ht hu hρ
  | t101 s =>
    have hm2 : 2 ≤ s + 1 := by simpa [StrothTypeIndex.k, Type101.k] using hk 0
    obtain ⟨huv', ht', hu', hρ'⟩ := modTwo_t101 s
    exact square_class_dichotomy (s + 1) hm2 q
      ((theta_matAct_iff_of_modEq_two (s + 1) hm2
        (StrothTypeIndex.t101 s).action.compat_uv (Type100.compat_uv (s + 1)) huv' q).mp huv)
      ((theta_matAct_iff_of_modEq_two (s + 1) hm2
        (StrothTypeIndex.t101 s).action.compat_t (Type100.compat_t (s + 1)) ht' q).mp ht)
      ((theta_matAct_iff_of_modEq_two (s + 1) hm2
        (StrothTypeIndex.t101 s).action.compat_u (Type100.compat_u (s + 1)) hu' q).mp hu)
      ((theta_matAct_iff_of_modEq_two (s + 1) hm2
        (StrothTypeIndex.t101 s).action.compat_ρ (Type100.compat_rho (s + 1)) hρ' q).mp hρ)
  | t110 t =>
    have hm2 : 2 ≤ t + 2 := by simpa [StrothTypeIndex.k, Type110.k] using hk 0
    obtain ⟨huv', ht', hu', hρ'⟩ := modTwo_t110 t
    exact square_class_dichotomy (t + 2) hm2 q
      ((theta_matAct_iff_of_modEq_two (t + 2) hm2
        (StrothTypeIndex.t110 t).action.compat_uv (Type100.compat_uv (t + 2)) huv' q).mp huv)
      ((theta_matAct_iff_of_modEq_two (t + 2) hm2
        (StrothTypeIndex.t110 t).action.compat_t (Type100.compat_t (t + 2)) ht' q).mp ht)
      ((theta_matAct_iff_of_modEq_two (t + 2) hm2
        (StrothTypeIndex.t110 t).action.compat_u (Type100.compat_u (t + 2)) hu' q).mp hu)
      ((theta_matAct_iff_of_modEq_two (t + 2) hm2
        (StrothTypeIndex.t110 t).action.compat_ρ (Type100.compat_rho (t + 2)) hρ' q).mp hρ)
  | t111 t =>
    have hm2 : 2 ≤ t + 2 := by simpa [StrothTypeIndex.k, Type111.k] using hk 0
    obtain ⟨huv', ht', hu', hρ'⟩ := modTwo_t111 t
    exact square_class_dichotomy (t + 2) hm2 q
      ((theta_matAct_iff_of_modEq_two (t + 2) hm2
        (StrothTypeIndex.t111 t).action.compat_uv (Type100.compat_uv (t + 2)) huv' q).mp huv)
      ((theta_matAct_iff_of_modEq_two (t + 2) hm2
        (StrothTypeIndex.t111 t).action.compat_t (Type100.compat_t (t + 2)) ht' q).mp ht)
      ((theta_matAct_iff_of_modEq_two (t + 2) hm2
        (StrothTypeIndex.t111 t).action.compat_u (Type100.compat_u (t + 2)) hu' q).mp hu)
      ((theta_matAct_iff_of_modEq_two (t + 2) hm2
        (StrothTypeIndex.t111 t).action.compat_ρ (Type100.compat_rho (t + 2)) hρ' q).mp hρ)
  | t120 m hm =>
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type120.k] using hk 0
    obtain ⟨huv', ht', hu', hρ'⟩ := modTwo_t120 m hm
    exact square_class_dichotomy m hm2 q
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t120 m hm).action.compat_uv (Type100.compat_uv m) huv' q).mp huv)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t120 m hm).action.compat_t (Type100.compat_t m) ht' q).mp ht)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t120 m hm).action.compat_u (Type100.compat_u m) hu' q).mp hu)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t120 m hm).action.compat_ρ (Type100.compat_rho m) hρ' q).mp hρ)
  | t121 m hm =>
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type121.k] using hk 0
    obtain ⟨huv', ht', hu', hρ'⟩ := modTwo_t121 m hm
    exact square_class_dichotomy m hm2 q
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t121 m hm).action.compat_uv (Type100.compat_uv m) huv' q).mp huv)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t121 m hm).action.compat_t (Type100.compat_t m) ht' q).mp ht)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t121 m hm).action.compat_u (Type100.compat_u m) hu' q).mp hu)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t121 m hm).action.compat_ρ (Type100.compat_rho m) hρ' q).mp hρ)
  | t130 m hm =>
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type130.k] using hk 0
    obtain ⟨huv', ht', hu', hρ'⟩ := modTwo_t130 m hm
    exact square_class_dichotomy m hm2 q
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t130 m hm).action.compat_uv (Type100.compat_uv m) huv' q).mp huv)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t130 m hm).action.compat_t (Type100.compat_t m) ht' q).mp ht)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t130 m hm).action.compat_u (Type100.compat_u m) hu' q).mp hu)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t130 m hm).action.compat_ρ (Type100.compat_rho m) hρ' q).mp hρ)
  | t131 m hm =>
    have hm2 : 2 ≤ m := by simpa [StrothTypeIndex.k, Type131.k] using hk 0
    obtain ⟨huv', ht', hu', hρ'⟩ := modTwo_t131 m hm
    exact square_class_dichotomy m hm2 q
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t131 m hm).action.compat_uv (Type100.compat_uv m) huv' q).mp huv)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t131 m hm).action.compat_t (Type100.compat_t m) ht' q).mp ht)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t131 m hm).action.compat_u (Type100.compat_u m) hu' q).mp hu)
      ((theta_matAct_iff_of_modEq_two m hm2
        (StrothTypeIndex.t131 m hm).action.compat_ρ (Type100.compat_rho m) hρ' q).mp hρ)
  | t200 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type200.k] at hrel
  | t201 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type201.k] at hrel
  | t210 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type210.k] at hrel
  | t211 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type211.k] at hrel
  | t220 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type220.k] at hrel
  | t221 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type221.k] at hrel
  | t230 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type230.k] at hrel
  | t231 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type231.k] at hrel
  | t300 n =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type300.k] at hrel
  | t310 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type310.k] at hrel
  | t320 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type320.k,
      Type32x.k] at hrel
  | t330 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type330.k,
      Type32x.k] at hrel
  | t321 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type321.k] at hrel
  | t331 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type331.k] at hrel

theorem action_rho_eq_type100 (τ : StrothTypeIndex) (hrel : τ.m + 1 = τ.n) :
    τ.action.ρ = Type100.ρM := by
  cases τ with
  | t100 m => rfl
  | t101 s => rfl
  | t110 t => rfl
  | t111 t => rfl
  | t120 m hm => rfl
  | t121 m hm => rfl
  | t130 m hm => rfl
  | t131 m hm => rfl
  | t200 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type200.k] at hrel
  | t201 m =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type201.k] at hrel
  | t210 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type210.k] at hrel
  | t211 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type211.k] at hrel
  | t220 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type220.k] at hrel
  | t221 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type221.k] at hrel
  | t230 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type230.k] at hrel
  | t231 s hs =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type231.k] at hrel
  | t300 n =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type300.k] at hrel
  | t310 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type310.k] at hrel
  | t320 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type320.k,
      Type32x.k] at hrel
  | t330 m hm =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type330.k,
      Type32x.k] at hrel
  | t321 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type321.k] at hrel
  | t331 =>
    exfalso
    simp [StrothTypeIndex.m, StrothTypeIndex.n, StrothTypeIndex.k, Type331.k] at hrel

theorem map_rho_sub_omegaOne (m : ℕ) (hm : 2 ≤ m) :
    AddSubgroup.map ((Type100.action m).φρ - AddMonoidHom.id (Torus (Type100.k m)))
      (AddSubgroup.closure ({ (2 : ℤ) • Torus.c, (2 : ℤ) ^ m • Torus.a,
        (2 : ℤ) ^ m • Torus.b } : Set (Torus (Type100.k m))))
      = AddSubgroup.closure ({ (2 : ℤ) ^ m • Torus.a, (2 : ℤ) ^ m • Torus.b } :
        Set (Torus (Type100.k m))) := by
  let f : Torus (Type100.k m) →+ Torus (Type100.k m) :=
    (Type100.action m).φρ - AddMonoidHom.id _
  let Ω : AddSubgroup (Torus (Type100.k m)) :=
    AddSubgroup.closure ({ (2 : ℤ) • Torus.c, (2 : ℤ) ^ m • Torus.a,
      (2 : ℤ) ^ m • Torus.b } : Set (Torus (Type100.k m)))
  let W : AddSubgroup (Torus (Type100.k m)) :=
    AddSubgroup.closure ({ (2 : ℤ) ^ m • Torus.a, (2 : ℤ) ^ m • Torus.b } :
      Set (Torus (Type100.k m)))
  change AddSubgroup.map f Ω = W
  have hf_ofInt (v : Fin 3 → ℤ) :
      f (Torus.ofInt (Type100.k m) v) =
        Torus.ofInt (Type100.k m) (Type100.ρM *ᵥ v - v) := by
    dsimp [f]
    rw [matAct_ofInt, Torus.ofInt_sub]
    rfl
  have hc_coord : (2 : ℤ) • Torus.c = Torus.ofInt (Type100.k m) ![2, 0, 0] := by
    have h : Torus.c = Torus.ofInt (Type100.k m) (![1, 0, 0] : Fin 3 → ℤ) := by
      rw [Torus.ofInt_eq_zsmul_gens]
      simp [Torus.c]
    rw [h, ← Torus.ofInt_zsmul]
    congr 1
    funext i
    fin_cases i <;> simp
  have ha_coord : (2 : ℤ) ^ m • Torus.a =
      Torus.ofInt (Type100.k m) ![0, (2 : ℤ) ^ m, 0] := by
    have h : Torus.a = Torus.ofInt (Type100.k m) (![0, 1, 0] : Fin 3 → ℤ) := by
      rw [Torus.ofInt_eq_zsmul_gens]
      simp [Torus.a]
    rw [h, ← Torus.ofInt_zsmul]
    congr 1
    funext i
    fin_cases i <;> simp
  have hb_coord : (2 : ℤ) ^ m • Torus.b =
      Torus.ofInt (Type100.k m) ![0, 0, (2 : ℤ) ^ m] := by
    have h : Torus.b = Torus.ofInt (Type100.k m) (![0, 0, 1] : Fin 3 → ℤ) := by
      rw [Torus.ofInt_eq_zsmul_gens]
      simp [Torus.b]
    rw [h, ← Torus.ofInt_zsmul]
    congr 1
    funext i
    fin_cases i <;> simp
  have hfc : f ((2 : ℤ) • Torus.c) = 0 := by
    rw [hc_coord, hf_ofInt]
    apply Torus.ofInt_eq_zero_iff.mpr
    intro i
    fin_cases i <;>
      simp [Type100.ρM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hfa : f ((2 : ℤ) ^ m • Torus.a) =
      (2 : ℤ) ^ m • Torus.b - (2 : ℤ) ^ m • Torus.a := by
    calc f ((2 : ℤ) ^ m • Torus.a)
        = Torus.ofInt (Type100.k m)
            (Type100.ρM *ᵥ (![0, (2 : ℤ) ^ m, 0] : Fin 3 → ℤ) -
              ![0, (2 : ℤ) ^ m, 0]) := by
          rw [ha_coord, hf_ofInt]
      _ = Torus.ofInt (Type100.k m) ![0, 0, (2 : ℤ) ^ m] -
          Torus.ofInt (Type100.k m) ![0, (2 : ℤ) ^ m, 0] := by
          rw [← Torus.ofInt_sub]
          congr 1
          funext i
          fin_cases i <;>
            simp [Type100.ρM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      _ = (2 : ℤ) ^ m • Torus.b - (2 : ℤ) ^ m • Torus.a := by
          rw [hb_coord, ha_coord]
  have hfb : f ((2 : ℤ) ^ m • Torus.b) = -((2 : ℤ) ^ m • Torus.a) := by
    calc f ((2 : ℤ) ^ m • Torus.b)
        = Torus.ofInt (Type100.k m)
            (Type100.ρM *ᵥ (![0, 0, (2 : ℤ) ^ m] : Fin 3 → ℤ) -
              ![0, 0, (2 : ℤ) ^ m]) := by
          rw [hb_coord, hf_ofInt]
      _ = -Torus.ofInt (Type100.k m) ![0, (2 : ℤ) ^ m, 0] := by
          rw [← Torus.ofInt_neg]
          apply Torus.ofInt_eq_ofInt_iff.mpr
          intro i
          fin_cases i <;>
            simp [Type100.ρM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Type100.k]
          · rw [Int.modEq_zero_iff_dvd]
            exact dvd_neg.mpr (dvd_mul_right ((2 : ℤ) ^ m) 2)
          · rw [Int.modEq_zero_iff_dvd]
            have hp : (2 : ℤ) ^ (m + 1) = (2 : ℤ) ^ m + (2 : ℤ) ^ m := by
              rw [pow_succ]; ring
            rw [hp]
            rw [show -(2 : ℤ) ^ m - (2 : ℤ) ^ m =
              -((2 : ℤ) ^ m + (2 : ℤ) ^ m) by ring]
            exact dvd_neg.mpr (dvd_refl ((2 : ℤ) ^ m + (2 : ℤ) ^ m))
      _ = -((2 : ℤ) ^ m • Torus.a) := by rw [ha_coord]
  apply le_antisymm
  · rw [AddSubgroup.map_le_iff_le_comap, AddSubgroup.closure_le]
    intro x hx
    change f x ∈ W
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [hfc]; exact W.zero_mem
    · rw [hfa]
      exact W.sub_mem (AddSubgroup.subset_closure (by simp))
        (AddSubgroup.subset_closure (by simp))
    · rw [hfb]
      exact W.neg_mem (AddSubgroup.subset_closure (by simp))
  · rw [AddSubgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have h2ma_mem : (2 : ℤ) ^ m • Torus.a ∈ Ω :=
      AddSubgroup.subset_closure (by simp)
    have h2mb_mem : (2 : ℤ) ^ m • Torus.b ∈ Ω :=
      AddSubgroup.subset_closure (by simp)
    rcases hx with rfl | rfl
    · refine AddSubgroup.mem_map.mpr ⟨-((2 : ℤ) ^ m • Torus.b), Ω.neg_mem h2mb_mem, ?_⟩
      rw [map_neg, hfb, neg_neg]
    · refine AddSubgroup.mem_map.mpr
        ⟨(2 : ℤ) ^ m • Torus.a - (2 : ℤ) ^ m • Torus.b, Ω.sub_mem h2ma_mem h2mb_mem, ?_⟩
      rw [map_sub, hfa, hfb]
      abel

end CFSG.CGT.Stroth77
