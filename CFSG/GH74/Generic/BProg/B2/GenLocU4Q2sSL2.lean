module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped MatrixGroups

namespace GenLocU4Q2sSL2

variable {K : Type} [Field K]

@[expose] def upperDiag (l c : K) (hl : l ≠ 0) : SL(2, K) :=
  ⟨!![l, c * (l - l⁻¹); 0, l⁻¹], by rw [det_fin_two_of]; simp [hl]⟩

theorem coe_upperDiag (l c : K) (hl : l ≠ 0) :
    (upperDiag l c hl : Matrix (Fin 2) (Fin 2) K) = !![l, c * (l - l⁻¹); 0, l⁻¹] := rfl

section Bar

variable (bar : K →+* K)

theorem transport {k kinv A S : Matrix (Fin 2) (Fin 2) K} (hk : k.map bar = k) (hkinv : kinv.map bar = kinv)
    (h1 : k * kinv = 1) (hA : (A.map bar)ᵀ * (kᵀ * S * k) * A = kᵀ * S * k) :
    ((k * A * kinv).map bar)ᵀ * S * (k * A * kinv) = S := by
  rw [Matrix.map_mul, Matrix.map_mul, hk, hkinv, Matrix.transpose_mul, Matrix.transpose_mul]
  calc _ = kinvᵀ * ((A.map bar)ᵀ * (kᵀ * S * k) * A) * kinv := by simp only [Matrix.mul_assoc]
    _ = kinvᵀ * (kᵀ * S * k) * kinv := by rw [hA]
    _ = (k * kinv)ᵀ * S * (k * kinv) := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = S := by rw [h1]; simp

theorem exists_decomp (hbb : ∀ c, bar (bar c) = c) {m : K} (hm : m ≠ bar m) (t : K) :
    ∃ t₁ t₂ : K, bar t₁ = t₁ ∧ bar t₂ = t₂ ∧ t = t₁ + m * t₂ := by
  have hne : m - bar m ≠ 0 := sub_ne_zero.2 hm
  have hne' : bar m - m ≠ 0 := fun h => hne (by linear_combination -h)
  have hx : bar ((t - bar t) / (m - bar m)) = (t - bar t) / (m - bar m) := by
    rw [map_div₀, map_sub, map_sub, hbb, hbb]
    field_simp
    ring
  refine ⟨t - m * ((t - bar t) / (m - bar m)), (t - bar t) / (m - bar m), ?_, hx, by ring⟩
  rw [map_sub, map_mul, hx]
  have : (m - bar m) * ((t - bar t) / (m - bar m)) = t - bar t := by field_simp
  linear_combination this

theorem core_aniso (hbb : ∀ c, bar (bar c) = c) (H : Subgroup SL(2, K))
    (hreal : ∀ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K).map bar = A → A ∈ H)
    (S : Matrix (Fin 2) (Fin 2) K) (hS : (S.map bar)ᵀ = -S) (h00 : S 0 0 ≠ 0)
    (hSU : ∀ A : SL(2, K), ((A : Matrix (Fin 2) (Fin 2) K).map bar)ᵀ * S * A = S → A ∈ H)
    {l : K} (hl : bar l * l = 1) (hl2 : l * l ≠ bar (l * l)) (t : K) : sl2Upper K t ∈ H := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  have hlm : l * l⁻¹ = 1 := mul_inv_cancel₀ hl0
  have hbl : bar l = l⁻¹ := by
    calc bar l = bar l * (l * l⁻¹) := by rw [hlm, mul_one]
      _ = (bar l * l) * l⁻¹ := by ring
      _ = l⁻¹ := by rw [hl, one_mul]
  have hbm : bar l⁻¹ = l := by rw [map_inv₀, hbl, inv_inv]
  have e00 : bar (S 0 0) = -S 0 0 := by
    have := congrFun (congrFun hS 0) 0
    simpa using this
  have e01 : bar (S 1 0) = -S 0 1 := by
    have := congrFun (congrFun hS 0) 1
    simpa using this
  have e10 : bar (S 0 1) = -S 1 0 := by
    have := congrFun (congrFun hS 1) 0
    simpa using this
  have e11 : bar (S 1 1) = -S 1 1 := by
    have := congrFun (congrFun hS 1) 1
    simpa using this
  obtain ⟨c, hc⟩ : ∃ c : K, S 0 1 = S 0 0 * c := ⟨S 0 1 / S 0 0, by field_simp⟩
  have hd : S 1 0 = bar c * S 0 0 := by
    have := congrArg bar hc
    rw [map_mul, e00, e10] at this
    linear_combination -this
  let g : SL(2, K) := upperDiag l c hl0
  have hg : g ∈ H := by
    apply hSU
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g, coe_upperDiag, Matrix.mul_apply, Fin.sum_univ_two, hbl, hbm, hd, hc] <;> field_simp <;> ring_nf
  have hconj : ∀ s : K, g * sl2Upper K s = sl2Upper K (l * l * s) * g := by
    intro s
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_upperDiag, coe_sl2Upper,
      coe_sl2Upper]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  have hU : ∀ s : K, bar s = s → sl2Upper K s ∈ H := by
    intro s hs
    apply hreal
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Upper, hs]
  have hU2 : ∀ s : K, bar s = s → sl2Upper K (l * l * s) ∈ H := by
    intro s hs
    have : sl2Upper K (l * l * s) = g * sl2Upper K s * g⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact (hconj s).symm
    rw [this]
    exact mul_mem (mul_mem hg (hU s hs)) (inv_mem hg)
  obtain ⟨t₁, t₂, h1, h2, ht⟩ := exists_decomp bar hbb hl2 t
  rw [ht, sl2Upper_add]
  exact mul_mem (hU t₁ h1) (hU2 t₂ h2)

end Bar

theorem exists_norm_one_pow_four_ne_one [Finite K] {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 2) (h5 : 5 ≤ p ^ f) :
    ∃ l : K, l ^ (p ^ f) * l = 1 ∧ l ^ 4 ≠ 1 := by
  have := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hq1 : 1 ≤ p ^ f := by omega
  have hprod : (p ^ f - 1) * (p ^ f + 1) = (p ^ f) ^ 2 - 1 := by
    zify [hq1, Nat.one_le_pow 2 _ (by omega : 0 < p ^ f)]
    ring
  have hu1 : (g ^ (p ^ f - 1)) ^ (p ^ f + 1) = 1 := by
    rw [← pow_mul, hprod, ← hord, pow_orderOf_eq_one]
  have hu2 : (g ^ (p ^ f - 1)) ^ 4 ≠ 1 := by
    intro h
    rw [← pow_mul] at h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hd
    have hle := Nat.le_of_dvd (by omega) hd
    have : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := hprod.symm
    rw [this] at hle
    have h4 : 0 < p ^ f - 1 := by omega
    nlinarith
  refine ⟨((g ^ (p ^ f - 1) : Kˣ) : K), ?_, ?_⟩
  · have := congrArg (fun w : Kˣ => (w : K)) hu1
    simpa [Units.val_pow_eq_pow_val, pow_succ] using this
  · intro h
    apply hu2
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val] using h

theorem unitaryFieldData_of {p f : ℕ} [Finite K] (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) :
    UnitaryFieldData p f K := by
  refine ⟨hp, ?_, by rw [hK, ← pow_mul, mul_comm]⟩
  by_contra h0
  have hf : f = 0 := by omega
  subst hf
  have : Nat.card K = 1 := by simpa using hK
  exact (not_subsingleton K) (Nat.card_eq_one_iff_unique.1 this).1

section Bar

variable (bar : K →+* K)

theorem upper_all_of_real (hbb : ∀ c, bar (bar c) = c) (H : Subgroup SL(2, K))
    (hreal : ∀ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K).map bar = A → A ∈ H)
    (S : Matrix (Fin 2) (Fin 2) K) (hS : (S.map bar)ᵀ = -S)
    (hSU : ∀ A : SL(2, K), ((A : Matrix (Fin 2) (Fin 2) K).map bar)ᵀ * S * A = S → A ∈ H)
    {l : K} (hl : bar l * l = 1) (hl2 : l * l ≠ bar (l * l))
    (k : SL(2, K)) (hk : (k : Matrix (Fin 2) (Fin 2) K).map bar = k)
    (h00 : ((k : Matrix (Fin 2) (Fin 2) K)ᵀ * S * k) 0 0 ≠ 0) (t : K) : sl2Upper K t ∈ H := by
  have hkH : k ∈ H := hreal k hk
  have h1 : (k : Matrix (Fin 2) (Fin 2) K) * ((k⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : ((k⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hkinv : ((k⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map bar = ((k⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
    calc ((k⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map bar
        = (((k⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K)) *
            ((k⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map bar := by rw [h2, Matrix.one_mul]
      _ = ((k⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
            ((k : Matrix (Fin 2) (Fin 2) K).map bar * ((k⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map bar) := by
          rw [hk, Matrix.mul_assoc]
      _ = ((k⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
          rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero bar) (map_one bar), Matrix.mul_one]
  have hkT : ((k : Matrix (Fin 2) (Fin 2) K)ᵀ).map bar = (k : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    rw [Matrix.transpose_map, hk]
  refine core_aniso bar hbb H hreal ((k : Matrix (Fin 2) (Fin 2) K)ᵀ * S * k) ?_ h00 ?_ hl hl2 t
  · rw [Matrix.map_mul, Matrix.map_mul, hkT, hk, Matrix.transpose_mul, Matrix.transpose_mul, hS,
      Matrix.transpose_transpose]
    simp [Matrix.mul_assoc]
  · intro A hA
    have hB : k * A * k⁻¹ ∈ H := by
      apply hSU
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact transport bar hk hkinv h1 hA
    have : A = k⁻¹ * (k * A * k⁻¹) * k := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hkH) hB) hkH

end Bar

end GenLocU4Q2sSL2

namespace GenLocU4Q2s

open GenLocU4Q2sSL2

variable {K : Type} [Field K]

theorem sl2_eq_top_of_two_forms_of_five_le {p f : ℕ} [Finite K] (hp : p.Prime)
    (hK : Nat.card K = (p ^ f) ^ 2) (h5 : 5 ≤ p ^ f)
    (H : Subgroup SL(2, K))
    (hreal : ∀ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)) = A → A ∈ H)
    (S : Matrix (Fin 2) (Fin 2) K) (hS : (S.map (· ^ (p ^ f)))ᵀ = -S)
    (hSX : ∀ c : K, S ≠ c • !![0, 1; -1, 0])
    (hSU : ∀ A : SL(2, K), ((A : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ * S * A = S → A ∈ H) :
    H = ⊤ := by
  have h := unitaryFieldData_of (K := K) (p := p) (f := f) hp hK
  obtain ⟨l, hl, hl4⟩ := exists_norm_one_pow_four_ne_one hK h5
  have hl' : h.bar l * l = 1 := hl
  have hl2 : l * l ≠ h.bar (l * l) := by
    intro he
    apply hl4
    calc l ^ 4 = (l * l) * (l * l) := by ring
      _ = h.bar (l * l) * (l * l) := by rw [← he]
      _ = (h.bar l * l) * (h.bar l * l) := by rw [map_mul]; ring
      _ = 1 := by rw [hl', one_mul]
  have hbb := h.bar_bar
  have hreal' : ∀ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K).map h.bar = A → A ∈ H := hreal
  have hS' : (S.map h.bar)ᵀ = -S := hS
  have hSU' : ∀ A : SL(2, K), ((A : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * S * A = S → A ∈ H := hSU
  have hall : ∀ t : K, sl2Upper K t ∈ H := by
    intro t
    by_cases h0 : S 0 0 = 0
    · by_cases h1 : S 1 1 = 0
      · by_cases h2 : S 0 1 + S 1 0 = 0
        · exfalso
          apply hSX (S 0 1)
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h0, h1]
          linear_combination h2
        · refine upper_all_of_real h.bar hbb H hreal' S hS' hSU' hl' hl2 ⟨!![1, 0; 1, 1], by simp [det_fin_two_of]⟩
            (by ext i j; fin_cases i <;> fin_cases j <;> simp) ?_ t
          simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
          intro h3
          apply h2
          linear_combination h3
      · refine upper_all_of_real h.bar hbb H hreal' S hS' hSU' hl' hl2 ⟨!![0, -1; 1, 0], by simp [det_fin_two_of]⟩
          (by ext i j; fin_cases i <;> fin_cases j <;> simp) ?_ t
        simpa [Matrix.mul_apply, Fin.sum_univ_two] using h1
    · refine upper_all_of_real h.bar hbb H hreal' S hS' hSU' hl' hl2 1 (by ext i j; fin_cases i <;> fin_cases j <;> simp) ?_ t
      simpa using h0
  have hlow : ∀ t : K, sl2Lower K t ∈ H := by
    intro t
    let w : SL(2, K) := ⟨!![0, 1; -1, 0], by simp [det_fin_two_of]⟩
    have hw : w ∈ H := hreal' w (by ext i j; fin_cases i <;> fin_cases j <;> simp [w])
    have hwl : sl2Lower K t = w⁻¹ * sl2Upper K (-t) * w := by
      rw [mul_assoc, eq_inv_mul_iff_mul_eq]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hwl]
    exact mul_mem (mul_mem (inv_mem hw) (hall _)) hw
  rw [eq_top_iff, ← sl2_closure_upper_lower (K := K), Subgroup.closure_le]
  rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
  exacts [hall t, hlow t]

end GenLocU4Q2s

end CFSG.GH74.Generic.BProg.B2
