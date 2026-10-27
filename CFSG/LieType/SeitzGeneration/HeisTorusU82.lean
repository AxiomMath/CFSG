module

public import CFSG.LieType.SeitzGeneration.HeisTorusUDefs
public import CFSG.LieType.SeitzGeneration.UnitaryHeisGU2

public section

open scoped MatrixGroups

open CFSG.BenderSuzuki.MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.LieType.SeitzGeneration

section Dickson

variable {K : Type} [Field K]

open CFSG.Glauberman.Dickson CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
  CFSG.GorensteinWalter in
theorem ug82_card_ge_of_pair {p f : ℕ} [Fact p.Prime] [CharP K p]
    [Finite K] (hK : Nat.card K = p ^ (2 * f)) (hq : 4 ≤ p ^ f) (H : Subgroup (PSL2MatrixGroup K))
    {A B : SpecialLinearGroup (Fin 2) K} (hA : (A : PSL2MatrixGroup K) ∈ H)
    (hB : (B : PSL2MatrixGroup K) ∈ H) {P : Matrix (Fin 2) (Fin 2) K} {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹])
    (hμ : orderOf (μ ^ 2) = p ^ f + 1) (hB3 : 2 < orderOf (B : PSL2MatrixGroup K))
    (hno : ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False) :
    p ^ f * ((p ^ f) ^ 2 - 1) ≤ 2 * Nat.card H := by
  classical
  have hp' : p.Prime := Fact.out
  have hf1 : 1 ≤ f := by
    by_contra hlt
    have : f = 0 := by omega
    subst this
    simp at hq
  have hord1 : orderOf (A : PSL2MatrixGroup K) = p ^ f + 1 := by
    rw [orderOf_mk_eq hP hAP]
    exact hμ
  have hμ4 : μ ^ 4 ≠ 1 := by
    intro h4
    have h2 : orderOf (μ ^ 2) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← pow_mul]; exact h4)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  set a : H := ⟨(A : PSL2MatrixGroup K), hA⟩ with ha
  set b : H := ⟨(B : PSL2MatrixGroup K), hB⟩ with hb
  have hao : orderOf a = p ^ f + 1 := by rw [ha, Subgroup.orderOf_mk, hord1]
  have hbo : orderOf b = orderOf (B : PSL2MatrixGroup K) := Subgroup.orderOf_mk _ _
  have hcomm_false : (a * b = b * a) → False := by
    intro hab
    have hP' : (A : PSL2MatrixGroup K) * (B : PSL2MatrixGroup K) =
        (B : PSL2MatrixGroup K) * (A : PSL2MatrixGroup K) := congrArg Subtype.val hab
    obtain ⟨x, hx0, hxA, hxB⟩ := exists_common_eigenvector_of_commute hP hAP hμ4 hP'
    exact hno x hx0 hxA hxB
  have ha5 : 5 ≤ orderOf a := by rw [hao]; omega
  have hb3 : 2 < orderOf b := by rw [hbo]; exact hB3
  rcases dickson_psl2_subgroup_list hK H with
    ⟨_, _, _, hel⟩ | ⟨_, _, _, hcyc⟩ | ⟨_, _, _, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, _, _, _, _, _, E, _, hEn, hEel, hEcard, _, _, _, _, _, _, _, ⟨_⟩⟩ | ⟨m, hmf, ⟨e⟩⟩ |
      ⟨m, hmf, ⟨e⟩⟩
  ·
    exfalso
    have := hel
    have h1 : (A : PSL2MatrixGroup K) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := p) (A := H) _ hA
    have h2 : orderOf (A : PSL2MatrixGroup K) ∣ p := orderOf_dvd_of_pow_eq_one h1
    have h3 := Nat.le_of_dvd hp'.pos h2
    have h4 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  ·
    exfalso
    exact hcomm_false (hcyc.commGroup.mul_comm a b)
  ·
    exfalso
    exact hcomm_false (commute_of_equiv_dihedral e (x := a) (y := b) (by omega) hb3)
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_alternating_four e a with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_perm_four e a with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    rcases orderOf_dvd_of_equiv_alternating_five e a with h | h | h
    · exfalso
      have := Nat.le_of_dvd (by norm_num) h
      omega
    · exfalso
      have := Nat.le_of_dvd (by norm_num) h
      omega
    · have h5 := Nat.le_of_dvd (by norm_num) h
      have hq4 : p ^ f = 4 := by omega
      have hcardH : Nat.card H = 60 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      rw [hq4, hcardH]
      norm_num
  ·
    exfalso
    have := hEn
    have := hEel
    have hE1 : E ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hEcard
      have : p ^ m = p ^ 0 := by rw [← hEcard, pow_zero]
      have := Nat.pow_right_injective hp'.two_le this
      omega
    obtain ⟨x, hx0, hxA, hxB⟩ := exists_common_eigenvector_of_normal_pGroup hE1 hA hB
    exact hno x hx0 hxA hxB
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hmf
      omega
    have hFm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    by_cases hfm : f ≤ m
    · have h1 := card_psl2_ge (GaloisField p m)
      rw [hFm] at h1
      have h2 : Nat.card H = Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        Nat.card_congr e.toEquiv
      rw [h2]
      have hxy : p ^ f ≤ p ^ m := Nat.pow_le_pow_right hp'.pos hfm
      calc p ^ f * ((p ^ f) ^ 2 - 1) ≤ p ^ m * ((p ^ m) ^ 2 - 1) :=
            Nat.mul_le_mul hxy (Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1)
        _ ≤ _ := h1
    · exfalso
      push Not at hfm
      have h1 := psl2_orderOf_le (GaloisField p m) (e a)
      rw [MulEquiv.orderOf_eq, hFm, hao] at h1
      have : p ^ m < p ^ f := Nat.pow_lt_pow_right hp'.one_lt hfm
      omega
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hmf
      omega
    have hFm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have hmf' : m ∣ f := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hmf
    by_cases hfm : f ≤ m
    · have h2 : Nat.card H = p ^ m * (p ^ (2 * m) - 1) := by
        rw [Nat.card_congr e.toEquiv, MaxUp.card_pgl2_galoisField hm0]
      rw [h2]
      have hxy : p ^ f ≤ p ^ m := Nat.pow_le_pow_right hp'.pos hfm
      have : (p ^ m) ^ 2 = p ^ (2 * m) := by rw [← pow_mul, mul_comm]
      calc p ^ f * ((p ^ f) ^ 2 - 1) ≤ p ^ m * ((p ^ m) ^ 2 - 1) :=
            Nat.mul_le_mul hxy (Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1)
        _ = p ^ m * (p ^ (2 * m) - 1) := by rw [this]
        _ ≤ 2 * (p ^ m * (p ^ (2 * m) - 1)) := Nat.le_mul_of_pos_left _ (by norm_num)
    · exfalso
      push Not at hfm
      have h1 := pgl2_orderOf_le (GaloisField p m) (e a)
      rw [MulEquiv.orderOf_eq, hFm, hao] at h1
      have : p ^ m < p ^ f := Nat.pow_lt_pow_right hp'.one_lt hfm
      omega

theorem ug82_card_ge_of_pgl_pair {p f : ℕ} [Fact p.Prime] [CharP K p]
    [Finite K] (hK : Nat.card K = p ^ (2 * f)) (hq : 4 ≤ p ^ f) (J : Subgroup PGL(Fin 2, K))
    (hJ : J ≤ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range)
    {A B : SpecialLinearGroup (Fin 2) K}
    (hA : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) ∈ J)
    (hB : ProjGenLinGroup.mk (SpecialLinearGroup.toGL B) ∈ J)
    {P : Matrix (Fin 2) (Fin 2) K} {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹])
    (hμ : orderOf (μ ^ 2) = p ^ f + 1) (hB3 : 2 < orderOf (B : PSL2MatrixGroup K))
    (hno : ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False) :
    p ^ f * ((p ^ f) ^ 2 - 1) ≤ 2 * Nat.card J := by
  set ι := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K) with hι
  set H : Subgroup (PSL2MatrixGroup K) := J.comap ι with hH
  have hmap : H.map ι = J := Subgroup.map_comap_eq_self hJ
  have hcard : Nat.card H = Nat.card J := by
    rw [← hmap]
    exact Nat.card_congr
      (H.equivMapOfInjective ι ProjectiveSpecialLinearGroup.toPGL_injective).toEquiv
  have hAH : (A : PSL2MatrixGroup K) ∈ H := by
    show ι (A : PSL2MatrixGroup K) ∈ J
    rw [hι, ProjectiveSpecialLinearGroup.toPGL_mk]
    exact hA
  have hBH : (B : PSL2MatrixGroup K) ∈ H := by
    show ι (B : PSL2MatrixGroup K) ∈ J
    rw [hι, ProjectiveSpecialLinearGroup.toPGL_mk]
    exact hB
  rw [← hcard]
  exact ug82_card_ge_of_pair hK hq H hAH hBH hP hAP hμ hB3 hno

end Dickson

section Homology

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem ug82_norm_eq_one (h : UnitaryFieldData ℓ f K) {σ : K} (hσ : orderOf σ = ℓ ^ f + 1) :
    h.bar σ * σ = 1 := by
  rw [bar_mul_self_eq_pow, ← hσ]
  exact pow_orderOf_eq_one σ

theorem ug82_rankOne_mem_gu2 (h : UnitaryFieldData ℓ f K) (w : Fin 2 → K) {c : K}
    (key : c + h.bar c + h.bar c * c * (h.bar (w 0) * w 0 + h.bar (w 1) * w 1) = 0)
    {g : GL (Fin 2) K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = 1 + c • vecMulVec w (fun i => h.bar (w i))) :
    g ∈ gu2 h := by
  rw [mem_gu2, hg]
  have e1 := h.bar_bar (w 0)
  have e2 := h.bar_bar (w 1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply, Matrix.one_apply, e1, e2,
      map_add, map_mul]
  · linear_combination (w 0 * h.bar (w 0)) * key
  · linear_combination (w 0 * h.bar (w 1)) * key
  · linear_combination (w 1 * h.bar (w 0)) * key
  · linear_combination (w 1 * h.bar (w 1)) * key

theorem ug82_homology_mem_gu2 (h : UnitaryFieldData ℓ f K) {w : Fin 2 → K}
    (hw : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 ≠ 0) {σ : K} (hσ : h.bar σ * σ = 1)
    {g : GL (Fin 2) K} (hg : (g : Matrix (Fin 2) (Fin 2) K) = unitaryHomology h w σ) :
    g ∈ gu2 h := by
  set n := h.bar (w 0) * w 0 + h.bar (w 1) * w 1 with hn
  have hcn : (σ - 1) / n * n = σ - 1 := div_mul_cancel₀ _ hw
  have hbn : h.bar n = n := by
    rw [hn, map_add, map_mul, map_mul, h.bar_bar, h.bar_bar]
    ring
  have hbcn : h.bar ((σ - 1) / n) * n = h.bar σ - 1 := by
    have := congrArg h.bar hcn
    rwa [map_mul, hbn, map_sub, map_one] at this
  refine ug82_rankOne_mem_gu2 h w (c := (σ - 1) / n) ?_ ?_
  · apply mul_right_cancel₀ hw
    linear_combination (h.bar ((σ - 1) / n) * n + 1) * hcn + σ * hbcn + hσ
  · rw [hg]
    simp only [unitaryHomology, Fin.sum_univ_two, hn]

theorem ug82_homology_data (h : UnitaryFieldData ℓ f K) {w : Fin 2 → K}
    (hw : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 ≠ 0) {σ : K} (hσ : h.bar σ * σ = 1)
    (hσ1 : σ ≠ 1) :
    ∃ (s μ : K) (A : SpecialLinearGroup (Fin 2) K) (P : Matrix (Fin 2) (Fin 2) K),
      s ≠ 0 ∧ (A : Matrix (Fin 2) (Fin 2) K) = s • unitaryHomology h w σ ∧ μ ^ 2 = σ ∧
      P.det ≠ 0 ∧ (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹] ∧
      ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
        (∃ t : K, t ≠ 0 ∧ x = t • w) ∨
          ∃ t : K, t ≠ 0 ∧ x = t • ![-h.bar (w 1), h.bar (w 0)] := by
  obtain ⟨n, hn⟩ : ∃ n, n = h.bar (w 0) * w 0 + h.bar (w 1) * w 1 := ⟨_, rfl⟩
  rw [← hn] at hw
  set Pw : Matrix (Fin 2) (Fin 2) K := !![w 0, -h.bar (w 1); w 1, h.bar (w 0)] with hPw
  have hdetP : Pw.det = n := by
    rw [hPw, Matrix.det_fin_two_of, hn]
    ring
  have hcn : (σ - 1) / n * n = σ - 1 := div_mul_cancel₀ _ hw
  have hg : unitaryHomology h w σ * Pw = Pw * diagonal ![σ, 1] := by
    simp only [unitaryHomology, Fin.sum_univ_two, ← hn]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hPw, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply, Matrix.one_apply,
        Matrix.diagonal_apply]
    · linear_combination w 0 * hcn - ((σ - 1) / n * w 0) * hn
    · ring
    · linear_combination w 1 * hcn - ((σ - 1) / n * w 1) * hn
    · ring
  have hdetg : (unitaryHomology h w σ).det = σ := by
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, hdetP, Matrix.det_diagonal, Fin.prod_univ_two] at this
    apply mul_right_cancel₀ hw
    simpa [mul_comm] using this
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    simp at hσ
  obtain ⟨s, hs⟩ := isSquare_of_norm_one h (u := σ⁻¹)
    (by rw [map_inv₀, ← mul_inv, hσ, inv_one])
  have hss : s * s * σ = 1 := by
    rw [← hs]
    exact inv_mul_cancel₀ hσ0
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hss
  have hμinv : (s * σ)⁻¹ = s := inv_eq_of_mul_eq_one_right (by linear_combination hss)
  have hdetA : (s • unitaryHomology h w σ).det = 1 := by
    rw [Matrix.det_smul, hdetg]
    simp only [Fintype.card_fin]
    linear_combination hss
  have hAP : (s • unitaryHomology h w σ) * Pw = Pw * diagonal ![s * σ, (s * σ)⁻¹] := by
    have hd : (diagonal ![s * σ, s] : Matrix (Fin 2) (Fin 2) K) =
        s • (diagonal ![σ, 1] : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
    rw [hμinv, Matrix.smul_mul, hg, hd, Matrix.mul_smul]
  have hne : s * σ ≠ (s * σ)⁻¹ := by
    rw [hμinv]
    intro h1
    apply hσ1
    have := mul_left_cancel₀ hs0 (h1.trans (mul_one s).symm)
    exact this
  have hdetP0 : Pw.det ≠ 0 := by rw [hdetP]; exact hw
  refine ⟨s, s * σ, ⟨s • unitaryHomology h w σ, hdetA⟩, Pw, hs0, rfl,
    by linear_combination σ * hss, hdetP0, hAP, ?_⟩
  intro x hx0 ⟨c, hc⟩
  rcases eigenvector_cases hdetP0 hne hAP hc hx0 with ⟨-, t, ht⟩ | ⟨-, t, ht⟩
  · left
    refine ⟨t, ?_, ?_⟩
    · rintro rfl
      apply hx0
      simpa using ht
    · rw [ht]
      congr 1
      ext i
      fin_cases i <;> simp [hPw]
  · right
    refine ⟨t, ?_, ?_⟩
    · rintro rfl
      apply hx0
      simpa using ht
    · rw [ht]
      congr 1
      ext i
      fin_cases i <;> simp [hPw]

theorem ug82_cross_eq_zero {a b : Fin 2 → K} {t t' : K} (ht : t ≠ 0) (h : t • a = t' • b) :
    a 0 * b 1 - a 1 * b 0 = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
  have : t * (a 0 * b 1 - a 1 * b 0) = 0 := by linear_combination b 1 * h0 - b 0 * h1
  exact (mul_eq_zero.1 this).resolve_left ht

theorem ug82_card_map_eq_card_quotient_ker {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (Y : Subgroup G) : Nat.card (Y.map φ) = Nat.card (Y ⧸ (φ.comp Y.subtype).ker) := by
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (φ.comp Y.subtype)).toEquiv,
    MonoidHom.range_comp, Subgroup.range_subtype]

theorem ug82_card_map_eq_of_ker_eq {G H₁ H₂ : Type*} [Group G] [Group H₁] [Group H₂]
    (φ₁ : G →* H₁) (φ₂ : G →* H₂) (hk : φ₁.ker = φ₂.ker) (Y : Subgroup G) :
    Nat.card (Y.map φ₁) = Nat.card (Y.map φ₂) := by
  rw [ug82_card_map_eq_card_quotient_ker φ₁, ug82_card_map_eq_card_quotient_ker φ₂,
    ← MonoidHom.comap_ker, ← MonoidHom.comap_ker, hk]

theorem su2_le_of_two_homologies (h : UnitaryFieldData ℓ f K)
    (hq : 4 ≤ ℓ ^ f) (he : 5 ≤ (ℓ ^ f + 1) / Nat.gcd 2 (ℓ ^ f + 1))
    (X : Subgroup (GL (Fin 2) K)) {w u : Fin 2 → K} {σ ρ : K}
    (hw : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 ≠ 0)
    (hu : h.bar (u 0) * u 0 + h.bar (u 1) * u 1 ≠ 0)
    (hwu : h.bar (w 0) * u 0 + h.bar (w 1) * u 1 ≠ 0) (hind : w 0 * u 1 - w 1 * u 0 ≠ 0)
    (hσ : orderOf σ = ℓ ^ f + 1) (hρ : orderOf ρ = ℓ ^ f + 1)
    (hX1 : ∃ g ∈ X, (g : Matrix (Fin 2) (Fin 2) K) = unitaryHomology h w σ)
    (hX2 : ∃ g ∈ X, (g : Matrix (Fin 2) (Fin 2) K) = unitaryHomology h u ρ) :
    unitarySU ℓ f K 2 ≤ X := by
  have _ := he
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hσn := ug82_norm_eq_one h hσ
  have hρn := ug82_norm_eq_one h hρ
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hρ
    omega
  obtain ⟨g₁, hg₁X, hg₁⟩ := hX1
  obtain ⟨g₂, hg₂X, hg₂⟩ := hX2
  have hg₁u : g₁ ∈ gu2 h := ug82_homology_mem_gu2 h hw hσn hg₁
  have hg₂u : g₂ ∈ gu2 h := ug82_homology_mem_gu2 h hu hρn hg₂
  obtain ⟨s, μ, A, P, hs0, hAs, hμ2, hP, hAP, hevA⟩ := ug82_homology_data h hw hσn hσ1
  obtain ⟨t, ν, B, Q, ht0, hBt, hν2, hQ, hBQ, hevB⟩ := ug82_homology_data h hu hρn hρ1
  set Y : Subgroup (gu2 h) := X.subgroupOf (gu2 h) with hY
  let ψ : gu2 h →* PGL(Fin 2, K) := ProjGenLinGroup.mk.comp (gu2 h).subtype
  have hker : ψ.ker = (gu2Proj h).ker := by
    ext g
    rw [mem_ker_gu2Proj, MonoidHom.mem_ker]
    exact ProjGenLinGroup.mk_eq_one
  have hψrange : ψ.range ≤ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    rintro _ ⟨g, rfl⟩
    exact mk_mem_range_toPGL _ (isSquare_of_norm_one h (norm_det_of_mem_gu2 h g.2))
  have hmk : ∀ (g : gu2 h) (v : K) (hv : v ≠ 0) (T : SpecialLinearGroup (Fin 2) K),
      ((T : Matrix (Fin 2) (Fin 2) K) = v • ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) →
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL T) = ψ g := by
    intro g v hv T hT
    show _ = ProjGenLinGroup.mk (g : GL (Fin 2) K)
    symm
    rw [ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 v hv, Units.ext ?_⟩
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hT]
    ext i j
    simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
  have hAJ : ProjGenLinGroup.mk (SpecialLinearGroup.toGL A) ∈ Y.map ψ := by
    rw [hmk ⟨g₁, hg₁u⟩ s hs0 A (by rw [hAs, hg₁])]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg₁X)
  have hBJ : ProjGenLinGroup.mk (SpecialLinearGroup.toGL B) ∈ Y.map ψ := by
    rw [hmk ⟨g₂, hg₂u⟩ t ht0 B (by rw [hBt, hg₂])]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg₂X)
  have hμ : orderOf (μ ^ 2) = ℓ ^ f + 1 := by rw [hμ2, hσ]
  have hB3 : 2 < orderOf (B : PSL2MatrixGroup K) := by
    have hν : orderOf (ν ^ 2) = ℓ ^ f + 1 := by rw [hν2, hρ]
    rw [orderOf_mk_eq hQ hBQ, hν]
    omega
  have hbar0 : ∀ z : K, h.bar z = 0 → z = 0 := fun z hz => (map_eq_zero h.bar).1 hz
  have hno : ∀ x : Fin 2 → K, x ≠ 0 →
      (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False := by
    intro x hx0 hxA hxB
    rcases hevA x hx0 hxA with ⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩ <;>
      rcases hevB x hx0 hxB with ⟨b, hb, hxb⟩ | ⟨b, hb, hxb⟩
    · exact hind (ug82_cross_eq_zero ha (hxa.symm.trans hxb))
    · have hc := ug82_cross_eq_zero ha (hxa.symm.trans hxb)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
      apply hwu
      apply hbar0
      rw [map_add, map_mul, map_mul, h.bar_bar, h.bar_bar]
      linear_combination hc
    · have hc := ug82_cross_eq_zero ha (hxa.symm.trans hxb)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
      apply hwu
      linear_combination -hc
    · have hc := ug82_cross_eq_zero ha (hxa.symm.trans hxb)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
      apply hind
      apply hbar0
      rw [map_sub, map_mul, map_mul]
      linear_combination hc
  have hcard := ug82_card_ge_of_pgl_pair h.card hq (Y.map ψ)
    ((Y.map_le_range ψ).trans hψrange) hAJ hBJ hP hAP hμ hB3 hno
  rw [ug82_card_map_eq_of_ker_eq ψ (gu2Proj h) hker Y] at hcard
  have hSU := su2_le_of_card_ge h hq Y hcard
  have hSUle : unitarySU ℓ f K 2 ≤ gu2 h := fun g hg =>
    (mem_gu2 h).2 ((mem_unitarySU_iff h).1 hg).2
  intro g hg
  exact hSU ⟨g, hSUle hg⟩ hg

end Homology

end CFSG.LieType.SeitzGeneration
