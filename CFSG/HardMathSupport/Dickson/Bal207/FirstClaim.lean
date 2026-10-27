module

public import CFSG.HardMathSupport.Dickson.Bal207.FCInner
public import CFSG.GH74.GLS.Stage2.OddAut.HeisField

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Timmesfeld.LinearRank

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem eq_of_pow_three_eq_one {c x : K} (hc : c ^ 3 = 1) (hc1 : c ≠ 1) (hx : x ^ 3 = 1) :
    x = 1 ∨ x = c ∨ x = c ^ 2 := by
  have h1 : c ^ 2 + c + 1 = 0 := by
    have h : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination hc
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hc1)
  have h2 : (x - 1) * (x - c) * (x - c ^ 2) = 0 := by
    linear_combination hx - (x ^ 2 - x * c) * h1 - hc
  rcases mul_eq_zero.1 h2 with h3 | h3
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact Or.inl (sub_eq_zero.1 h4)
    · exact Or.inr (Or.inl (sub_eq_zero.1 h4))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h3))

theorem ringEquiv_apply_of_pow_three (φ : K ≃+* K) {c x : K} (hc : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hφ : φ c = c) (hx : x ^ 3 = 1) : φ x = x := by
  rcases eq_of_pow_three_eq_one hc hc1 hx with rfl | rfl | rfl
  · exact map_one φ
  · exact hφ
  · rw [map_pow, hφ]

theorem ringEquiv_eq_one (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hf : f = 1 ∨ f = 3)
    {φ : K ≃+* K} {r : ℕ} (hr : Nat.Coprime 3 r) (hφr : φ ^ r = 1) {c : K} (hc : c ^ 3 = 1)
    (hc1 : c ≠ 1) (hφ : φ c = c) : φ = 1 := by
  subst hℓ
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨j, -, hj⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow Nat.prime_two
    (by have := h.one_le; omega) h.card φ
  have hj2 : 2 ∣ j := by
    by_contra hodd
    obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i + 1 := ⟨j / 2, by omega⟩
    have hmod : 2 ^ (2 * i + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h2 : c ^ 2 ^ (2 * i + 1) = c ^ 2 := by
      rw [← Nat.div_add_mod (2 ^ (2 * i + 1)) 3, hmod, pow_add, pow_mul, hc, one_pow, one_mul]
    have h3 := hj c
    rw [hφ, h2] at h3
    have hc0 : c ≠ 0 := by
      rintro rfl
      norm_num at hc
    apply hc1
    have h4 : c * (c - 1) = 0 := by linear_combination -h3
    exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_left hc0)
  obtain ⟨i, rfl⟩ := hj2
  obtain ⟨m, hm⟩ : 2 * f ∣ 3 * (2 * i) := by
    rcases hf with rfl | rfl
    · exact ⟨3 * i, by ring⟩
    · exact ⟨i, by ring⟩
  have hcard : Fintype.card K = 2 ^ (2 * f) := by
    rw [Fintype.card_eq_nat_card]
    exact h.card
  have he : 2 ^ (2 * i) * (2 ^ (2 * i) * 2 ^ (2 * i)) = Fintype.card K ^ m := by
    rw [hcard, ← pow_mul, ← hm]
    ring
  have hφ3 : φ ^ 3 = 1 := by
    refine RingEquiv.ext fun x => ?_
    rw [pow_three, RingAut.mul_apply, RingAut.mul_apply, hj, hj, hj, ← pow_mul, ← pow_mul, he,
      RingAut.one_apply]
    exact FiniteField.pow_card_pow m x
  have h1 := (pow_gcd_eq_one (a := φ) (m := 3) (n := r)).2 ⟨hφ3, hφr⟩
  rwa [hr, pow_one] at h1

theorem exists_apply_ne_zero (A : GL (Fin n) K) (r : Fin n) :
    ∃ s, (A : Matrix (Fin n) (Fin n) K) r s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M r r) A.mul_inv
  simp only [Matrix.mul_apply, hcon, zero_mul, Finset.sum_const_zero, one_apply_eq] at h1
  exact zero_ne_one h1

theorem eq_of_mul_map_eq {φ : K ≃+* K} (hφ : ∀ c : K, c ^ 3 = 1 → c ≠ 1 → φ c ≠ c)
    {A d : Matrix (Fin n) (Fin n) K} {t : K}
    (hAd : ∀ i j, A i j * φ (d j j) = t * (d i i * A i j)) {r r' s s' : Fin n} (hr : r ≠ r')
    (hs : A r s ≠ 0) (hs' : A r' s' ≠ 0) (hc : d r r ^ 3 = 1) (hc1 : d r r ≠ 1)
    (hd1 : ∀ i, i ≠ r → d i i = 1) : s' = r := by
  by_contra hne
  have ht : t = 1 := by
    have e := hAd r' s'
    rw [hd1 s' hne, hd1 r' (Ne.symm hr), map_one, mul_one, one_mul] at e
    have e2 : (t - 1) * A r' s' = 0 := by linear_combination -e
    exact sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_right hs')
  have e := hAd r s
  rw [ht, one_mul] at e
  have e2 : φ (d s s) = d r r := by
    have e3 : A r s * (φ (d s s) - d r r) = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 e3).resolve_left hs)
  by_cases hsr : s = r
  · subst hsr
    exact hφ _ hc hc1 e2
  · rw [hd1 s hsr, map_one] at e2
    exact hc1 e2.symm

structure IsOmegaOneTorus (D : Subgroup (GL (Fin n) K)) : Prop where
  diag : ∀ d ∈ D, (d : Matrix (Fin n) (Fin n) K).IsDiag
  cube : ∀ d ∈ D, d ^ 3 = 1
  single : ∀ u : Fin n, ∃ d ∈ D, (d : Matrix (Fin n) (Fin n) K) u u ≠ 1 ∧
    ∀ i, i ≠ u → (d : Matrix (Fin n) (Fin n) K) i i = 1

theorem IsOmegaOneTorus.isFullDiag {D : Subgroup (GL (Fin n) K)} (hD : IsOmegaOneTorus D) :
    IsFullDiag D where
  diag := hD.diag
  cube := hD.cube
  sep i j hij := by
    obtain ⟨d, hd, hi, hj⟩ := hD.single i
    exact ⟨d, hd, by rw [hj j (Ne.symm hij)]; exact hi⟩
  three i j l hij hil hjl := by
    obtain ⟨d, hd, hi, hj⟩ := hD.single i
    exact ⟨d, hd, by rw [hj l (Ne.symm hil)]; exact hi,
      by rw [hj j (Ne.symm hij), hj l (Ne.symm hil)]⟩

theorem eq_bot_of_omegaOne (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hf : f = 1 ∨ f = 3)
    (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {D : Subgroup (GL (Fin n) K)}
    (hD : IsOmegaOneTorus D) {Q : Subgroup (MulAut (primeFormP h (oneGram K n)))}
    (hQ3 : Nat.Coprime 3 (Nat.card Q))
    (hDQ : ∀ A : primeFormUnitary h (oneGram K n), (A : GL (Fin n) K) ∈ D → ∀ σ ∈ Q,
      primeFormConjHom h _ A * σ * (primeFormConjHom h _ A)⁻¹ ∈ Q) : Q = ⊥ := by
  classical
  obtain ⟨k, hq⟩ : ∃ k, ℓ ^ f + 1 = 3 ^ k := by
    subst hℓ
    rcases hf with rfl | rfl
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
  have hC := isPrimeFormGram_one (K := K) (n := n)
  set F := primeFormFieldFactor h hC hn hne with hF
  have hker : F.ker = primeFormD h (oneGram K n) := ker_primeFormFieldFactor h hC hn hne
  have hcD : ∀ A : primeFormUnitary h (oneGram K n), F (primeFormConjHom h _ A) = 1 := by
    intro A
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨A, rfl⟩
  have hQD : Q ⊓ primeFormD h (oneGram K n) = ⊥ := by
    refine eq_bot_of_le_primeFormD h hq hn hne hD.isFullDiag inf_le_right ?_ ?_
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hQ3
    · intro A hA σ hσ
      obtain ⟨hσQ, hσD⟩ := Subgroup.mem_inf.1 hσ
      refine Subgroup.mem_inf.2 ⟨hDQ A hA σ hσQ, ?_⟩
      rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_inv, hcD, one_mul, inv_one, mul_one]
      rw [← MonoidHom.mem_ker, hker]
      exact hσD
  have hcomm : ∀ A : primeFormUnitary h (oneGram K n), (A : GL (Fin n) K) ∈ D → ∀ s ∈ Q,
      primeFormConjHom h _ A * s = s * primeFormConjHom h _ A := by
    intro A hA s hs
    have h1 : primeFormConjHom h _ A * s * (primeFormConjHom h _ A)⁻¹ * s⁻¹ ∈
        Q ⊓ primeFormD h (oneGram K n) := by
      refine Subgroup.mem_inf.2 ⟨Q.mul_mem (hDQ A hA s hs) (Q.inv_mem hs), ?_⟩
      rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcD]
      group
    rw [hQD, Subgroup.mem_bot] at h1
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
  obtain ⟨d₀, hd₀D, hd₀1, -⟩ := hD.single ⟨0, by omega⟩
  have hc3 := hD.isFullDiag.entry_cube hd₀D ⟨0, by omega⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro s hs
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hne s
  rw [primeFormPsi_apply] at hAφ
  have hFs : F s = φ := by
    rw [← hAφ]
    exact primeFormFieldFactor_apply h hC hn hne A φ
  by_cases hφ : φ ((d₀ : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) =
      (d₀ : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩
  ·
    have hr : Nat.Coprime 3 (orderOf s) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard Q hs) hQ3
    have hφr : φ ^ orderOf s = 1 := by rw [← hFs, ← map_pow, pow_orderOf_eq_one, map_one]
    have hφ1 := ringEquiv_eq_one h hℓ hf hr hφr hc3 hd₀1 hφ
    have hsD : s ∈ Q ⊓ primeFormD h (oneGram K n) := by
      refine Subgroup.mem_inf.2 ⟨hs, ?_⟩
      rw [← hker, MonoidHom.mem_ker, hFs, hφ1]
    rw [hQD] at hsD
    exact hsD
  ·
    exfalso
    have hφ' : ∀ x : K, x ^ 3 = 1 → x ≠ 1 → φ x ≠ x := fun x hx hx1 hφx =>
      hφ (ringEquiv_apply_of_pow_three φ hx hx1 hφx hc3)
    have hrel : ∀ d ∈ D, ∃ t : K, ∀ i j,
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j *
          φ ((d : Matrix (Fin n) (Fin n) K) j j) = t * ((d : Matrix (Fin n) (Fin n) K) i i *
            ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) := by
      intro d hd
      have hdU : d ∈ primeFormUnitary h (oneGram K n) := hD.isFullDiag.mem_unitary h hq hd
      have hsc := hcomm ⟨d, hdU⟩ hd s hs
      set dU : primeFormUnitary h (oneGram K n) := ⟨d, hdU⟩ with hdU'
      have h2 : primeFormConjHom h (oneGram K n)
          (A * primeFormFieldU h hC φ dU * A⁻¹ * dU⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← primeFormField_conj_eq h hC φ dU]
        calc _ = (primeFormConjHom h _ A * primeFormFieldHom h hC φ) * primeFormConjHom h _ dU *
              (primeFormConjHom h _ A * primeFormFieldHom h hC φ)⁻¹ *
                (primeFormConjHom h _ dU)⁻¹ := by group
          _ = 1 := by
            rw [hAφ, ← hsc]
            group
      have h3 := (primeFormConjHom_eq_one_iff_center h hn hne _).1 h2
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3
      obtain ⟨t, ht⟩ := h3
      have h4 : (A : GL (Fin n) K) * glAut φ d =
          Matrix.GeneralLinearGroup.scalar (Fin n) t * d * A := by
        rw [ht]
        simp only [hdU', Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, Subgroup.coe_mk]
        group
      refine ⟨(t : K), fun i j => ?_⟩
      have h5 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i j) h4
      simp only [Units.val_mul, coe_glAut, Matrix.GeneralLinearGroup.coe_scalar] at h5
      rw [mul_diag_apply ((hD.diag d hd).map (map_zero φ)), Matrix.map_apply, mul_assoc,
        Matrix.scalar_apply, diagonal_mul, diag_mul_apply (hD.diag d hd)] at h5
      exact h5
    have hrow : ∀ r r' : Fin n, r ≠ r' → ∀ s s' : Fin n,
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) r s ≠ 0 →
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) r' s' ≠ 0 → s' = r := by
      intro r r' hr s s' hs hs'
      obtain ⟨d, hd, hd1, hdo⟩ := hD.single r
      obtain ⟨t, ht⟩ := hrel d hd
      exact eq_of_mul_map_eq hφ' ht hr hs hs' (hD.isFullDiag.entry_cube hd r) hd1 hdo
    obtain ⟨s₀, hs₀⟩ := exists_apply_ne_zero (A : GL (Fin n) K) ⟨0, by omega⟩
    obtain ⟨s₁, hs₁⟩ := exists_apply_ne_zero (A : GL (Fin n) K) ⟨1, by omega⟩
    obtain ⟨s₂, hs₂⟩ := exists_apply_ne_zero (A : GL (Fin n) K) ⟨2, by omega⟩
    have e₀ := hrow ⟨0, by omega⟩ ⟨2, by omega⟩ (by simp) s₀ s₂ hs₀ hs₂
    have e₁ := hrow ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp) s₁ s₂ hs₁ hs₂
    rw [e₀] at e₁
    exact absurd (congrArg Fin.val e₁) (by simp)

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
