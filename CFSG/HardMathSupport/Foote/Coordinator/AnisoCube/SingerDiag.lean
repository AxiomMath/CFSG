module

public import CFSG.Quasithin.SteinbergBQPlaneEigen
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

open Matrix

variable {K : Type} [Field K] [Finite K] {r : ℕ} [hr : Fact r.Prime] [CharP K r]

theorem not_dvd_sub_one_add_one_of_dvd {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hq : 1 ≤ q)
    (hpq : p ∣ q ^ 2 + q + 1) : ¬ p ∣ q - 1 ∧ ¬ p ∣ q + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Nat.add_sub_cancel] at h
    have he : (m + 1) ^ 2 + (m + 1) + 1 = m * (m + 3) + 3 := by ring
    rw [he] at hpq
    have h3 : p ∣ 3 := (Nat.dvd_add_right (dvd_mul_of_dvd_left h _)).1 hpq
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)
  · have he : (m + 1) ^ 2 + (m + 1) + 1 = (m + 1 + 1) * (m + 1) + 1 := by ring
    rw [he] at hpq
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_left h _)).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem exists_conj_diag_of_orderOf {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpr : p ≠ r)
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : orderOf g = p) :
    ∃ (l : FiniteField.Extension K r 3) (s : Matrix (Fin 3) (Fin 3) (FiniteField.Extension K r 3)),
      orderOf l = p ∧ IsUnit s ∧
      (algebraMap K (FiniteField.Extension K r 3)).mapMatrix (g : Matrix (Fin 3) (Fin 3) K) * s =
        s * Matrix.diagonal ![l, l ^ Nat.card K, l ^ (Nat.card K ^ 2)] := by
  classical
  have hpF : Fact p.Prime := ⟨hp⟩
  set L := FiniteField.Extension K r 3
  set q := Nat.card K with hqdef
  set f := algebraMap K L
  set Fr : L ≃ₐ[K] L := FiniteField.Extension.frob K r 3 with hFr
  have hFrap : ∀ x : L, Fr x = x ^ q := fun x => FiniteField.Extension.frob_apply K r 3
  have hq1 : 1 ≤ q := Nat.card_pos
  obtain ⟨hpq1, hpq2⟩ := not_dvd_sub_one_add_one_of_dvd hp hp3 hq1 hpq
  set T : Matrix (Fin 3) (Fin 3) L := f.mapMatrix (g : Matrix (Fin 3) (Fin 3) K) with hT
  have hcardL : Nat.card L = q ^ 3 := FiniteField.natCard_extension K r 3
  have hpL : p ∣ Nat.card Lˣ := by
    rw [Nat.card_units, hcardL]
    have he : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
      obtain ⟨m, hm⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      have : (m + 1) ^ 3 = m * ((m + 1) ^ 2 + (m + 1) + 1) + 1 := by ring
      omega
    rw [he]
    exact dvd_mul_of_dvd_right hpq _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Lˣ) p hpL
  have hζ : IsPrimitiveRoot (u : L) p := by
    have := IsPrimitiveRoot.orderOf (u : L)
    rwa [orderOf_units, hu] at this
  have : CharP L r := charP_of_injective_algebraMap (algebraMap K L).injective r
  have hpL0 : (p : L) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff L r] at h
    exact hpr ((Nat.prime_dvd_prime_iff_eq hr.out hp).1 h).symm
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hTp : T ^ p = 1 := by
    rw [hT, ← map_pow, ← Matrix.SpecialLinearGroup.coe_pow, hgp,
      Matrix.SpecialLinearGroup.coe_one, map_one]
  obtain ⟨M, M', α, -, hM'M, hMM', hdiag, -⟩ :=
    CFSG.Quasithin.SteinbergBQ.exists_joint_eigenbasis hζ hpL0 hTp (one_pow p)
      (by rw [mul_one, one_mul])
  set μ : Fin 3 → L := fun i => (u : L) ^ (α i).val with hμ
  have hTM : T * M = M * Matrix.diagonal μ := by
    have : M * (M' * T * M) = M * Matrix.diagonal μ := by
      rw [hdiag]; rfl
    rwa [← mul_assoc, ← mul_assoc, hMM', one_mul] at this
  have hcol : ∀ j, T *ᵥ M.col j = μ j • M.col j := by
    intro j
    funext i
    have h := congrFun (congrFun hTM i) j
    rw [Matrix.mul_diagonal, Matrix.mul_apply] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
    rw [h, mul_comm]
  have hcol0 : ∀ j, M.col j ≠ 0 := by
    intro j h0
    have h1 : M' *ᵥ M.col j = Pi.single j 1 := by
      have hc : M.col j = M *ᵥ Pi.single j 1 := by
        funext i
        rw [Matrix.mulVec_single_one, Matrix.col_apply]
      rw [hc, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    have := congrFun h1 j
    simp at this
  obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hd : Matrix.diagonal μ = 1 := by
      rw [← Matrix.diagonal_one]; congr 1; funext i; exact hall i
    have hT1 : T = 1 := by
      have : T = M * Matrix.diagonal μ * M' := by
        rw [← hTM, mul_assoc, hMM', mul_one]
      rw [this, hd, mul_one, hMM']
    have hg1 : g = 1 := by
      apply Subtype.ext
      apply Matrix.map_injective f.injective
      show (g : Matrix (Fin 3) (Fin 3) K).map f =
        ((1 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map f
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.map_one (⇑f) f.map_zero f.map_one]
      rw [hT, RingHom.mapMatrix_apply] at hT1
      exact hT1
    rw [hg1, orderOf_one] at hg
    exact hp.one_lt.ne' hg.symm
  obtain ⟨l, hl⟩ : ∃ l, μ j = l := ⟨_, rfl⟩
  have hl0 : l ≠ 0 := by rw [← hl]; exact pow_ne_zero _ (Units.ne_zero u)
  have hlp : l ^ p = 1 := by
    rw [← hl, hμ]
    simp only
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hlne : l ≠ 1 := hl ▸ hj
  have hlord : orderOf l = p := orderOf_eq_prime hlp hlne
  set Fv : (Fin 3 → L) → (Fin 3 → L) := fun v i => Fr (v i) with hFv
  have hTfix : ∀ i k, Fr (T i k) = T i k := by
    intro i k
    rw [hT, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Fr.commutes _
  have hFv_mul : ∀ v, T *ᵥ Fv v = Fv (T *ᵥ v) := by
    intro v
    funext i
    simp only [hFv, Matrix.mulVec, dotProduct, map_sum, map_mul, hTfix]
  have hFv_eig : ∀ (c : L) (v : Fin 3 → L), T *ᵥ v = c • v → T *ᵥ Fv v = c ^ q • Fv v := by
    intro c v hv
    rw [hFv_mul, hv]
    funext i
    simp only [hFv, Pi.smul_apply, smul_eq_mul, hFrap, mul_pow]
  have hFv0 : ∀ v : Fin 3 → L, v ≠ 0 → Fv v ≠ 0 := by
    intro v hv h0
    apply hv
    funext i
    have := congrFun h0 i
    simp only [hFv, Pi.zero_apply] at this
    simpa using (map_eq_zero_iff Fr Fr.injective).1 this
  set v₀ := M.col j
  set v₁ := Fv v₀
  set v₂ := Fv v₁
  have hv₀ : T *ᵥ v₀ = l • v₀ := hl ▸ hcol j
  have hv₁ : T *ᵥ v₁ = l ^ q • v₁ := hFv_eig l v₀ hv₀
  have hv₂ : T *ᵥ v₂ = l ^ (q ^ 2) • v₂ := by
    have := hFv_eig (l ^ q) v₁ hv₁
    rwa [← pow_mul, ← sq] at this
  have hne₀ : v₀ ≠ 0 := hcol0 j
  have hne₁ : v₁ ≠ 0 := hFv0 _ hne₀
  have hne₂ : v₂ ≠ 0 := hFv0 _ hne₁
  have hpow_ne : ∀ n : ℕ, 1 ≤ n → l ^ n = l → p ∣ n - 1 := by
    intro n hn h
    have h1 : l ^ (n - 1) = 1 := by
      have : l ^ (n - 1) * l = 1 * l := by
        rw [← pow_succ, Nat.sub_add_cancel hn, one_mul, h]
      exact mul_right_cancel₀ hl0 this
    rw [← hlord]
    exact orderOf_dvd_of_pow_eq_one h1
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hd01 : l ≠ l ^ q := fun h => hpq1 (hpow_ne q hq1 h.symm)
  have hd02 : l ≠ l ^ (q ^ 2) := by
    intro h
    have h1 := hpow_ne (q ^ 2) hq2 h.symm
    have he : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      obtain ⟨m, hm⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      have : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
      omega
    rw [he] at h1
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exact hpq1 h2
    · exact hpq2 h2
  have hd12 : l ^ q ≠ l ^ (q ^ 2) := by
    intro h
    apply hd01
    apply Fr.injective
    rw [hFrap, hFrap, ← pow_mul, ← sq]
    exact h
  set ev : Fin 3 → L := ![l, l ^ q, l ^ (q ^ 2)] with hev
  set vs : Fin 3 → (Fin 3 → L) := ![v₀, v₁, v₂] with hvs
  have hvs_eig : ∀ k, T *ᵥ vs k = ev k • vs k := by
    intro k
    fin_cases k
    · exact hv₀
    · exact hv₁
    · exact hv₂
  have hvs0 : ∀ k, vs k ≠ 0 := by
    intro k
    fin_cases k
    · exact hne₀
    · exact hne₁
    · exact hne₂
  have hev_inj : Function.Injective ev := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd hab hd01
    · exact absurd hab hd02
    · exact absurd hab.symm hd01
    · rfl
    · exact absurd hab hd12
    · exact absurd hab.symm hd02
    · exact absurd hab.symm hd12
    · rfl
  have hli : LinearIndependent L vs := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' T) ev hev_inj vs fun k => ?_
    refine ⟨?_, hvs0 k⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hvs_eig k
  set s : Matrix (Fin 3) (Fin 3) L := Matrix.of fun i k => vs k i with hs
  have hscol : s.col = vs := by
    funext k i
    rfl
  refine ⟨l, s, hlord, ?_, ?_⟩
  · rw [← Matrix.linearIndependent_cols_iff_isUnit, hscol]
    exact hli
  · ext i k
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    have h := congrFun (hvs_eig k) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    change ∑ x, T i x * vs k x = vs k i * ev k
    rw [h, mul_comm]

@[expose] noncomputable def singerDiag {L : Type*} [Field L] (q : ℕ) (l : L)
    (hl : l * l ^ q * l ^ (q ^ 2) = 1) : Matrix.SpecialLinearGroup (Fin 3) L :=
  ⟨Matrix.diagonal ![l, l ^ q, l ^ (q ^ 2)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    exact hl⟩

theorem singerDiag_det_eq {L : Type*} [Field L] {q p : ℕ} {l : L} (hlp : l ^ p = 1)
    (hpq : p ∣ q ^ 2 + q + 1) : l * l ^ q * l ^ (q ^ 2) = 1 := by
  obtain ⟨k, hk⟩ := hpq
  have h : l * l ^ q * l ^ (q ^ 2) = l ^ (q ^ 2 + q + 1) := by ring
  rw [h, hk, pow_mul, hlp, one_pow]

theorem exists_sl3_conj_singerDiag {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpr : p ≠ r)
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : orderOf g = p) :
    ∃ (l : FiniteField.Extension K r 3) (hl : l * l ^ Nat.card K * l ^ (Nat.card K ^ 2) = 1)
      (s : Matrix.SpecialLinearGroup (Fin 3) (FiniteField.Extension K r 3)),
      orderOf l = p ∧
      Matrix.SpecialLinearGroup.map (algebraMap K (FiniteField.Extension K r 3)) g =
        s * singerDiag (Nat.card K) l hl * s⁻¹ := by
  obtain ⟨l, s₀, hlord, hs₀, hconj⟩ := exists_conj_diag_of_orderOf hp hp3 hpr hpq hg
  have hlp : l ^ p = 1 := by rw [← hlord]; exact pow_orderOf_eq_one l
  have hl := singerDiag_det_eq hlp hpq
  have hd : IsUnit s₀.det := (Matrix.isUnit_iff_isUnit_det s₀).1 hs₀
  set d := s₀.det with hddef
  have hd0 : d ≠ 0 := hd.ne_zero
  set c : Matrix (Fin 3) (Fin 3) (FiniteField.Extension K r 3) :=
    Matrix.diagonal ![d⁻¹, 1, 1] with hc
  set s₁ : Matrix (Fin 3) (Fin 3) (FiniteField.Extension K r 3) := s₀ * c with hs₁
  have hdet : s₁.det = 1 := by
    rw [hs₁, Matrix.det_mul, hc, Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    rw [← hddef, mul_inv_cancel₀ hd0]
  let s : Matrix.SpecialLinearGroup (Fin 3) (FiniteField.Extension K r 3) := ⟨s₁, hdet⟩
  have hcomm : c * Matrix.diagonal ![l, l ^ Nat.card K, l ^ (Nat.card K ^ 2)] =
      Matrix.diagonal ![l, l ^ Nat.card K, l ^ (Nat.card K ^ 2)] * c := by
    rw [hc, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hmul : Matrix.SpecialLinearGroup.map (algebraMap K (FiniteField.Extension K r 3)) g * s =
      s * singerDiag (Nat.card K) l hl := by
    apply Subtype.ext
    change (algebraMap K (FiniteField.Extension K r 3)).mapMatrix
      (g : Matrix (Fin 3) (Fin 3) K) * s₁ =
      s₁ * Matrix.diagonal ![l, l ^ Nat.card K, l ^ (Nat.card K ^ 2)]
    rw [hs₁, ← mul_assoc, hconj, mul_assoc, ← hcomm, ← mul_assoc]
  refine ⟨l, hl, s, hlord, ?_⟩
  rw [← hmul, mul_inv_cancel_right]

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
