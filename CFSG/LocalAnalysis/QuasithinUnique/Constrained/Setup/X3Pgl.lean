module

public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.GorensteinWalter CFSG.LinearGroups CFSG.Semidihedral.MatrixCoverData
  CFSG.Semidihedral.ProjectiveNonsquareInvolutions

universe u

variable {K : Type u} [Field K]

section Basic

@[expose] noncomputable def pglS (K : Type u) [Field K] : Subgroup (PGL2 K) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range

theorem pglS_index [Finite K] (hK : ringChar K ≠ 2) : (pglS K).index = 2 :=
  pgl2_psl2Range_index_eq_two K (isOddPrimePower_card_of_ringChar_ne_two hK)

theorem pglS_normal [Finite K] (hK : ringChar K ≠ 2) : (pglS K).Normal :=
  Subgroup.normal_of_index_eq_two (pglS_index hK)

theorem pglS_bijective : Function.Bijective
    ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).rangeRestrict) :=
  ⟨fun _ _ h => Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (congrArg Subtype.val h),
    MonoidHom.rangeRestrict_surjective _⟩

theorem card_le_four_of_elementaryAbelian
    [Finite K] (hK : ringChar K ≠ 2)
    (B : Subgroup (PGL2 K)) [CFSG.IsElementaryAbelian 2 B] : Nat.card B ≤ 4 := by
  have hodd := isOddPrimePower_card_of_ringChar_ne_two hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PGL2 K) := Finite.of_injective _
    (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglEquivCoordinateD K).injective
  by_contra hlt
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.IsElementaryAbelian.isPGroup 2 B)
  have h4 : 2 ^ 2 ∣ Nat.card B := by
    rw [hn]
    refine pow_dvd_pow 2 ?_
    by_contra h
    rw [hn] at hlt
    interval_cases n <;> simp_all
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  have hcard : Nat.card (W.map B.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hW]
    norm_num
  have hsq (x : W.map B.subtype) : x ^ 2 = 1 := by
    obtain ⟨w, -, hw⟩ := x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hw]
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) (w : PGL2 K) w.2
    simpa using this
  have hC := pgl2_kleinFour_centralizer_eq_self K hodd _ (isKleinFour_of_card_eq_four hcard hsq)
  have hle : B ≤ W.map B.subtype := by
    rw [← hC]
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, -, rfl⟩
    exact congrArg Subtype.val ((inferInstance : IsMulCommutative B).is_comm.comm w ⟨b, hb⟩)
  have := Subgroup.card_le_of_le hle
  rw [hcard] at this
  omega

end Basic

section Pairing

theorem trace_eq_zero_of_sq_mem_center {T : GL2 K} (hsq : T ^ 2 ∈ Subgroup.center (GL2 K))
    (hT : T ∉ Subgroup.center (GL2 K)) : Matrix.trace (T : Matrix (Fin 2) (Fin 2) K) = 0 := by
  by_contra ht
  apply hT
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hsq ⊢
  obtain ⟨l, hl⟩ := hsq
  have hm : (T : Matrix (Fin 2) (Fin 2) K) ^ 2 = Matrix.scalar (Fin 2) (l : K) :=
    congrArg Units.val hl.symm
  have hch := cayley_hamilton_two K (T : Matrix (Fin 2) (Fin 2) K)
  rw [hm] at hch
  let c := ((l : K) + Matrix.det (T : Matrix (Fin 2) (Fin 2) K)) /
    Matrix.trace (T : Matrix (Fin 2) (Fin 2) K)
  have he : (T : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) c := by
    ext i j
    have h := congrArg (fun X : Matrix (Fin 2) (Fin 2) K => X i j) hch
    fin_cases i <;> fin_cases j
    · simp [Matrix.scalar_apply, Matrix.diagonal] at h ⊢
      dsimp [c]
      field_simp [ht]
      linear_combination -h
    · simp [Matrix.scalar_apply, Matrix.diagonal] at h ⊢
      exact h.resolve_left ht
    · simp [Matrix.scalar_apply, Matrix.diagonal] at h ⊢
      exact h.resolve_left ht
    · simp [Matrix.scalar_apply, Matrix.diagonal] at h ⊢
      dsimp [c]
      field_simp [ht]
      linear_combination -h
  have hc0 : c ≠ 0 := by
    intro hz
    have hd := (Matrix.GeneralLinearGroup.det T).ne_zero
    have hdet : (Matrix.GeneralLinearGroup.det T : K) = 0 := by
      change Matrix.det (T : Matrix (Fin 2) (Fin 2) K) = 0
      rw [he, hz]
      simp
    exact hd hdet
  exact ⟨Units.mk0 c hc0, Units.ext he.symm⟩

theorem exists_sq_add_mul_sq [Finite K] (hK : ringChar K ≠ 2) {a : K} (ha : a ≠ 0) (c : K) :
    ∃ x y : K, x ^ 2 + a * y ^ 2 = c := by
  have := Fintype.ofFinite K
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 - Polynomial.C c) (g := Polynomial.C a * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_sub_C (by norm_num) c) (Polynomial.degree_C_mul_X_pow 2 ha)
    (FiniteField.odd_card_of_char_ne_two hK)
  refine ⟨x, y, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul] at h
  linear_combination h

theorem exists_anticommuting [Finite K] (hK : ringChar K ≠ 2) (a : Kˣ) :
    ∃ R₀ : GL2 K, Matrix.trace (R₀ : Matrix (Fin 2) (Fin 2) K) = 0 ∧
      Matrix.GeneralLinearGroup.det R₀ = a ∧
      (R₀ : Matrix (Fin 2) (Fin 2) K) * (J K a : Matrix (Fin 2) (Fin 2) K) =
        -((J K a : Matrix (Fin 2) (Fin 2) K) * (R₀ : Matrix (Fin 2) (Fin 2) K)) ∧
      ∀ c : Kˣ, R₀ ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  obtain ⟨p, r, hpr⟩ := exists_sq_add_mul_sq hK a.ne_zero (-(a : K))
  have hdet : Matrix.det !![p, (a : K) * r; r, -p] = (a : K) := by
    rw [Matrix.det_fin_two_of]
    linear_combination -hpr
  have hdet0 : Matrix.det !![p, (a : K) * r; r, -p] ≠ 0 := by
    rw [hdet]
    exact a.ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![p, (a : K) * r; r, -p] hdet0, ?_, ?_, ?_, ?_⟩
  · simp [Matrix.trace_fin_two, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  · exact Units.ext hdet
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, J_matrix, Matrix.mul_apply, Fin.sum_univ_two]
      <;> ring
  · intro c hc
    have h10 := congrArg (fun g : GL2 K => (g : Matrix (Fin 2) (Fin 2) K) 1 0) hc
    have h00 := congrArg (fun g : GL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hc
    have h11 := congrArg (fun g : GL2 K => (g : Matrix (Fin 2) (Fin 2) K) 1 1) hc
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.scalar_apply,
      Matrix.diagonal] at h10 h00 h11
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hp : p = 0 := by
      have : (2 : K) * p = 0 := by linear_combination h00 - h11
      exact (mul_eq_zero.mp this).resolve_left h2
    rw [hp, h10] at hpr
    apply a.ne_zero
    linear_combination hpr

theorem exists_commuting_det [Finite K] (hK : ringChar K ≠ 2) {T : GL2 K}
    (htr : Matrix.trace (T : Matrix (Fin 2) (Fin 2) K) = 0) (δ : Kˣ) :
    ∃ z : GL2 K, (z : Matrix (Fin 2) (Fin 2) K) * T = T * z ∧
      Matrix.GeneralLinearGroup.det z = δ := by
  have ha : (Matrix.GeneralLinearGroup.det T : K) =
      (T : Matrix (Fin 2) (Fin 2) K) 0 0 * (T : Matrix (Fin 2) (Fin 2) K) 1 1 -
        (T : Matrix (Fin 2) (Fin 2) K) 0 1 * (T : Matrix (Fin 2) (Fin 2) K) 1 0 :=
    Matrix.det_fin_two _
  obtain ⟨x, y, hxy⟩ := exists_sq_add_mul_sq hK (Matrix.GeneralLinearGroup.det T).ne_zero (δ : K)
  have h11 : (T : Matrix (Fin 2) (Fin 2) K) 1 1 = -(T : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    rw [Matrix.trace_fin_two] at htr
    linear_combination htr
  let Z : Matrix (Fin 2) (Fin 2) K := x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (T : Matrix _ _ K)
  have hdetZ : Z.det = δ := by
    rw [Matrix.det_fin_two]
    simp only [Z, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
      Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one, smul_eq_mul, mul_one,
      mul_zero, zero_add]
    rw [h11]
    rw [ha, h11] at hxy
    linear_combination hxy
  have hdet0 : Z.det ≠ 0 := by
    rw [hdetZ]
    exact δ.ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Z hdet0, ?_, Units.ext hdetZ⟩
  change Z * (T : Matrix (Fin 2) (Fin 2) K) = (T : Matrix (Fin 2) (Fin 2) K) * Z
  simp [Z, add_mul, mul_add]

theorem exists_anticommuting_conj [Finite K] (hK : ringChar K ≠ 2) {T : GL2 K}
    (htr : Matrix.trace (T : Matrix (Fin 2) (Fin 2) K) = 0) (hT : T ∉ Subgroup.center (GL2 K)) :
    ∃ s R : GL2 K, Matrix.GeneralLinearGroup.det s = 1 ∧ s⁻¹ * T * s = R ∧
      (R : Matrix (Fin 2) (Fin 2) K) * (T : Matrix (Fin 2) (Fin 2) K) =
        -((T : Matrix (Fin 2) (Fin 2) K) * (R : Matrix (Fin 2) (Fin 2) K)) := by
  have hns : ∀ c : Kˣ, T ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) c := fun c hc =>
    hT (by rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨c, hc.symm⟩)
  obtain ⟨P, hP⟩ := companion_conjugator K T (Matrix.GeneralLinearGroup.det T) htr rfl hns
  obtain ⟨R₀, hR₀tr, hR₀det, hR₀anti, hR₀ns⟩ :=
    exists_anticommuting hK (Matrix.GeneralLinearGroup.det T)
  obtain ⟨P', hP'⟩ := companion_conjugator K R₀ (Matrix.GeneralLinearGroup.det T) hR₀tr hR₀det hR₀ns
  have hT' : T = P * J K (Matrix.GeneralLinearGroup.det T) * P⁻¹ := by
    calc T = P * (P⁻¹ * T * P) * P⁻¹ := by group
      _ = P * J K (Matrix.GeneralLinearGroup.det T) * P⁻¹ := by rw [hP]
  have hR₀' : R₀ = P' * J K (Matrix.GeneralLinearGroup.det T) * P'⁻¹ := by
    calc R₀ = P' * (P'⁻¹ * R₀ * P') * P'⁻¹ := by group
      _ = P' * J K (Matrix.GeneralLinearGroup.det T) * P'⁻¹ := by rw [hP']
  obtain ⟨z, hzT, hzdet⟩ := exists_commuting_det hK htr
    (Matrix.GeneralLinearGroup.det (P * P' * P⁻¹)⁻¹⁻¹)
  have hzT' : z * T = T * z := Units.ext hzT
  refine ⟨z * (P * P' * P⁻¹)⁻¹, P * R₀ * P⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, hzdet]
    simp
  · calc (z * (P * P' * P⁻¹)⁻¹)⁻¹ * T * (z * (P * P' * P⁻¹)⁻¹) =
          (P * P' * P⁻¹) * (z⁻¹ * T * z) * (P * P' * P⁻¹)⁻¹ := by group
      _ = (P * P' * P⁻¹) * T * (P * P' * P⁻¹)⁻¹ := by
          rw [show z⁻¹ * T * z = T by rw [mul_assoc, ← hzT', ← mul_assoc, inv_mul_cancel,
            one_mul]]
      _ = P * R₀ * P⁻¹ := by
          conv_lhs => rw [hT']
          rw [hR₀']
          group
  · have h1 : P * R₀ * P⁻¹ * T = P * (R₀ * J K (Matrix.GeneralLinearGroup.det T)) * P⁻¹ := by
      conv_lhs => rw [hT']
      group
    have h2 : T * (P * R₀ * P⁻¹) = P * (J K (Matrix.GeneralLinearGroup.det T) * R₀) * P⁻¹ := by
      conv_lhs => rw [hT']
      group
    rw [← Units.val_mul, ← Units.val_mul, h1, h2]
    simp only [Units.val_mul]
    rw [hR₀anti]
    simp [Matrix.mul_assoc]

theorem exists_commuting_conjugate [Finite K] (hK : ringChar K ≠ 2) {t : PGL2 K} (ht2 : t * t = 1)
    (ht1 : t ≠ 1) :
    ∃ s ∈ pglS K, s⁻¹ * t * s ≠ t ∧ t * (s⁻¹ * t * s) = (s⁻¹ * t * s) * t := by
  obtain ⟨T, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective t
  have hsq : T ^ 2 ∈ Subgroup.center (GL2 K) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    rw [map_pow, pow_two, ht2]
  have hT : T ∉ Subgroup.center (GL2 K) := fun h => ht1 (Matrix.ProjGenLinGroup.mk_eq_one.mpr h)
  have htr := trace_eq_zero_of_sq_mem_center hsq hT
  obtain ⟨s, R, hsdet, hsR, hRT⟩ := exists_anticommuting_conj hK htr hT
  have hs1 : (s : Matrix (Fin 2) (Fin 2) K).det = 1 := congrArg Units.val hsdet
  let X : Matrix.SpecialLinearGroup (Fin 2) K := ⟨(s : Matrix (Fin 2) (Fin 2) K), hs1⟩
  have hX : Matrix.SpecialLinearGroup.toGL X = s := Units.ext rfl
  have hconj : (Matrix.ProjGenLinGroup.mk s)⁻¹ * Matrix.ProjGenLinGroup.mk T *
      Matrix.ProjGenLinGroup.mk s = Matrix.ProjGenLinGroup.mk R := by
    rw [← map_inv, ← map_mul, ← map_mul, hsR]
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine ⟨Matrix.ProjGenLinGroup.mk s, ⟨(QuotientGroup.mk X : PSL2 K), ?_⟩, ?_, ?_⟩
  · rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, hX]
  · rw [hconj]
    intro h
    have h' : Matrix.ProjGenLinGroup.mk (R⁻¹ * T) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have hmem := Matrix.ProjGenLinGroup.mk_eq_one.mp h'
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hTc : T = R * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
      rw [hc]
      group
    have hcomm : (T : Matrix (Fin 2) (Fin 2) K) * R = R * T := by
      have hsc := (Matrix.scalar_commute (c : K) (fun r => Commute.all (c : K) r)
        (R : Matrix (Fin 2) (Fin 2) K)).eq
      conv_lhs => rw [hTc]
      conv_rhs => rw [hTc]
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
      rw [Matrix.mul_assoc, ← hsc, ← Matrix.mul_assoc]
    have h1 : (R : Matrix (Fin 2) (Fin 2) K) * T = -((R : Matrix (Fin 2) (Fin 2) K) * T) := by
      calc (R : Matrix (Fin 2) (Fin 2) K) * T = -((T : Matrix (Fin 2) (Fin 2) K) * R) := hRT
        _ = -((R : Matrix (Fin 2) (Fin 2) K) * T) := by rw [hcomm]
    have h2' : (2 : K) • ((R : Matrix (Fin 2) (Fin 2) K) * T) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h1]
      exact neg_add_cancel _
    have h3 : (R : Matrix (Fin 2) (Fin 2) K) * T = 0 := by
      have := congrArg (fun M => (2 : K)⁻¹ • M) h2'
      simp [smul_smul, h2] at this
    exact Units.ne_zero (R * T) (by simp at h3 ⊢)
  · rw [hconj, ← map_mul, ← map_mul]
    have hneg : (Matrix.scalar (Fin 2) (-1 : K)) = (-1 : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
    have hTR : T * R = Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) * (R * T) := by
      apply Units.ext
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg,
        Units.val_one, hneg, neg_mul, one_mul]
      rw [hRT, neg_neg]
    rw [hTR, map_mul, Matrix.ProjGenLinGroup.mk_eq_one.mpr
      (by rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨-1, rfl⟩), one_mul]

theorem projective_involution_pairing
    (K : Type u) [Field K] [Finite K] (hK : ringChar K ≠ 2) :
    (pglS K).Normal ∧ (pglS K).index = 2 ∧
      Function.Bijective
        ((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).rangeRestrict) ∧
      (∀ (B : Subgroup (PGL2 K)) [CFSG.IsElementaryAbelian 2 B], Nat.card B ≤ 4) ∧
      ∀ t : PGL2 K, t * t = 1 → t ≠ 1 →
        ∃ s ∈ pglS K, s⁻¹ * t * s ≠ t ∧ Commute t (s⁻¹ * t * s) :=
  ⟨pglS_normal hK, pglS_index hK, pglS_bijective, fun B _ => card_le_four_of_elementaryAbelian hK B,
    fun _ ht2 ht1 => exists_commuting_conjugate hK ht2 ht1⟩

end Pairing

end CFSG.QuasithinUnique.Setup.X3
