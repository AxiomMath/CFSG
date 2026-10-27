module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk412Mat

public section

open Polynomial Subgroup CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.GLS.IVK.Proofs2

section LinExist

variable {F : Type} [Field F] [Finite F]

theorem irreducible_X_sq_add_one' (h4 : Nat.card F % 4 = 3) : Irreducible (X ^ 2 + 1 : F[X]) := by
  have := Fintype.ofFinite F
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc]
    have : (X ^ 2 + 1 : F[X]).natDegree = 2 := by simp
    omega
  · intro x hx
    have h0 : x ^ 2 + 1 = 0 := by simpa using hx
    have hsq : IsSquare (-1 : F) := ⟨x, by linear_combination -h0⟩
    rw [FiniteField.isSquare_neg_one_iff] at hsq
    rw [← Nat.card_eq_fintype_card] at hsq
    exact hsq h4

@[expose] def innerAlgHom (d : Matrix (Fin 2) (Fin 2) F) (hd : d * d = 1) :
    Matrix (Fin 2) (Fin 2) F →ₐ[F] Matrix (Fin 2) (Fin 2) F where
  toFun x := d * x * d
  map_one' := by simp [hd]
  map_mul' x y := by
    calc d * (x * y) * d = d * x * (d * d) * y * d := by rw [hd]; simp [mul_assoc]
      _ = d * x * d * (d * y * d) := by simp [mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]
  commutes' a := by
    rw [← Algebra.commutes, mul_assoc, hd, mul_one]


theorem exists_field_ext (h4 : Nat.card F % 4 = 3) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (φ : E →+* Matrix (Fin 2) (Fin 2) F),
      Nat.card E = Nat.card F ^ 2 ∧
      ∀ e : E, (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) * φ e * !![1, 0; 0, -1] =
        φ (e ^ Nat.card F) := by
  have : Fact (Irreducible (X ^ 2 + 1 : F[X])) := ⟨irreducible_X_sq_add_one' h4⟩
  have hf : (X ^ 2 + 1 : F[X]) ≠ 0 := (Fact.out : Irreducible (X ^ 2 + 1 : F[X])).ne_zero
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by simp
  let pb := AdjoinRoot.powerBasis hf
  have : Module.Finite F (AdjoinRoot (X ^ 2 + 1 : F[X])) := pb.finite
  have : Finite (AdjoinRoot (X ^ 2 + 1 : F[X])) := Module.finite_of_finite F
  let J' : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0]
  have hJ' : aeval J' (X ^ 2 + 1 : F[X]) = 0 := by
    simp only [map_add, map_pow, aeval_X, map_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J', pow_two]
  let φ : AdjoinRoot (X ^ 2 + 1 : F[X]) →ₐ[F] Matrix (Fin 2) (Fin 2) F :=
    Ideal.Quotient.liftₐ (Ideal.span {(X ^ 2 + 1 : F[X])}) (aeval J') (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 ha
      simp [hJ'])
  have hr2 : (AdjoinRoot.root (X ^ 2 + 1 : F[X])) ^ 2 = -1 := by
    have := AdjoinRoot.eval₂_root (X ^ 2 + 1 : F[X])
    simp at this
    linear_combination this
  have hφroot : φ (AdjoinRoot.root (X ^ 2 + 1 : F[X])) = J' := by
    show Ideal.Quotient.liftₐ (Ideal.span {(X ^ 2 + 1 : F[X])}) (aeval J') _
      (Ideal.Quotient.mk (Ideal.span {(X ^ 2 + 1 : F[X])}) X) = J'
    exact aeval_X J'
  have hcard : Nat.card (AdjoinRoot (X ^ 2 + 1 : F[X])) = Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), pb.finrank, AdjoinRoot.powerBasis_dim, hdeg]
  refine ⟨AdjoinRoot (X ^ 2 + 1 : F[X]), inferInstance, inferInstance, φ.toRingHom, hcard, ?_⟩
  have := Fintype.ofFinite F
  have hdd : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 0, -1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hroot_pow : (AdjoinRoot.root (X ^ 2 + 1 : F[X])) ^ Nat.card F =
      -AdjoinRoot.root (X ^ 2 + 1 : F[X]) := by
    obtain ⟨k, hk⟩ : ∃ k, Nat.card F = 4 * k + 3 := ⟨Nat.card F / 4, by omega⟩
    rw [hk]
    calc (AdjoinRoot.root (X ^ 2 + 1 : F[X])) ^ (4 * k + 3) =
        ((AdjoinRoot.root (X ^ 2 + 1 : F[X])) ^ 2) ^ (2 * k + 1) *
          AdjoinRoot.root (X ^ 2 + 1 : F[X]) := by ring
      _ = -AdjoinRoot.root (X ^ 2 + 1 : F[X]) := by
        rw [hr2, Odd.neg_one_pow ⟨k, rfl⟩, neg_one_mul]
  have key : (innerAlgHom (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) hdd).comp φ =
      φ.comp (FiniteField.frobeniusAlgHom F (AdjoinRoot (X ^ 2 + 1 : F[X]))) := by
    apply AdjoinRoot.algHom_ext
    have h1 : (innerAlgHom (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) hdd) J' = -J' := by
      show (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) * J' * !![1, 0; 0, -1] = -J'
      ext i j
      fin_cases i <;> fin_cases j <;> simp [J', Matrix.mul_apply, Fin.sum_univ_two]
    have h2 : (FiniteField.frobeniusAlgHom F (AdjoinRoot (X ^ 2 + 1 : F[X])))
        (AdjoinRoot.root (X ^ 2 + 1 : F[X])) = -AdjoinRoot.root (X ^ 2 + 1 : F[X]) := by
      rw [FiniteField.coe_frobeniusAlgHom, ← Nat.card_eq_fintype_card]
      exact hroot_pow
    simp only [AlgHom.comp_apply, hφroot, h2, map_neg, h1]
  intro e
  have := congrArg (fun ψ => ψ e) key
  simp only [AlgHom.comp_apply, FiniteField.coe_frobeniusAlgHom] at this
  rw [← Nat.card_eq_fintype_card] at this
  exact this

end LinExist
theorem exists_pow_two_pow_eq_neg_one (E : Type) [Field E] [Finite E] {w t : ℕ} (hw : 0 < w)
    (hN : Nat.card E - 1 = w * 2 ^ (t + 1)) : ∃ ζ : Eˣ, (ζ : E) ^ 2 ^ t = -1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hord : orderOf g = w * 2 ^ (t + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hN]
  refine ⟨g ^ w, ?_⟩
  have hx : ((g ^ w) ^ 2 ^ t : Eˣ) * ((g ^ w) ^ 2 ^ t : Eˣ) = 1 := by
    have : ((g ^ w) ^ 2 ^ t : Eˣ) * ((g ^ w) ^ 2 ^ t : Eˣ) = g ^ orderOf g := by
      rw [← pow_mul, ← pow_add, hord]
      congr 1
      ring
    rw [this]
    exact pow_orderOf_eq_one g
  have hne : ((g ^ w) ^ 2 ^ t : Eˣ) ≠ 1 := by
    intro h
    rw [← pow_mul] at h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hd
    have hle := Nat.le_of_dvd (by positivity) hd
    have : w * 2 ^ t < w * 2 ^ (t + 1) := by
      apply Nat.mul_lt_mul_of_pos_left _ hw
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hx' : (((g ^ w) ^ 2 ^ t : Eˣ) : E) * (((g ^ w) ^ 2 ^ t : Eˣ) : E) = 1 := by
    have := congrArg (fun u : Eˣ => (u : E)) hx
    simpa using this
  rcases mul_self_eq_one_iff.1 hx' with h | h
  · exact absurd (Units.ext h) hne
  · rw [← Units.val_pow_eq_pow_val]
    exact h

theorem arith_lin (q : ℕ) (h4 : q % 4 = 3) :
    ∃ s j a : ℕ, 2 ≤ s ∧ Odd j ∧ Odd a ∧ q = 2 * a + 1 ∧ q + 1 = 2 ^ s * j ∧
      q ^ 2 - 1 = (a * j) * 2 ^ (s + 1) := by
  obtain ⟨s, j, hj, hqs⟩ := Nat.exists_eq_two_pow_mul_odd (n := q + 1) (by omega)
  have hs : 2 ≤ s := by
    by_contra h
    replace h := not_le.1 h
    interval_cases s
    · obtain ⟨t, rfl⟩ := hj
      omega
    · obtain ⟨t, rfl⟩ := hj
      omega
  have hq : q = 2 * ((q - 1) / 2) + 1 := by omega
  refine ⟨s, j, (q - 1) / 2, hs, hj, ⟨(q - 1) / 4, by omega⟩, hq, hqs, ?_⟩
  have h1 : q ^ 2 - 1 = 2 * ((q - 1) / 2) * (q + 1) := by
    obtain ⟨b, hb⟩ : ∃ b, q = 2 * b + 1 := ⟨(q - 1) / 2, hq⟩
    subst hb
    have : (2 * ((2 * b + 1 - 1) / 2) ) = 2 * b := by omega
    rw [this]
    have e : (2 * b + 1) ^ 2 = 2 * b * (2 * b + 1 + 1) + 1 := by ring
    omega
  rw [h1, hqs]
  ring

section LinExist2

variable {F : Type} [Field F] [Finite F]

theorem exists_rotData_lin (h4 : Nat.card F % 4 = 3) :
    ∃ (n : ℕ) (D : RotData (ModelData.lin F)), 3 ≤ n ∧ D.R ^ 2 ^ (n - 1) = -1 ∧
      ∃ h' : ℕ, Odd h' ∧ Nat.card ↥(ModelData.lin F).H2 = 2 ^ n * h' := by
  obtain ⟨s, j, a, hs, hj, ha, hqa, hqs, hq2⟩ := arith_lin (Nat.card F) h4
  obtain ⟨E, _, _, φ, hEcard, hconj⟩ := exists_field_ext (F := F) h4
  have hN : Nat.card E - 1 = (a * j) * 2 ^ (s + 1) := by rw [hEcard]; exact hq2
  obtain ⟨ζ, hζ⟩ := exists_pow_two_pow_eq_neg_one E (w := a * j)
    (Nat.mul_pos ha.pos hj.pos) hN
  have hqodd : Odd (Nat.card F) := ⟨a, by omega⟩
  have hζq : (ζ : E) ^ (Nat.card F + 1) = -1 := by
    rw [hqs, pow_mul, hζ]
    exact Odd.neg_one_pow hj
  have hζ0 : (ζ : E) ≠ 0 := ζ.ne_zero
  have hζq' : (ζ : E) ^ Nat.card F = -(ζ : E)⁻¹ := by
    have : (ζ : E) ^ Nat.card F * (ζ : E) = -1 := by rw [← pow_succ]; exact hζq
    field_simp
    linear_combination this
  let R : GL (Fin 2) F := Units.map (φ : E →* Matrix (Fin 2) (Fin 2) F) ζ
  have hRval : (R : Matrix (Fin 2) (Fin 2) F) = φ ζ := rfl
  have hRinv : ((R⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = φ (ζ : E)⁻¹ := by
    show ((Units.map (φ : E →* Matrix (Fin 2) (Fin 2) F) ζ)⁻¹ : GL (Fin 2) F).val = _
    rw [← map_inv, Units.coe_map, Units.val_inv_eq_inv_val]
    rfl
  have hcR : dRefl F * R * dRefl F = -R⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_neg, coe_dRefl, hRval, hRinv, hconj, hζq', map_neg]
  have hdet : (R : Matrix (Fin 2) (Fin 2) F).det * (R : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have h1 := congrArg Matrix.det (congrArg Units.val hcR)
    rw [Units.val_mul, Units.val_mul, Units.val_neg, Matrix.det_mul, Matrix.det_mul, coe_dRefl,
      Matrix.det_neg] at h1
    have h2 : (R : Matrix (Fin 2) (Fin 2) F).det * ((R⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    have h3 : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F).det = -1 := by
      simp [Matrix.det_fin_two]
    rw [h3] at h1
    simp only [Fintype.card_fin] at h1
    have h4 : (R : Matrix (Fin 2) (Fin 2) F).det =
        ((R⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det := by linear_combination h1
    calc (R : Matrix (Fin 2) (Fin 2) F).det * (R : Matrix (Fin 2) (Fin 2) F).det
        = (R : Matrix (Fin 2) (Fin 2) F).det *
          ((R⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det := by rw [← h4]
      _ = 1 := h2
  have hRn : R ^ 2 ^ s = -1 := by
    apply Units.ext
    have : ((R ^ 2 ^ s : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = φ ((ζ : E) ^ 2 ^ s) := by
      rw [Units.val_pow_eq_pow_val, hRval, map_pow]
    rw [this, hζ, map_neg, map_one, Units.val_neg, Units.val_one]
  refine ⟨s + 1, ⟨R, Subgroup.mem_top _, Subgroup.mem_top _, hdet, hcR⟩, by omega, ?_, ?_⟩
  · show R ^ 2 ^ (s + 1 - 1) = -1
    rw [Nat.add_sub_cancel]
    exact hRn
  · refine ⟨Nat.card F * (a * j), hqodd.mul (ha.mul hj), ?_⟩
    show Nat.card ↥(StatedSL 2 F) = _
    rw [CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSL_two, hq2]
    ring

theorem prop412_lin (h5 : 5 ≤ Nat.card F) (h4 : Nat.card F % 4 = 3) :
    Prop412 (PG (ModelData.lin F)) := by
  have h2 : (2 : F) ≠ 0 :=
    CFSG.GH74.L5U5.two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  have hG := goodModel_lin h2 h5
  have hZ := zsTwo_lin h4
  have hC := clsFacts_lin h2 h5 h4
  obtain ⟨n, D, hn, hRn, h', hh', hH⟩ := exists_rotData_lin (F := F) h4
  obtain ⟨o, ho, hcard⟩ := card_PG_eq_of_good hG hZ (card_U2_lin (F := F))
  obtain ⟨a', ha1, ha2⟩ : ∃ a', Nat.card F - 1 = 2 * a' ∧ Odd a' :=
    ⟨(Nat.card F - 1) / 2, by omega, ⟨Nat.card F / 4, by omega⟩⟩
  rw [hH, ha1] at hcard
  refine prop412_of_rotData D hG hZ hC hn hRn (m := o * a' * h' ^ 2)
    ((ho.mul ha2).mul (hh'.pow)) ?_
  rw [hcard]
  ring

end LinExist2

end CFSG.GH74.GLS.IVK.Proofs2
