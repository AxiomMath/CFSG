module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsNT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

universe u

variable {F : Type u} [Field F] [Finite F]

theorem pow_two_mul_sub_one_dvd {t u : ℕ} (ht : Odd t) (hu : Odd u) :
    ∃ S : ℕ, Odd S ∧ t ^ (2 * u) - 1 = (t ^ 2 - 1) * S := by
  refine ⟨∑ i ∈ Finset.range u, (t ^ 2) ^ i, ?_, ?_⟩
  · have h := odd_geom_sum (t := ((t ^ 2 : ℕ) : ℤ)) (by exact_mod_cast ht.pow) hu
    exact_mod_cast h
  · have h := geom_sum_mul ((t ^ 2 : ℕ) : ℤ) u
    have ht1 : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ ht.pos
    have htu : 1 ≤ t ^ (2 * u) := Nat.one_le_pow _ _ ht.pos
    have : ((t ^ (2 * u) - 1 : ℕ) : ℤ) = ((t ^ 2 - 1 : ℕ) : ℤ) * ((∑ i ∈ Finset.range u,
        (t ^ 2) ^ i : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub ht1, Nat.cast_sub htu] at h ⊢
      rw [show (t : ℤ) ^ (2 * u) = ((t : ℤ) ^ 2) ^ u by rw [← pow_mul]]
      linear_combination -h
    exact_mod_cast this

theorem isSquare_of_pow_eq_one {t u : ℕ} (ht : Odd t) (hu : Odd u) (hq : Nat.card F = t ^ 2)
    {δ : F} (hδ : δ ≠ 0) (h : δ ^ ((t ^ u - 1) * ((t ^ u + 1) / 2)) = 1) : IsSquare δ := by
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h2
    have := (FiniteField.even_card_iff_char_two (F := F)).mp h2
    rw [← Nat.card_eq_fintype_card, hq] at this
    have hodd := Nat.odd_iff.mp (ht.pow : Odd (t ^ 2))
    omega
  rw [FiniteField.isSquare_iff hchar hδ, ← Nat.card_eq_fintype_card, hq]
  obtain ⟨S, hS, hSeq⟩ := pow_two_mul_sub_one_dvd ht hu
  have htu : Odd (t ^ u) := ht.pow
  have h1 : (t ^ u - 1) * ((t ^ u + 1) / 2) = (t ^ 2 - 1) / 2 * S := by
    have e1 : (t ^ u - 1) * ((t ^ u + 1) / 2) = (t ^ (2 * u) - 1) / 2 := by
      obtain ⟨m, hm⟩ := htu
      rw [show t ^ (2 * u) = (t ^ u) ^ 2 by ring, hm]
      have : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [this, show (2 * m + 1) ^ 2 - 1 = 2 * ((2 * m) * (m + 1)) by ring_nf; omega,
        Nat.mul_div_cancel_left _ two_pos]
      rw [show 2 * m + 1 - 1 = 2 * m by omega]
    rw [e1, hSeq]
    obtain ⟨m, hm⟩ := (ht.pow : Odd (t ^ 2))
    rw [hm, show 2 * m + 1 - 1 = 2 * m by omega, mul_assoc, Nat.mul_div_cancel_left _ two_pos,
      Nat.mul_div_cancel_left _ two_pos]
  rw [h1] at h
  have hq1 : δ ^ (t ^ 2 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one δ hδ
    rwa [← Nat.card_eq_fintype_card, hq] at this
  have hg := (pow_gcd_eq_one (a := δ)).mpr ⟨h, hq1⟩
  have hgcd : Nat.gcd ((t ^ 2 - 1) / 2 * S) (t ^ 2 - 1) = (t ^ 2 - 1) / 2 := by
    obtain ⟨m, hm⟩ := (ht.pow : Odd (t ^ 2))
    rw [hm, show 2 * m + 1 - 1 = 2 * m by omega, Nat.mul_div_cancel_left _ two_pos]
    have hc : Nat.gcd S 2 = 1 := Nat.coprime_two_right.mpr hS
    rw [show 2 * m = m * 2 by ring, Nat.gcd_mul_left, hc, mul_one]
  rw [hgcd] at hg
  have hodd := Nat.odd_iff.mp (ht.pow : Odd (t ^ 2))
  rwa [show t ^ 2 / 2 = (t ^ 2 - 1) / 2 by omega]

omit [Finite F] in
theorem pgl2FieldAut_mk (σ : F ≃+* F) (A : GL (Fin 2) F) :
    pgl2FieldAut F σ (Matrix.ProjGenLinGroup.mk A) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map σ.toRingHom A) :=
  pgl2RingEquiv_mk σ A

omit [Finite F] in
theorem smul_left_cancel_of_det {b : Matrix (Fin 2) (Fin 2) F} (hb : b.det ≠ 0) {k k' : F}
    (h : k • b = k' • b) : k = k' := by
  by_contra hne
  have h' : (k - k') • b = 0 := by rw [sub_smul, h, sub_self]
  have := congrArg Matrix.det h'
  rw [Matrix.det_smul, Matrix.det_zero, Fintype.card_fin] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hne (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1))
  · exact hb h1

theorem mem_pslRange_of_commute_fieldInv {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ f) (x : PGammaL2 F) (hx2 : x * x = 1) (hxr : x.right ≠ 1)
    (g : PGL2 F) (hg : x * SemidirectProduct.inl g = SemidirectProduct.inl g * x) :
    SemidirectProduct.inl g ∈ pGammaL2PSLRange F := by
  set σ := x.right with hσdef
  have hσσ : σ * σ = 1 := by
    have := congrArg SemidirectProduct.right hx2
    simpa using this
  have hσ2 : orderOf σ = 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hσσ) hxr
  have hσσy : ∀ y : F, σ (σ y) = y := fun y => by
    have := congrArg (fun τ : F ≃+* F => τ y) hσσ
    simpa using this
  obtain ⟨t, u, ht, hu, hcard, hσx⟩ := exists_odd_pow_of_orderOf_two_pow hp hp2 hF σ le_rfl hσ2
  rw [pow_one] at hcard
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have h1 : Matrix.ProjGenLinGroup.mk (A * Matrix.GeneralLinearGroup.map σ.toRingHom A) = 1 := by
    have := congrArg SemidirectProduct.left hx2
    simp only [SemidirectProduct.mul_left, SemidirectProduct.one_left, ← hσdef] at this
    rw [← hA, pgl2FieldAut_mk] at this
    rw [map_mul]
    exact this
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨μ, hμ⟩ := h1
  have h2 : Matrix.ProjGenLinGroup.mk (A * Matrix.GeneralLinearGroup.map σ.toRingHom B) =
      Matrix.ProjGenLinGroup.mk (B * A) := by
    have := congrArg SemidirectProduct.left hg
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply, ← hσdef] at this
    rw [← hA, pgl2FieldAut_mk] at this
    rw [map_mul, map_mul]
    exact this
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h2
  set a : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) with ha
  set b : Matrix (Fin 2) (Fin 2) F := (B : Matrix (Fin 2) (Fin 2) F) with hb
  set m : Matrix (Fin 2) (Fin 2) F →+* Matrix (Fin 2) (Fin 2) F := σ.toRingHom.mapMatrix
  have hmap : ∀ C : GL (Fin 2) F,
      ((Matrix.GeneralLinearGroup.map σ.toRingHom C : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = m (C : Matrix (Fin 2) (Fin 2) F) := fun C => rfl
  have hmm : ∀ X : Matrix (Fin 2) (Fin 2) F, m (m X) = X := by
    intro X
    ext i j
    simp [m, hσσy]
  have hE1 : a * m a = (μ : F) • 1 := by
    have := congrArg (fun C : GL (Fin 2) F => (C : Matrix (Fin 2) (Fin 2) F)) hμ
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, hmap] at this
    rw [← this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hE2 : (c : F) • (a * m b) = b * a := by
    have := congrArg (fun C : GL (Fin 2) F => (C : Matrix (Fin 2) (Fin 2) F)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, hmap] at this
    rw [← this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]
  have hsm : ∀ (k : F) (X : Matrix (Fin 2) (Fin 2) F), m (k • X) = σ k • m X := by
    intro k X
    ext i j
    simp [m]
  have hE3 : σ (c : F) • (m a * b) = m b * m a := by
    have := congrArg m hE2
    rw [hsm, map_mul, map_mul, hmm] at this
    exact this
  have hdetb : b.det ≠ 0 := B.det_ne_zero
  have hdeta : a.det ≠ 0 := A.det_ne_zero
  have hμ0 : (μ : F) ≠ 0 := μ.ne_zero
  have hcc : (c : F) * σ (c : F) = 1 := by
    have e1 : (c : F) • (a * m b * m a) = (μ : F) • b := by
      rw [← Matrix.smul_mul, hE2, Matrix.mul_assoc, hE1, Matrix.mul_smul, Matrix.mul_one]
    have e2 : a * m b * m a = (σ (c : F) * μ) • b := by
      rw [Matrix.mul_assoc, ← hE3, Matrix.mul_smul, ← Matrix.mul_assoc, hE1, Matrix.smul_mul,
        Matrix.one_mul, smul_smul]
    rw [e2, smul_smul] at e1
    have := smul_left_cancel_of_det hdetb e1
    have h' : ((c : F) * σ (c : F) - 1) * μ = 0 := by linear_combination this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hμ0)
  have hdet : (c : F) ^ 2 * σ b.det = b.det := by
    have := congrArg Matrix.det hE2
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Fintype.card_fin] at this
    have hm : (m b).det = σ b.det := (RingHom.map_det σ.toRingHom b).symm
    rw [hm] at this
    have h' : ((c : F) ^ 2 * σ b.det - b.det) * a.det = 0 := by linear_combination this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hdeta)
  set s := t ^ u with hs
  have hσc : σ (c : F) = (c : F) ^ s := hσx _
  have hσd : σ b.det = b.det ^ s := hσx _
  rw [hσc] at hcc
  rw [hσd] at hdet
  have hs1 : 1 ≤ s := Nat.one_le_pow _ _ ht.pos
  obtain ⟨k, hk⟩ : ∃ k, s + 1 = 2 * k := by
    obtain ⟨j, hj⟩ := (ht.pow : Odd (t ^ u))
    exact ⟨j + 1, by rw [hs, hj]; ring⟩
  have hδ : b.det ^ ((s - 1) * ((s + 1) / 2)) = 1 := by
    have e1 : (c : F) ^ 2 * b.det ^ (s - 1) = 1 := by
      have : b.det ^ s = b.det ^ (s - 1) * b.det := by
        rw [← pow_succ, Nat.sub_add_cancel hs1]
      rw [this, ← mul_assoc] at hdet
      have h' : ((c : F) ^ 2 * b.det ^ (s - 1) - 1) * b.det = 0 := by linear_combination hdet
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hdetb)
    have e2 : (c : F) ^ (2 * k) = 1 := by
      rw [← hk, pow_succ, mul_comm]
      exact hcc
    rw [show (s + 1) / 2 = k by omega]
    have := congrArg (· ^ k) e1
    simp only [mul_pow, one_pow, ← pow_mul] at this
    rw [e2, one_mul] at this
    exact this
  have hsq := isSquare_of_pow_eq_one ht hu hcard hdetb hδ
  have hmem : Matrix.ProjGenLinGroup.mk B ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    (pgl2_mk_mem_psl2_range_iff_det_isSquare B).mpr hsq
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, by rw [MonoidHom.comp_apply, hy]⟩

end CFSG.ComponentClassification.AutL2Facts
