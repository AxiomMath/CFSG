module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.InvolutionMatrices
public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacyExhaustive

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Conjugation

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem conj_specialInclusion {k : CentralExtension F b m hm heven} {Q : GL (Fin 2) F}
    (hk : projectiveMap F b m hm heven k = ProjGenLinGroup.mk Q)
    {Y Z : SpecialLinearGroup (Fin 2) F}
    (hZ : SpecialLinearGroup.toGL Z = Q * SpecialLinearGroup.toGL Y * Q⁻¹) :
    k * specialInclusion F b m hm heven Y * k⁻¹ = specialInclusion F b m hm heven Z := by
  obtain ⟨Y', j, rfl⟩ := quotientClass_surjective F b m hm heven k
  rw [projectiveMap_quotientClass] at hk
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hk
  have hconj : quotientClass F b m hm heven Y' j * specialInclusion F b m hm heven Y *
      (quotientClass F b m hm heven Y' j)⁻¹ =
        specialInclusion F b m hm heven (Y' * (beta F b ^ j.val) Y * Y'⁻¹) := by
    rw [mul_inv_eq_iff_eq_mul, specialInclusion_mul_quotientClass, specialInclusion_apply,
      quotientClass_mul, add_zero, inv_mul_cancel_right]
  rw [hconj]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  have hs : ∀ M : GL (Fin 2) F,
      GeneralLinearGroup.scalar (Fin 2) c * M = M * GeneralLinearGroup.scalar (Fin 2) c := by
    intro M
    have hmem : GeneralLinearGroup.scalar (Fin 2) c ∈ Subgroup.center (GL (Fin 2) F) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨c, rfl⟩
    exact (Subgroup.mem_center_iff.mp hmem M).symm
  have h1 : GeneralLinearGroup.scalar (Fin 2) c * SpecialLinearGroup.toGL Y *
      (GeneralLinearGroup.scalar (Fin 2) c)⁻¹ = SpecialLinearGroup.toGL Y := by
    rw [hs, mul_inv_cancel_right]
  rw [hZ, ← hc, map_mul, map_mul, map_inv, toGL_beta_pow]
  calc SpecialLinearGroup.toGL Y' * (nonsquareMatrix F b ^ j.val * SpecialLinearGroup.toGL Y *
        (nonsquareMatrix F b ^ j.val)⁻¹) * (SpecialLinearGroup.toGL Y')⁻¹
      = SpecialLinearGroup.toGL Y' * nonsquareMatrix F b ^ j.val *
          (GeneralLinearGroup.scalar (Fin 2) c * SpecialLinearGroup.toGL Y *
            (GeneralLinearGroup.scalar (Fin 2) c)⁻¹) *
          (SpecialLinearGroup.toGL Y' * nonsquareMatrix F b ^ j.val)⁻¹ := by
        rw [h1]
        group
    _ = _ := by group

end Conjugation

@[expose] noncomputable def involutionY (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (heven : Even m) : CentralExtension F b m hm heven :=
  (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) * specialInclusion F b m hm heven (weyl F)

section Involutions

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

omit [Fintype F] in
theorem baseResidue_cyclicGenerator_pow (k : ℕ) :
    baseResidue F b m hm heven (cyclicGenerator F b m hm heven ^ k) =
      Multiplicative.ofAdd (k : ZMod m) := by
  rw [map_pow, cyclicGenerator, baseResidue_quotientClass, map_one, ← ofAdd_nsmul, nsmul_one]

omit [Fintype F] in
theorem cyclicGenerator_pow_half (h4 : 4 ∣ m) :
    cyclicGenerator F b m hm heven ^ (m / 2) = (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) := by
  rw [← pow_mul]
  congr 1
  omega

omit [Fintype F] in
theorem cyclicGenerator_pow_half_comm (h4 : 4 ∣ m) (g : CentralExtension F b m hm heven) :
    cyclicGenerator F b m hm heven ^ (m / 2) * g =
      g * cyclicGenerator F b m hm heven ^ (m / 2) := by
  rw [cyclicGenerator_pow_half h4]
  exact (Commute.pow_left (cyclicGenerator_sq_comm F b m hm heven g) (m / 4)).eq

omit [Fintype F] in
theorem involutionY_eq (h4 : 4 ∣ m) :
    involutionY F b m hm heven =
      specialInclusion F b m hm heven (weyl F) * cyclicGenerator F b m hm heven ^ (m / 2) := by
  rw [involutionY, ← cyclicGenerator_pow_half h4, cyclicGenerator_pow_half_comm h4]

omit [Fintype F] in
theorem cyclicGenerator_pow_m_mul_self :
    cyclicGenerator F b m hm heven ^ m * cyclicGenerator F b m hm heven ^ m = 1 := by
  rw [cyclicGenerator_pow_m, ← map_mul, ← pow_two,
    CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_square, map_one]

omit [Fintype F] in
theorem involutionY_mul_self (h4 : 4 ∣ m) :
    involutionY F b m hm heven * involutionY F b m hm heven = 1 := by
  rw [involutionY_eq h4]
  have hc := cyclicGenerator_pow_half_comm (b := b) (hm := hm) (heven := heven) h4
    (specialInclusion F b m hm heven (weyl F))
  calc specialInclusion F b m hm heven (weyl F) * cyclicGenerator F b m hm heven ^ (m / 2) *
        (specialInclusion F b m hm heven (weyl F) * cyclicGenerator F b m hm heven ^ (m / 2))
      = specialInclusion F b m hm heven (weyl F) *
          (cyclicGenerator F b m hm heven ^ (m / 2) * specialInclusion F b m hm heven (weyl F)) *
          cyclicGenerator F b m hm heven ^ (m / 2) := by group
    _ = specialInclusion F b m hm heven (weyl F * weyl F) *
          (cyclicGenerator F b m hm heven ^ (m / 2) *
            cyclicGenerator F b m hm heven ^ (m / 2)) := by
        rw [hc, map_mul]
        group
    _ = 1 := by
        rw [weyl_sq, ← pow_add, show m / 2 + m / 2 = m by omega, ← cyclicGenerator_pow_m,
          cyclicGenerator_pow_m_mul_self]

omit [Fintype F] in
theorem projectiveMap_involutionY (hb : ¬ IsSquare b) :
    projectiveMap F b m hm heven (involutionY F b m hm heven) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL (weyl F)) := by
  have ha : projectiveMap F b m hm heven (cyclicGenerator F b m hm heven ^ 2) = 1 :=
    (projectiveMap_eq_one_iff hb _).mpr (Subgroup.mem_zpowers _)
  rw [involutionY, map_mul, map_pow, ha, one_pow, one_mul, projectiveMap_specialInclusion]

omit [Fintype F] in
theorem weyl_not_scalar :
    ¬ ∃ c : Fˣ, SpecialLinearGroup.toGL (weyl F) = GeneralLinearGroup.scalar (Fin 2) c := by
  rintro ⟨c, hc⟩
  have h : ((SpecialLinearGroup.toGL (weyl F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      ((GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    rw [hc]
  change ((weyl F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = _ at h
  rw [weyl_val] at h
  simp at h

omit [Fintype F] in
theorem involutionY_not_mem (hb : ¬ IsSquare b) :
    involutionY F b m hm heven ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  rw [← projectiveMap_eq_one_iff hb, projectiveMap_involutionY hb, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar]
  rintro ⟨c, hc⟩
  exact weyl_not_scalar ⟨c, hc.symm⟩

omit [Fintype F] in
theorem isSquare_neg_four_iff (h2 : (2 : F) ≠ 0) : IsSquare (-4 : F) ↔ IsSquare (-1 : F) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s / 2, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero h2 h2)]
    linear_combination hs
  · rintro ⟨s, hs⟩
    exact ⟨2 * s, by linear_combination 4 * hs⟩

theorem card_fixed_involutionY (hb : ¬ IsSquare b) :
    Nat.card {p : Omega F // involutionY F b m hm heven • p = p} =
      if IsSquare (-1 : F) then 2 else 0 := by
  have h2 := two_ne_zero_of_not_isSquare hb
  have hfix : Nat.card {p : Omega F // involutionY F b m hm heven • p = p} =
      Nat.card {p : Omega F //
        coordinateGLAction F (SpecialLinearGroup.toGL (weyl F)) p = p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun p => by
      rw [smul_eq_coordinateGLAction (projectiveMap_involutionY hb)])
  rw [hfix, card_fixed_coordinateGLAction h2 _ weyl_not_scalar, sqrtCount_eq h2]
  have htr : Matrix.trace (SpecialLinearGroup.toGL (weyl F) : GL (Fin 2) F).val = 0 := by
    change Matrix.trace ((weyl F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 0
    rw [weyl_val, Matrix.trace_fin_two]
    simp
  have hdet : Matrix.det (SpecialLinearGroup.toGL (weyl F) : GL (Fin 2) F).val = 1 := by
    change Matrix.det ((weyl F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [weyl_val, Matrix.det_fin_two]
    simp
  rw [htr, hdet]
  have h4 : (0 : F) ^ 2 - 4 * 1 = -4 := by ring
  have h40 : (-4 : F) ≠ 0 := by
    intro h
    apply h2
    have h22 : (2 : F) * 2 = 0 := by linear_combination -h
    exact mul_self_eq_zero.mp h22
  rw [h4, ite_eq_right h40]
  by_cases hs : IsSquare (-1 : F)
  · rw [ite_eq_left ((isSquare_neg_four_iff h2).mpr hs), ite_eq_left hs]
  · rw [ite_eq_right (mt (isSquare_neg_four_iff h2).mp hs), ite_eq_right hs]

theorem involution_cases (hb : ¬ IsSquare b) (h4 : 4 ∣ m) {w : CentralExtension F b m hm heven}
    (hw : w * w = 1) :
    w = 1 ∨ w = cyclicGenerator F b m hm heven ^ m ∨ IsConj (involutionY F b m hm heven) w := by
  have h2 := two_ne_zero_of_not_isSquare hb
  set ρ := baseResidue F b m hm heven with hρ
  have htt : Multiplicative.toAdd (ρ w) + Multiplicative.toAdd (ρ w) = 0 := by
    rw [← toAdd_mul, ← map_mul, hw, map_one, toAdd_one]
  rcases zmod_eq_zero_or_half hm heven htt with h0 | hhalf
  · have hker : w ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective h0
    rw [hρ, baseResidue_ker] at hker
    obtain ⟨X, rfl⟩ := hker
    have hXX : X * X = 1 :=
      specialInclusion_injective F b m hm heven (by rw [map_mul, hw, map_one])
    rcases SL2_eq_one_or_neg_of_mul_self h2 hXX with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl (cyclicGenerator_pow_m F b m hm heven).symm)
  · right
    right
    have hker : w * (cyclicGenerator F b m hm heven ^ (m / 2))⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, baseResidue_cyclicGenerator_pow,
        mul_inv_eq_one]
      exact Multiplicative.toAdd.injective hhalf
    rw [hρ, baseResidue_ker] at hker
    obtain ⟨X, hX⟩ := hker
    have hw' :
        w = specialInclusion F b m hm heven X * cyclicGenerator F b m hm heven ^ (m / 2) := by
      rw [hX, inv_mul_cancel_right]
    have hc := cyclicGenerator_pow_half_comm (b := b) (hm := hm) (heven := heven) h4
      (specialInclusion F b m hm heven X)
    have hXX : X * X = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
      apply specialInclusion_injective F b m hm heven
      have hww : specialInclusion F b m hm heven (X * X) * cyclicGenerator F b m hm heven ^ m =
          1 := by
        rw [← hw, hw', map_mul]
        calc specialInclusion F b m hm heven X * specialInclusion F b m hm heven X *
              cyclicGenerator F b m hm heven ^ m
            = specialInclusion F b m hm heven X * specialInclusion F b m hm heven X *
                (cyclicGenerator F b m hm heven ^ (m / 2) *
                  cyclicGenerator F b m hm heven ^ (m / 2)) := by
              rw [← pow_add, show m / 2 + m / 2 = m by omega]
          _ = specialInclusion F b m hm heven X *
                (cyclicGenerator F b m hm heven ^ (m / 2) * specialInclusion F b m hm heven X) *
                cyclicGenerator F b m hm heven ^ (m / 2) := by
              rw [hc]
              group
          _ = _ := by group
      rw [← cyclicGenerator_pow_m]
      calc specialInclusion F b m hm heven (X * X)
          = specialInclusion F b m hm heven (X * X) * cyclicGenerator F b m hm heven ^ m *
              cyclicGenerator F b m hm heven ^ m := by
            rw [mul_assoc, cyclicGenerator_pow_m_mul_self, mul_one]
        _ = cyclicGenerator F b m hm heven ^ m := by rw [hww, one_mul]
    obtain ⟨Q, hQ⟩ := exists_conj_weyl h2 hXX
    obtain ⟨k, hk⟩ := projectiveMap_surjective F b m hm heven hb (ProjGenLinGroup.mk Q)
    have hconj := conj_specialInclusion hk (Y := X) (Z := weyl F) hQ.symm
    refine isConj_iff.mpr ⟨k⁻¹, ?_⟩
    rw [inv_inv, involutionY_eq h4, hw']
    have hk' : specialInclusion F b m hm heven (weyl F) =
        k * specialInclusion F b m hm heven X * k⁻¹ := hconj.symm
    rw [hk']
    have hck := cyclicGenerator_pow_half_comm (b := b) (hm := hm) (heven := heven) h4 k
    calc k⁻¹ * (k * specialInclusion F b m hm heven X * k⁻¹ *
          cyclicGenerator F b m hm heven ^ (m / 2)) * k
        = specialInclusion F b m hm heven X * (k⁻¹ * cyclicGenerator F b m hm heven ^ (m / 2) *
            k) := by group
      _ = _ := by
        rw [mul_assoc k⁻¹, hck, inv_mul_cancel_left]

end Involutions

section Centralizer

variable {K : Type} [Group K] [Finite K]

theorem card_centralizer_of_isConj {g h : K} (hgh : IsConj g h) :
    Nat.card (Subgroup.centralizer {g} : Subgroup K) =
      Nat.card (Subgroup.centralizer {h} : Subgroup K) := by
  have hg := card_isConj_mul_card_centralizer g
  have hh := card_isConj_mul_card_centralizer h
  have hcl : Nat.card {x : K // IsConj g x} = Nat.card {x : K // IsConj h x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun hx => hgh.symm.trans hx, fun hx => hgh.trans hx⟩)
  have hpos : 0 < Nat.card {x : K // IsConj h x} := by
    have : Nonempty {x : K // IsConj h x} := ⟨⟨h, IsConj.refl h⟩⟩
    exact Nat.card_pos
  rw [hcl] at hg
  exact Nat.eq_of_mul_eq_mul_left hpos (hg.trans hh.symm)

end Centralizer

section CentralizerY

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem card_centralizer_involutionY (hb : ¬ IsSquare b) :
    Nat.card (Subgroup.centralizer {involutionY F b m hm heven}) =
      if IsSquare (-1 : F) then m * (Nat.card F - 1) else m * (Nat.card F + 1) := by
  obtain ⟨E, _, _, ⟨basis⟩⟩ := exists_quadratic_extension F b hb
  have h2 := two_ne_zero_of_not_isSquare hb
  have hfix := card_fixed_involutionY (hm := hm) (heven := heven) hb
  rcases conjugacy_type_exists basis hb (involutionY F b m hm heven) with hA |
      ⟨α, hα, hc⟩ | ⟨t, ht, htA, hc⟩ | ⟨t, ht, htA, hc⟩
  · exact absurd hA (involutionY_not_mem hb)
  · exfalso
    have h1 := card_fixed_of_isConj (Ω := Omega F) hc
    rw [card_fixed_unipotent hα one_ne_zero, hfix] at h1
    by_cases hs : IsSquare (-1 : F)
    · rw [ite_eq_left hs] at h1
      omega
    · rw [ite_eq_right hs] at h1
      omega
  · have h1 := card_fixed_of_isConj (Ω := Omega F) hc
    rw [card_fixed_splitTorus hb ht htA, hfix] at h1
    have hsq : IsSquare (-1 : F) := by
      by_contra hsq
      rw [ite_eq_right hsq] at h1
      omega
    rw [ite_eq_left hsq, card_centralizer_of_isConj hc, centralizer_splitTorus hb ht htA,
      card_splitTorus]
  · have h1 := card_fixed_of_isConj (Ω := Omega F) hc
    rw [card_fixed_nonsplitTorus hb ht htA, hfix] at h1
    have hsq : ¬ IsSquare (-1 : F) := by
      intro hsq
      rw [ite_eq_left hsq] at h1
      omega
    obtain ⟨y, hy⟩ : ∃ y : Eˣ, (y : E) * (y : E) ^ Nat.card F = -1 :=
      exists_norm_eq F E basis (-1) |>.imp fun y' hy' => by rw [hy']; simp
    obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
    rw [ite_eq_right hsq, card_centralizer_of_isConj hc,
      centralizer_nonsplitTorus y hy h2 hb ht htA,
      card_nonsplitTorus z hz]

end CentralizerY

end CFSG.Wreathed.CentralSL2
