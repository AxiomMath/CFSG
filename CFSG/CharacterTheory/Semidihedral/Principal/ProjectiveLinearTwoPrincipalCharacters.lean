module

public import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.CharacterTheory.Semidihedral.Principal.DoublyTransitiveAugmentation
public import CFSG.CharacterTheory.Semidihedral.Principal.LinearTwistBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionPrincipalTransport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.GorensteinWalter

universe u v

section Coordinates

variable {F : Type u} [Field F]

omit [Field F] in
theorem card_omega [Fintype F] : Nat.card (Omega F) = Nat.card F + 1 := by
  simp [Omega, Nat.card_eq_fintype_card, Fintype.card_option]

theorem coordinateG_two_transitive [Finite F] (x₁ x₂ y₁ y₂ : Omega F) (hx : x₁ ≠ x₂)
    (hy : y₁ ≠ y₂) :
    ∃ g ∈ coordinateG F, g x₁ = y₁ ∧ g x₂ = y₂ := by
  set e := coordinateEquiv F
  let emb₁ : Fin 2 ↪ PSL2ProjectiveLine F :=
    ⟨![e x₁, e x₂], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [e.injective.eq_iff, eq_comm]⟩
  let emb₂ : Fin 2 ↪ PSL2ProjectiveLine F :=
    ⟨![e y₁, e y₂], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [e.injective.eq_iff, eq_comm]⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) F) emb₁ emb₂
  have hpt : ∀ x : Omega F, e (coordinatePSLAction F (psl2QuotientMap F g) x) = g • e x := by
    intro x
    rw [coordinatePSLAction_point]
    rfl
  refine ⟨coordinatePSLAction F (psl2QuotientMap F g), ?_, ?_, ?_⟩
  · rw [← coordinatePSLAction_range_eq_G]
    exact ⟨_, rfl⟩
  · apply e.injective
    rw [hpt]
    exact congrArg (fun f : Fin 2 ↪ PSL2ProjectiveLine F => f 0) hg
  · apply e.injective
    rw [hpt]
    exact congrArg (fun f : Fin 2 ↪ PSL2ProjectiveLine F => f 1) hg

theorem card_sqrts_eq [Fintype F] (hF : ringChar F ≠ 2) {s : F} (hs : s ≠ 0) :
    Nat.card {y : F // y ^ 2 = s} = if IsSquare s then 2 else 0 := by
  have h := quadraticChar_card_sqrts hF s
  have hcard : Nat.card {y : F // y ^ 2 = s} = ({x : F | x ^ 2 = s}.toFinset).card := by
    rw [Nat.card_eq_fintype_card, Set.toFinset_card]
    rfl
  rw [hcard]
  split_ifs with hsq
  · rw [(quadraticChar_one_iff_isSquare hs).mpr hsq] at h
    exact_mod_cast h
  · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hsq, neg_add_cancel] at h
    exact_mod_cast h

@[expose] noncomputable def jMatrix (a : F) (ha : a ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -a; 1, 0] (by simp [Matrix.det_fin_two, ha])

theorem jMatrix_det (a : F) (ha : a ≠ 0) : ((jMatrix a ha).det : F) = a := by
  simp [jMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]

omit [Field F] in
theorem card_subtype_eq_of_param {P : Omega F → Prop} {Q : F → Prop} (g : F → F)
    (hg : Function.Injective g) (h : ∀ x, P x ↔ ∃ y, x = some (g y) ∧ Q y) :
    Nat.card {x // P x} = Nat.card {y // Q y} := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun y => ⟨some (g y.1), (h _).mpr ⟨y.1, rfl, y.2⟩⟩) ⟨?_, ?_⟩
  · intro y y' hyy
    exact Subtype.ext (hg (Option.some.inj (congrArg Subtype.val hyy)))
  · intro x
    obtain ⟨y, hy, hQ⟩ := (h x.1).mp x.2
    exact ⟨⟨y, hQ⟩, Subtype.ext hy.symm⟩

theorem card_fixed_jMatrix [Fintype F] (hF : ringChar F ≠ 2) (a : F) (ha : a ≠ 0) :
    Nat.card {x : Omega F // coordinateGLAction F (jMatrix a ha) x = x} =
      if IsSquare (-a) then 2 else 0 := by
  have hval : ∀ i j, (jMatrix a ha).val i j = !![0, -a; 1, 0] i j := fun i j => rfl
  rw [← card_sqrts_eq hF (neg_ne_zero.mpr ha)]
  apply card_subtype_eq_of_param id Function.injective_id
  intro x
  cases x with
  | none =>
    rw [coordinateGLAction_infinity F _ (by rw [hval]; simp)]
    simp
  | some y =>
    by_cases hy : y = 0
    · subst hy
      rw [coordinateGLAction_finite_denominator_zero F _ 0 (by simp [hval])]
      simp [ha]
    · rw [coordinateGLAction_finite F _ y (by simp [hval, hy])]
      simp only [hval, Option.some.injEq, id, exists_eq_left']
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, zero_add, one_mul, add_zero]
      constructor
      · intro h
        field_simp at h
        linear_combination -h
      · intro h
        field_simp
        linear_combination -h

theorem sl_sq_neg_one_trace (hF : ringChar F ≠ 2) (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (hX : (X : Matrix (Fin 2) (Fin 2) F) * X = -1) :
    (X : Matrix (Fin 2) (Fin 2) F) 1 1 = -(X : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  have hdet : (X : Matrix (Fin 2) (Fin 2) F).det = 1 := X.2
  rw [Matrix.det_fin_two] at hdet
  have h00 := congrFun (congrFun hX 0) 0
  have h01 := congrFun (congrFun hX 0) 1
  have h10 := congrFun (congrFun hX 1) 0
  have h11 := congrFun (congrFun hX 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), neg_zero] at h00 h01 h10 h11
  set a := (X : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (X : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (X : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (X : Matrix (Fin 2) (Fin 2) F) 1 1
  by_contra hne
  have hs : a + d ≠ 0 := fun h => hne (by linear_combination h)
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_right hs
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination h10
    exact (mul_eq_zero.mp this).resolve_right hs
  have had : a = d := by
    have : (a - d) * (a + d) = 0 := by
      rw [hb, hc] at h00 h11
      linear_combination h00 - h11
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hs)
  rw [hb, hc, ← had] at hdet
  rw [hb, hc] at h00
  exact Ring.neg_one_ne_one_of_char_ne_two hF (by linear_combination -h00 + hdet)

theorem card_fixed_sl_sq_neg_one [Fintype F] (hF : ringChar F ≠ 2)
    (X : Matrix.SpecialLinearGroup (Fin 2) F) (hX : (X : Matrix (Fin 2) (Fin 2) F) * X = -1) :
    Nat.card {x : Omega F //
        coordinateGLAction F (Matrix.SpecialLinearGroup.toGL X) x = x} =
      if IsSquare (-1 : F) then 2 else 0 := by
  have htrace := sl_sq_neg_one_trace hF X hX
  have h00 := congrFun (congrFun hX 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq] at h00
  have hval : ∀ i j, (Matrix.SpecialLinearGroup.toGL X).val i j =
      (X : Matrix (Fin 2) (Fin 2) F) i j := fun i j => rfl
  set a := (X : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (X : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (X : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (X : Matrix (Fin 2) (Fin 2) F) 1 1
  have hneg : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  by_cases hc : c = 0
  ·
    have ha2 : a * a = -1 := by rw [hc] at h00; linear_combination h00
    have ha : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_mul] at ha2
      exact hneg ha2.symm
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    have hsq : IsSquare (-1 : F) := ⟨a, ha2.symm⟩
    simp only [hsq, ↓reduceIte]
    have hfix : ∀ x : Omega F, coordinateGLAction F (Matrix.SpecialLinearGroup.toGL X) x = x ↔
        x ∈ ({none, some (-b / (2 * a))} : Finset (Omega F)) := by
      intro x
      cases x with
      | none =>
        rw [coordinateGLAction_infinity_lower_left_zero F _ (by rw [hval]; exact hc)]
        simp
      | some y =>
        have hden : (Matrix.SpecialLinearGroup.toGL X).val 1 0 * y +
            (Matrix.SpecialLinearGroup.toGL X).val 1 1 ≠ 0 := by
          rw [hval, hval]
          change c * y + d ≠ 0
          rw [hc, htrace, zero_mul, zero_add]
          exact neg_ne_zero.mpr ha
        rw [coordinateGLAction_finite F _ y hden]
        simp only [hval, Option.some.injEq, Finset.mem_insert, Finset.mem_singleton,
          reduceCtorEq, false_or]
        change (a * y + b) / (c * y + d) = y ↔ y = -b / (2 * a)
        rw [hc, htrace, zero_mul, zero_add]
        have hna : -a ≠ 0 := neg_ne_zero.mpr ha
        rw [div_eq_iff hna, eq_div_iff (mul_ne_zero h2 ha)]
        constructor
        · intro h
          linear_combination h
        · intro h
          linear_combination h
    rw [Nat.card_congr (Equiv.subtypeEquivRight hfix), Nat.card_eq_fintype_card,
      Fintype.card_coe, Finset.card_pair (by simp)]
  ·
    rw [← card_sqrts_eq hF hneg]
    have hg : Function.Injective fun y : F => (y + a) / c := by
      intro y y' h
      have := (div_left_inj' hc).mp h
      linear_combination this
    apply card_subtype_eq_of_param (fun y => (y + a) / c) hg
    intro x
    cases x with
    | none =>
      rw [coordinateGLAction_infinity F _ (by rw [hval]; exact hc)]
      simp
    | some y =>
      simp only [Option.some.injEq]
      have hiff : (∃ z : F, y = (z + a) / c ∧ z ^ 2 = -1) ↔ (c * y - a) ^ 2 = -1 := by
        constructor
        · rintro ⟨z, rfl, hz⟩
          field_simp
          linear_combination hz
        · intro h
          refine ⟨c * y - a, ?_, h⟩
          field_simp
          ring
      rw [hiff]
      by_cases hden : (Matrix.SpecialLinearGroup.toGL X).val 1 0 * y +
          (Matrix.SpecialLinearGroup.toGL X).val 1 1 = 0
      · rw [coordinateGLAction_finite_denominator_zero F _ y hden]
        rw [hval, hval] at hden
        change c * y + d = 0 at hden
        rw [htrace] at hden
        have hzero : c * y - a = 0 := by linear_combination hden
        rw [hzero]
        simp only [reduceCtorEq, false_iff]
        intro h
        exact hneg (by rw [← h]; ring)
      · rw [coordinateGLAction_finite F _ y hden]
        rw [hval, hval] at hden
        change c * y + d ≠ 0 at hden
        simp only [hval, Option.some.injEq]
        change (a * y + b) / (c * y + d) = y ↔ _
        rw [div_eq_iff hden]
        constructor
        · intro h
          linear_combination h00 - c * h - c * y * htrace
        · intro h
          have hmul : c * (a * y + b - y * (c * y + d)) = 0 := by
            linear_combination -h + h00 - c * y * htrace
          have := (mul_eq_zero.mp hmul).resolve_left hc
          linear_combination this

theorem isSquare_neg_iff_of_not_isSquare [Fintype F] {a : F} (ha : a ≠ 0)
    (hns : ¬ IsSquare a) : IsSquare (-a) ↔ ¬ IsSquare (-1 : F) := by
  have hχa : quadraticChar F a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hns
  have hmul : quadraticChar F (-a) = quadraticChar F (-1) * quadraticChar F a := by
    rw [← map_mul, neg_one_mul]
  rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr ha),
    ← quadraticChar_neg_one_iff_not_isSquare, hmul, hχa]
  constructor <;> intro h <;> linarith

omit [Field F] in
theorem forall_of_card_subtype_eq [Fintype F] (P : Omega F → Prop)
    (h : Nat.card {x // P x} = Nat.card (Omega F)) : ∀ x, P x := by
  intro x
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact Finset.filter_card_eq h x (Finset.mem_univ x)

theorem two_transitive_of_coordinateG_le [Finite F] {H : Type v} [Group H]
    [MulAction H (Omega F)] (ψ : H →* Equiv.Perm (Omega F)) (hψ : ∀ h x, h • x = ψ h x)
    (hG : coordinateG F ≤ ψ.range) : MulAction.IsMultiplyPretransitive H (Omega F) 2 := by
  rw [MulAction.isMultiplyPretransitive_iff]
  intro x y
  have hx : x 0 ≠ x 1 := fun h => by simpa using x.injective h
  have hy : y 0 ≠ y 1 := fun h => by simpa using y.injective h
  obtain ⟨g, hg, h0, h1⟩ := coordinateG_two_transitive (x 0) (x 1) (y 0) (y 1) hx hy
  obtain ⟨c, hc⟩ := hG hg
  refine ⟨c, ?_⟩
  apply Function.Embedding.ext
  intro i
  fin_cases i
  · change c • x 0 = y 0
    rw [hψ, hc, h0]
  · change c • x 1 = y 1
    rw [hψ, hc, h1]

end Coordinates

section Sign

@[expose] noncomputable def cardTwoSign (Q : Type u) [Group Q] (hQ : Nat.card Q = 2) :
    Q →* ℂˣ where
  toFun s := if s = 1 then 1 else -1
  map_one' := by simp
  map_mul' s t := by
    by_cases hs : s = 1
    · simp [hs]
    by_cases ht : t = 1
    · simp [ht]
    have hst : s * t = 1 := by
      have hts : t = s := eq_of_nonone_of_card_two hQ ht hs
      have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
      have hdvd : orderOf s ∣ 2 := hQ ▸ orderOf_dvd_natCard s
      rw [hts, ← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    simp [hs, ht, hst]

theorem cardTwoSign_apply (Q : Type u) [Group Q] (hQ : Nat.card Q = 2) (s : Q) :
    ((cardTwoSign Q hQ s : ℂˣ) : ℂ) = if s = 1 then 1 else -1 := by
  change ((if s = 1 then 1 else -1 : ℂˣ) : ℂ) = _
  split_ifs <;> simp

end Sign

section NormalForm

variable (F : Type u) [Field F] [Finite F]

theorem normalForm_square_iff_theta (hK : IsOddPrimePower (Nat.card F)) (e : coordinateE F) :
    (∃ (d : coordinateD F) (σ : F ≃+* F) (a : Matrix.GeneralLinearGroup (Fin 2) F),
      (e : Equiv.Perm (Omega F)) = d * fieldExtension F σ ∧
        coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d ∧ IsSquare (a.det : F)) ↔
      (theta F hK e).1 = 1 := by
  constructor
  · rintro ⟨d, σ, a, he, ha, hsq⟩
    rw [theta_presentation F hK e d σ he a ha]
    exact (squareClassMap_eq_one F _).mpr ((isSquare_unit_iff _).mpr hsq)
  · intro h1
    obtain ⟨⟨d, σ⟩, he, -⟩ := coordinate_normal_form F e
    have hd : (d : Equiv.Perm (Omega F)) ∈ (coordinatePGLAction F).range := by
      rw [coordinatePGLAction_range_eq_D]
      exact d.2
    obtain ⟨g, hg⟩ := hd
    obtain ⟨a, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    refine ⟨d, σ, a, he, hg, ?_⟩
    rw [theta_presentation F hK e d σ he a hg] at h1
    exact (isSquare_unit_iff _).mp ((squareClassMap_eq_one F _).mp h1)

theorem normalForm_square_iff_det (hK : IsOddPrimePower (Nat.card F)) (e : coordinateE F)
    (d : coordinateD F) (σ : F ≃+* F) (he : (e : Equiv.Perm (Omega F)) = d * fieldExtension F σ)
    (a : Matrix.GeneralLinearGroup (Fin 2) F)
    (ha : coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d) :
    (∃ (d : coordinateD F) (σ : F ≃+* F) (a : Matrix.GeneralLinearGroup (Fin 2) F),
      (e : Equiv.Perm (Omega F)) = d * fieldExtension F σ ∧
        coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d ∧ IsSquare (a.det : F)) ↔
      IsSquare (a.det : F) := by
  rw [normalForm_square_iff_theta F hK e, theta_presentation F hK e d σ he a ha]
  exact (squareClassMap_eq_one F _).trans (isSquare_unit_iff _)

omit [Finite F] in
theorem coordinateGLAction_normalForm (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∃ d : coordinateD F, coordinateGLAction F A = d * fieldExtension F (RingEquiv.refl F) ∧
      coordinatePGLAction F (Matrix.ProjGenLinGroup.mk A) = d := by
  have hmem : coordinateGLAction F A ∈ coordinateD F := by
    rw [← coordinatePGLAction_range_eq_D]
    exact ⟨_, rfl⟩
  refine ⟨⟨coordinateGLAction F A, hmem⟩, ?_, rfl⟩
  have h1 : fieldExtension F (RingEquiv.refl F) = 1 := by
    ext x
    cases x <;> rfl
  rw [h1, mul_one]

end NormalForm

theorem projective_linear_two_four_principal_odd_degree_characters {p f : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hf : 1 ≤ f) (F : Type u) [Field F] [Fintype F] (hcard : Nat.card F = p ^ f)
    (Γ : Subgroup (Equiv.Perm (Omega F))) (hDΓ : coordinateD F ≤ Γ) (hΓE : Γ ≤ coordinateE F)
    {C : Type v} [Group C] [Fintype C] (ρ : C →* Γ) (hρ : Function.Surjective ρ)
    (basis : FiniteIrreducibleCharacterBasis C) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    let φ : C → ℂ := fun c =>
      (Nat.card {x : Omega F // (ρ c : Equiv.Perm (Omega F)) x = x} : ℂ) - 1
    let δ : C → ℂ := fun c =>
      if ∃ (d : coordinateD F) (σ : F ≃+* F) (a : Matrix.GeneralLinearGroup (Fin 2) F),
          (ρ c : Equiv.Perm (Omega F)) = d * fieldExtension F σ ∧
            coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d ∧ IsSquare (a.det : F)
      then 1 else -1
    let ε : ℂ := if Nat.card F % 4 = 1 then 1 else -1
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let L : Subgroup C := (coordinateG F).comap (Γ.subtype.comp ρ)
    (∀ (c : C) (d : coordinateD F) (σ : F ≃+* F) (a : Matrix.GeneralLinearGroup (Fin 2) F),
      (ρ c : Equiv.Perm (Omega F)) = d * fieldExtension F σ →
      coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d →
      (δ c = 1 ↔ IsSquare (a.det : F))) ∧
    (∃ lam : C →* ℂˣ, ∀ c, (lam c : ℂ) = δ c) ∧ (∃ c, δ c ≠ 1) ∧ (∀ c, δ c * δ c = 1) ∧
    (∃ lδ lφ lδφ : basis.index,
      (∀ c, (basis.representation lδ).character c = δ c) ∧
      (∀ c, (basis.representation lφ).character c = φ c) ∧
      (∀ c, (basis.representation lδφ).character c = δ c * φ c) ∧
      [principal, lδ, lφ, lδφ].Nodup ∧
      (∀ l ∈ [principal, lδ, lφ, lδφ], (basis.representation l).IsIrreducible ∧ l ∈ B ∧
        ∀ c, ∃ z : ℤ, (basis.representation l).character c = z) ∧
      Module.finrank ℂ (basis.representation principal).vector = 1 ∧
      Module.finrank ℂ (basis.representation lδ).vector = 1 ∧
      Module.finrank ℂ (basis.representation lφ).vector = Nat.card F ∧
      Module.finrank ℂ (basis.representation lδφ).vector = Nat.card F ∧
      MonoidHom.ker (basis.representation lφ).representation = ρ.ker ∧
      MonoidHom.ker (basis.representation lδφ).representation = ρ.ker) ∧
    ((fun _ => (1 : ℂ)) ≠ δ ∧ (fun _ => (1 : ℂ)) ≠ φ ∧
      (fun _ => (1 : ℂ)) ≠ (fun c => δ c * φ c) ∧ δ ≠ φ ∧ δ ≠ (fun c => δ c * φ c) ∧
      φ ≠ (fun c => δ c * φ c)) ∧
    (∀ basisL : FiniteIrreducibleCharacterBasis L, ∃ l : basisL.index,
      ∀ y : L, (basisL.representation l).character y = φ y) ∧
    (∀ c ∈ L, δ c = 1) ∧ (∀ c : C, Odd (orderOf c) → δ c = 1) ∧
    (∀ (c : C) (X : Matrix.SpecialLinearGroup (Fin 2) F),
      (X : Matrix (Fin 2) (Fin 2) F) * X = -1 →
      (ρ c : Equiv.Perm (Omega F)) = coordinateGLAction F (Matrix.SpecialLinearGroup.toGL X) →
      φ c = ε ∧ δ c * φ c = ε) ∧
    (∀ (c : C) (a : F) (ha : a ≠ 0), ¬ IsSquare a →
      (ρ c : Equiv.Perm (Omega F)) = coordinateGLAction F (jMatrix a ha) →
      δ c = -1 ∧ φ c = -ε ∧ δ c * φ c = ε) := by
  intro φ δ ε B L
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hodd, hf, hcard⟩
  have hqodd : Odd (Nat.card F) := by
    rw [hcard]
    exact hodd.pow
  have hF2 : ringChar F ≠ 2 := by
    intro h
    have h' := FiniteField.even_card_iff_char_two.mp h
    rw [← Nat.card_eq_fintype_card] at h'
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hq3 : 3 ≤ Nat.card F := by
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    rw [hcard]
    calc 3 ≤ p := h3
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hε : IsSquare (-1 : F) ↔ Nat.card F % 4 = 1 := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hεne : ε ≠ -ε := by
    simp only [ε]
    split_ifs <;> norm_num
  let : MulAction C (Omega F) := MulAction.compHom (Omega F) (Γ.subtype.comp ρ)
  have hsmul : ∀ (c : C) (x : Omega F), c • x = (Γ.subtype.comp ρ) c x := fun _ _ => rfl
  have hGΓ : coordinateG F ≤ Γ := (coordinateG_le_D F).trans hDΓ
  have htwo : MulAction.IsMultiplyPretransitive C (Omega F) 2 :=
    two_transitive_of_coordinateG_le (Γ.subtype.comp ρ) hsmul (by
      intro g hg
      obtain ⟨c, hc⟩ := hρ ⟨g, hGΓ hg⟩
      exact ⟨c, by rw [MonoidHom.comp_apply, hc]; rfl⟩)
  have hΩ : Nat.card (Omega F) = Nat.card F + 1 := card_omega
  have hΩ2 : 2 ≤ Nat.card (Omega F) := by omega
  have hΩdvd : 2 ∣ Nat.card (Omega F) := by
    rw [hΩ]
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k + 1, by omega⟩
  obtain ⟨lφ, hlφ, hlφirr, hlφint, hlφB, hlφdeg, hlφker⟩ :=
    doubly_transitive_prime_divisible_degree_principal_augmentation hΩ2 basis ideal 2 principal
      hprincipal hΩdvd
  have hφchar : ∀ c, (basis.representation lφ).character c = φ c := fun c => hlφ c
  have hlφdeg' : Module.finrank ℂ (basis.representation lφ).vector = Nat.card F := by
    rw [hlφdeg, hΩ, Nat.add_sub_cancel]
  have hdeg_of : ∀ l, (basis.representation l).character 1 =
      (Module.finrank ℂ (basis.representation l).vector : ℂ) := fun l => Representation.char_one _
  have hφ1 : φ 1 = Nat.card F := by
    rw [← hφchar, hdeg_of, hlφdeg']
  have htoPerm : MulAction.toPermHom C (Omega F) = Γ.subtype.comp ρ := by
    ext c x
    rfl
  have hlφker' : MonoidHom.ker (basis.representation lφ).representation = ρ.ker := by
    rw [hlφker, htoPerm]
    exact MonoidHom.ker_comp_of_injective ρ Γ.subtype Subtype.val_injective
  have hφ_eq_card_iff : ∀ c, φ c = Nat.card F ↔ ρ c = 1 := by
    intro c
    constructor
    · intro h
      have h' : (Nat.card {x : Omega F // (ρ c : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 =
          Nat.card F := h
      have hcard' : Nat.card {x : Omega F // (ρ c : Equiv.Perm (Omega F)) x = x} =
          Nat.card (Omega F) := by
        have e : (Nat.card {x : Omega F // (ρ c : Equiv.Perm (Omega F)) x = x} : ℂ) =
            ((Nat.card F + 1 : ℕ) : ℂ) := by
          push_cast
          linear_combination h'
        rw [hΩ]
        exact_mod_cast e
      exact Subtype.ext (Equiv.ext (forall_of_card_subtype_eq _ hcard'))
    · intro h
      change (Nat.card {x : Omega F // (ρ c : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 = Nat.card F
      have e : Nat.card {x : Omega F // (ρ c : Equiv.Perm (Omega F)) x = x} =
          Nat.card (Omega F) := by
        rw [h]
        exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => rfl)
      rw [e, hΩ]
      push_cast
      ring
  have hsq2 : Nat.card (SquareClass F) = 2 := squareClass_card_two F hK
  let δΓ : Γ →* ℂˣ := (cardTwoSign (SquareClass F) hsq2).comp
    ((MonoidHom.fst _ _).comp ((theta F hK).comp (Subgroup.inclusion hΓE)))
  let lam : C →* ℂˣ := δΓ.comp ρ
  have hδval : ∀ c, δ c = 1 ∨ δ c = -1 := by
    intro c
    simp only [δ]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hδ_one_iff : ∀ c, δ c = 1 ↔
      ∃ (d : coordinateD F) (σ : F ≃+* F) (a : Matrix.GeneralLinearGroup (Fin 2) F),
        (ρ c : Equiv.Perm (Omega F)) = d * fieldExtension F σ ∧
          coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d ∧ IsSquare (a.det : F) := by
    intro c
    simp only [δ]
    split_ifs with h
    · simp only [true_iff]
      exact h
    · simp only [h, iff_false]
      norm_num
  have hlam : ∀ c, (lam c : ℂ) = δ c := by
    intro c
    change ((cardTwoSign (SquareClass F) hsq2
      (theta F hK (Subgroup.inclusion hΓE (ρ c))).1 : ℂˣ) : ℂ) = δ c
    rw [cardTwoSign_apply]
    have hiff := normalForm_square_iff_theta F hK (Subgroup.inclusion hΓE (ρ c))
    split_ifs with h
    · exact ((hδ_one_iff c).mpr (hiff.mpr h)).symm
    · rcases hδval c with h' | h'
      · exact absurd (hiff.mp ((hδ_one_iff c).mp h')) h
      · exact h'.symm
  have hclause1 : ∀ (c : C) (d : coordinateD F) (σ : F ≃+* F)
      (a : Matrix.GeneralLinearGroup (Fin 2) F),
      (ρ c : Equiv.Perm (Omega F)) = d * fieldExtension F σ →
      coordinatePGLAction F (Matrix.ProjGenLinGroup.mk a) = d →
      (δ c = 1 ↔ IsSquare (a.det : F)) := by
    intro c d σ a he ha
    rw [hδ_one_iff]
    exact normalForm_square_iff_det F hK (Subgroup.inclusion hΓE (ρ c)) d σ he a ha
  have hlam1 : ∀ c, ρ c = 1 → δ c = 1 := by
    intro c hc
    rw [← hlam]
    change ((δΓ (ρ c) : ℂˣ) : ℂ) = 1
    rw [hc, map_one, Units.val_one]
  have hδ1 : δ 1 = 1 := hlam1 1 (map_one ρ)
  have hδL : ∀ c ∈ L, δ c = 1 := by
    intro c hc
    rw [← hlam]
    have hker : Subgroup.inclusion hΓE (ρ c) ∈ (theta F hK).ker := by
      rw [theta_ker, Subgroup.mem_subgroupOf]
      exact hc
    change ((cardTwoSign (SquareClass F) hsq2
      (theta F hK (Subgroup.inclusion hΓE (ρ c))).1 : ℂˣ) : ℂ) = 1
    rw [MonoidHom.mem_ker.mp hker, cardTwoSign_apply]
    simp
  have hδodd : ∀ c : C, Odd (orderOf c) → δ c = 1 := by
    intro c hc
    have hpow : δ c ^ orderOf c = 1 := by
      rw [← hlam, ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one,
        Units.val_one]
    rcases hδval c with h | h
    · exact h
    · rw [h, hc.neg_one_pow] at hpow
      norm_num at hpow
  have hlamsq : ∀ c, lam c ^ 2 ^ 1 = 1 := by
    intro c
    apply Units.ext
    rw [pow_one, Units.val_pow_eq_pow_val, hlam, Units.val_one]
    rcases hδval c with h | h <;> rw [h] <;> norm_num
  obtain ⟨lδ, hlδ, hlδB⟩ :=
    exists_linearTwist_label_mem_coefficientBlock basis ideal 2 lam 1 hlamsq principal
  obtain ⟨lδφ, hlδφ, hlδφB⟩ :=
    exists_linearTwist_label_mem_coefficientBlock basis ideal 2 lam 1 hlamsq lφ
  have hδchar : ∀ c, (basis.representation lδ).character c = δ c := by
    intro c
    rw [hlδ, hprincipal, Pi.one_apply, mul_one, hlam]
  have hδφchar : ∀ c, (basis.representation lδφ).character c = δ c * φ c := by
    intro c
    rw [hlδφ, hlam, hφchar]
  have hlδφB' : lδφ ∈ B := by
    have h := coefficientBlock_eq_of_mem basis (localizedComplexIntegerRing ideal) hlφB
    rw [h] at hlδφB
    exact hlδφB
  have hdeg1 : Module.finrank ℂ (basis.representation principal).vector = 1 := by
    have h := hdeg_of principal
    rw [hprincipal, Pi.one_apply] at h
    exact_mod_cast h.symm
  have hdegδ : Module.finrank ℂ (basis.representation lδ).vector = 1 := by
    have h := hdeg_of lδ
    rw [hδchar, hδ1] at h
    exact_mod_cast h.symm
  have hdegδφ : Module.finrank ℂ (basis.representation lδφ).vector = Nat.card F := by
    have h := hdeg_of lδφ
    rw [hδφchar, hδ1, one_mul, hφ1] at h
    exact_mod_cast h.symm
  have hlδφker : MonoidHom.ker (basis.representation lδφ).representation = ρ.ker := by
    apply le_antisymm
    · intro c hc
      rw [MonoidHom.mem_ker] at hc ⊢
      have hval : (basis.representation lδφ).character c =
          (basis.representation lδφ).character 1 := by
        change LinearMap.trace ℂ _ ((basis.representation lδφ).representation c) =
          LinearMap.trace ℂ _ ((basis.representation lδφ).representation 1)
        rw [hc, map_one (basis.representation lδφ).representation]
      rw [hδφchar, hδφchar, hδ1, one_mul, hφ1] at hval
      rcases hδval c with h | h
      · rw [h, one_mul] at hval
        exact (hφ_eq_card_iff c).mp hval
      · exfalso
        rw [h] at hval
        have h' : -1 * ((Nat.card {x : Omega F // (ρ c : Equiv.Perm (Omega F)) x = x} : ℂ) - 1) =
            Nat.card F := hval
        have e : ((Nat.card {x : Omega F // (ρ c : Equiv.Perm (Omega F)) x = x} +
            Nat.card F : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
          push_cast
          linear_combination -h'
        have e' := Nat.cast_injective e
        omega
    · refine CFSG.LyonsUnitaryFour.le_ker_of_character_eq_degree _ _ fun c hc => ?_
      rw [MonoidHom.mem_ker] at hc
      change (basis.representation lδφ).character c = (basis.representation lδφ).character 1
      rw [hδφchar, hδφchar, hlam1 c hc, hδ1, (hφ_eq_card_iff c).mpr hc, hφ1]
  have hXclause : ∀ (c : C) (X : Matrix.SpecialLinearGroup (Fin 2) F),
      (X : Matrix (Fin 2) (Fin 2) F) * X = -1 →
      (ρ c : Equiv.Perm (Omega F)) = coordinateGLAction F (Matrix.SpecialLinearGroup.toGL X) →
      φ c = ε ∧ δ c * φ c = ε := by
    intro c X hX hc
    have hφc : φ c = ε := by
      change (Nat.card {x : Omega F // (ρ c : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 = ε
      rw [hc, card_fixed_sl_sq_neg_one hF2 X hX]
      simp only [ε]
      by_cases hs : IsSquare (-1 : F)
      · simp only [hs, hε.mp hs, ↓reduceIte]
        norm_num
      · simp only [hs, show ¬ (Nat.card F % 4 = 1) from fun h => hs (hε.mpr h), ↓reduceIte]
        norm_num
    have hδc : δ c = 1 := by
      obtain ⟨d, hd, hda⟩ := coordinateGLAction_normalForm F (Matrix.SpecialLinearGroup.toGL X)
      rw [hclause1 c d (RingEquiv.refl F) (Matrix.SpecialLinearGroup.toGL X) (hc.trans hd) hda]
      have hdet : ((Matrix.SpecialLinearGroup.toGL X).det : F) = 1 := by
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        exact X.2
      rw [hdet]
      exact ⟨1, (one_mul 1).symm⟩
    exact ⟨hφc, by rw [hδc, one_mul, hφc]⟩
  have hJclause : ∀ (c : C) (a : F) (ha : a ≠ 0), ¬ IsSquare a →
      (ρ c : Equiv.Perm (Omega F)) = coordinateGLAction F (jMatrix a ha) →
      δ c = -1 ∧ φ c = -ε ∧ δ c * φ c = ε := by
    intro c a ha hns hc
    have hδc : δ c = -1 := by
      obtain ⟨d, hd, hda⟩ := coordinateGLAction_normalForm F (jMatrix a ha)
      have h := hclause1 c d (RingEquiv.refl F) (jMatrix a ha) (hc.trans hd) hda
      rw [jMatrix_det] at h
      rcases hδval c with h1 | h1
      · exact absurd (h.mp h1) hns
      · exact h1
    have hφc : φ c = -ε := by
      change (Nat.card {x : Omega F // (ρ c : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 = -ε
      rw [hc, card_fixed_jMatrix hF2 a ha]
      have hiff := isSquare_neg_iff_of_not_isSquare ha hns
      simp only [ε]
      by_cases hs : IsSquare (-1 : F)
      · simp only [show ¬ IsSquare (-a) from fun h => (hiff.mp h) hs, hε.mp hs, ↓reduceIte]
        norm_num
      · simp only [hiff.mpr hs, show ¬ (Nat.card F % 4 = 1) from fun h => hs (hε.mpr h),
          ↓reduceIte]
        norm_num
    refine ⟨hδc, hφc, ?_⟩
    rw [hδc, hφc]
    ring
  obtain ⟨a₀, ha₀⟩ := FiniteField.exists_nonsquare hF2
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    exact ha₀ ⟨0, by ring⟩
  have hJmem : coordinateGLAction F (jMatrix a₀ ha₀0) ∈ Γ := by
    apply hDΓ
    rw [← coordinatePGLAction_range_eq_D]
    exact ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ := hρ ⟨_, hJmem⟩
  have hc₀' : (ρ c₀ : Equiv.Perm (Omega F)) = coordinateGLAction F (jMatrix a₀ ha₀0) := by
    rw [hc₀]
  obtain ⟨hδc₀, hφc₀, hδφc₀⟩ := hJclause c₀ a₀ ha₀0 ha₀ hc₀'
  have hq1 : (Nat.card F : ℂ) ≠ 1 := by
    intro h
    have : Nat.card F = 1 := by exact_mod_cast h
    omega
  have hdistinct : (fun _ => (1 : ℂ)) ≠ δ ∧ (fun _ => (1 : ℂ)) ≠ φ ∧
      (fun _ => (1 : ℂ)) ≠ (fun c => δ c * φ c) ∧ δ ≠ φ ∧ δ ≠ (fun c => δ c * φ c) ∧
      φ ≠ (fun c => δ c * φ c) := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have e := congrFun h c₀
      simp only [hδc₀] at e
      norm_num at e
    · have e := congrFun h 1
      simp only [hφ1] at e
      exact hq1 e.symm
    · have e := congrFun h 1
      simp only [hδ1, hφ1, one_mul] at e
      exact hq1 e.symm
    · have e := congrFun h 1
      rw [hδ1, hφ1] at e
      exact hq1 e.symm
    · have e := congrFun h 1
      simp only [hδ1, hφ1, one_mul] at e
      exact hq1 e.symm
    · have e : φ c₀ = δ c₀ * φ c₀ := congrFun h c₀
      rw [hδc₀, hφc₀] at e
      exact hεne (by linear_combination -e)
  obtain ⟨hd1, hd2, hd3, hd4, hd5, hd6⟩ := hdistinct
  have hlabel_ne : ∀ l l' : basis.index, ((basis.representation l).character ≠
      (basis.representation l').character) → l ≠ l' := by
    rintro l l' h rfl
    exact h rfl
  have hnodup : [principal, lδ, lφ, lδφ].Nodup := by
    have h12 : principal ≠ lδ := hlabel_ne _ _ fun h =>
      hd1 (funext fun c => (congrFun hprincipal c).symm.trans ((congrFun h c).trans (hδchar c)))
    have h13 : principal ≠ lφ := hlabel_ne _ _ fun h =>
      hd2 (funext fun c => (congrFun hprincipal c).symm.trans ((congrFun h c).trans (hφchar c)))
    have h14 : principal ≠ lδφ := hlabel_ne _ _ fun h =>
      hd3 (funext fun c => (congrFun hprincipal c).symm.trans ((congrFun h c).trans (hδφchar c)))
    have h23 : lδ ≠ lφ := hlabel_ne _ _ fun h =>
      hd4 (funext fun c => (hδchar c).symm.trans ((congrFun h c).trans (hφchar c)))
    have h24 : lδ ≠ lδφ := hlabel_ne _ _ fun h =>
      hd5 (funext fun c => (hδchar c).symm.trans ((congrFun h c).trans (hδφchar c)))
    have h34 : lφ ≠ lδφ := hlabel_ne _ _ fun h =>
      hd6 (funext fun c => (hφchar c).symm.trans ((congrFun h c).trans (hδφchar c)))
    simp [List.nodup_cons, h12, h13, h14, h23, h24, h34]
  have hP : ∀ l ∈ [principal, lδ, lφ, lδφ], (basis.representation l).IsIrreducible ∧ l ∈ B ∧
      ∀ c, ∃ z : ℤ, (basis.representation l).character c = z := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · refine ⟨basis.irreducible _, coefficientBlock_self_mem _ _ _, fun c => ⟨1, ?_⟩⟩
      rw [hprincipal]
      simp
    · refine ⟨basis.irreducible _, hlδB, fun c => ?_⟩
      rcases hδval c with h | h
      · exact ⟨1, by rw [hδchar, h]; simp⟩
      · exact ⟨-1, by rw [hδchar, h]; simp⟩
    · exact ⟨hlφirr, hlφB, hlφint⟩
    · refine ⟨basis.irreducible _, hlδφB', fun c => ?_⟩
      obtain ⟨z, hz⟩ := hlφint c
      rcases hδval c with h | h
      · exact ⟨z, by rw [hδφchar, h, one_mul, ← hφchar, hz]⟩
      · exact ⟨-z, by rw [hδφchar, h, ← hφchar, hz]; push_cast; ring⟩
  have hrestrict : ∀ basisL : FiniteIrreducibleCharacterBasis L, ∃ l : basisL.index,
      ∀ y : L, (basisL.representation l).character y = φ y := by
    intro basisL
    obtain ⟨principalL, hprincipalL⟩ :=
      finiteIrreducibleCharacterBasis_exists_principal_label basisL
    have hsmulL : ∀ (y : L) (x : Omega F), y • x = (Γ.subtype.comp (ρ.comp L.subtype)) y x :=
      fun _ _ => rfl
    have htwoL : MulAction.IsMultiplyPretransitive L (Omega F) 2 :=
      two_transitive_of_coordinateG_le (Γ.subtype.comp (ρ.comp L.subtype)) hsmulL (by
        intro g hg
        obtain ⟨c, hc⟩ := hρ ⟨g, hGΓ hg⟩
        have hcL : c ∈ L := by
          change (Γ.subtype.comp ρ) c ∈ coordinateG F
          rw [MonoidHom.comp_apply, hc]
          exact hg
        exact ⟨⟨c, hcL⟩, by
          change ((ρ c : Γ) : Equiv.Perm (Omega F)) = g
          rw [hc]⟩)
    obtain ⟨l, hl, -⟩ := doubly_transitive_prime_divisible_degree_principal_augmentation hΩ2
      basisL ideal 2 principalL hprincipalL hΩdvd
    exact ⟨l, fun y => hl y⟩
  refine ⟨hclause1, ⟨lam, hlam⟩, ⟨c₀, by rw [hδc₀]; norm_num⟩, fun c => ?_,
    ⟨lδ, lφ, lδφ, hδchar, hφchar, hδφchar, hnodup, hP, hdeg1, hdegδ, hlφdeg', hdegδφ,
      hlφker', hlδφker⟩, ⟨hd1, hd2, hd3, hd4, hd5, hd6⟩, hrestrict, hδL, hδodd, hXclause,
    hJclause⟩
  rcases hδval c with h | h <;> rw [h] <;> norm_num

end CFSG.Semidihedral.Principal
