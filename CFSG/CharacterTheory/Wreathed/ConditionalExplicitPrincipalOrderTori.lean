module

public import CFSG.CharacterTheory.Wreathed.ConditionalExplicitPrincipalOrderDual
public import CFSG.CharacterTheory.Wreathed.ConditionalCuspidalSelectionCount
public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesValues
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearCuspidalFamily

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
  CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Wreathed.CentralSL2Abelianization

section Involution

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

omit [Fintype F] in
theorem sq_eq_one_of_isConj_involutionY (h4 : 4 ∣ m) {t : CentralExtension F b m hm heven}
    (ht : IsConj (involutionY F b m hm heven) t) : t ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp ht
  rw [pow_two, show c * involutionY F b m hm heven * c⁻¹ * (c * involutionY F b m hm heven * c⁻¹) =
    c * (involutionY F b m hm heven * involutionY F b m hm heven) * c⁻¹ by group,
    involutionY_mul_self h4, mul_one, mul_inv_cancel]

theorem exists_splitTorus_isConj_involutionY (hb : ¬ IsSquare b) (hsq : IsSquare (-1 : F)) :
    ∃ t ∈ splitTorus F b m hm heven,
      t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ∧
        IsConj (involutionY F b m hm heven) t := by
  obtain ⟨E, _, _, basis, -, -⟩ := exists_cuspidal_data (F := F) hb
  have hfix : Nat.card {p : Omega F // involutionY F b m hm heven • p = p} = 2 := by
    rw [card_fixed_involutionY hb]
    exact ite_eq_left hsq
  rcases conjugacy_type_exists basis hb (involutionY F b m hm heven) with hA | ⟨α, hα, hc⟩ |
      ⟨t, ht, htA, hc⟩ | ⟨t, ht, htA, hc⟩
  · exact absurd hA (involutionY_not_mem hb)
  · have h1 := card_fixed_of_isConj (Ω := Omega F) hc
    rw [card_fixed_unipotent hα one_ne_zero, hfix] at h1
    norm_num at h1
  · exact ⟨t, ht, htA, hc⟩
  · have h1 := card_fixed_of_isConj (Ω := Omega F) hc
    rw [card_fixed_nonsplitTorus hb ht htA, hfix] at h1
    norm_num at h1

theorem exists_nonsplitTorus_isConj_involutionY {E : Type} [Field E] [Algebra F E]
    (basis : Module.Basis (Fin 2) F E) (hb : ¬ IsSquare b) (hsq : ¬ IsSquare (-1 : F)) :
    ∃ t ∈ nonsplitTorus F b m hm heven E basis,
      t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) ∧
        IsConj (involutionY F b m hm heven) t := by
  have hfix : Nat.card {p : Omega F // involutionY F b m hm heven • p = p} = 0 := by
    rw [card_fixed_involutionY hb]
    exact ite_eq_right hsq
  rcases conjugacy_type_exists basis hb (involutionY F b m hm heven) with hA | ⟨α, hα, hc⟩ |
      ⟨t, ht, htA, hc⟩ | ⟨t, ht, htA, hc⟩
  · exact absurd hA (involutionY_not_mem hb)
  · have h1 := card_fixed_of_isConj (Ω := Omega F) hc
    rw [card_fixed_unipotent hα one_ne_zero, hfix] at h1
    norm_num at h1
  · have h1 := card_fixed_of_isConj (Ω := Omega F) hc
    rw [card_fixed_splitTorus hb ht htA, hfix] at h1
    norm_num at h1
  · exact ⟨t, ht, htA, hc⟩

theorem principalSeries_involutionY_eq_zero (hb : ¬ IsSquare b) (hsq : ¬ IsSquare (-1 : F))
    (lam : splitTorus F b m hm heven →* ℂˣ) :
    principalSeries F b m hm heven lam (involutionY F b m hm heven) = 0 := by
  apply principalSeries_eq_zero
  intro p hp
  have h0 : Nat.card {p : Omega F // involutionY F b m hm heven • p = p} = 0 := by
    rw [card_fixed_involutionY hb]
    exact ite_eq_right hsq
  exact (Finite.card_eq_zero_iff.mp h0).false ⟨p, hp⟩

theorem cuspidalCharacter_involutionY_eq_zero {E : Type} [Field E] [Algebra F E]
    {basis : Module.Basis (Fin 2) F E} (hb : ¬ IsSquare b) (hsq : IsSquare (-1 : F))
    (ψ : AddChar F ℂ) (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    cuspidalCharacter hb ψ lam (involutionY F b m hm heven) = 0 := by
  have hfix : Nat.card {p : Omega F // involutionY F b m hm heven • p = p} = 2 := by
    rw [card_fixed_involutionY hb]
    exact ite_eq_left hsq
  rw [cuspidalCharacter, Pi.sub_apply, gammaCharacter_eq_zero hb _ ψ (Or.inr hfix),
    torusInduction_eq_zero hb lam (Or.inr hfix), sub_zero]

end Involution

section Split

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

theorem principalSeries_isClassFunction (lam : splitTorus F b m hm heven →* ℂˣ) :
    BlocksIsClassFunction (principalSeries F b m hm heven lam) :=
  inducedFunction_classFunction _ _

omit [Fintype F] in
theorem torusCharacter_two_pow_iff {n : ℕ} (hmn : m = 2 ^ n)
    (P : PrincipalSeriesParameter F b m) :
    (∃ k : ℕ, orderOf (torusCharacter F b m hm heven P) = 2 ^ k) ↔
      ∃ k : ℕ, orderOf P.1.1 = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    let δ : Fˣ →* splitTorus F b m hm heven :=
      (torusDiagHom F b m hm heven).codRestrict _ (torusDiag_mem_splitTorus F b m hm heven)
    have hP : P.1.1 = (torusCharacter F b m hm heven P).comp δ :=
      MonoidHom.ext fun c => (torusCharacter_torusDiag F b m hm heven P c).symm
    rw [hP]
    exact exists_two_pow_of_dvd ((orderOf_comp_dvd _ δ).trans hk.dvd)
  · rintro ⟨k, hk⟩
    have hα : P.1.1 ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
    apply exists_two_pow_of_dvd (N := n + k)
    apply orderOf_dvd_of_pow_eq_one
    refine MonoidHom.ext fun t => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, pow_add, ← hmn]
    exact torusCharacter_pow_eq_one P hα t

theorem sum_principalSeries_involutionY_sq [Fintype (PrincipalSeriesParameter F b m)]
    (hb : ¬ IsSquare b) (hsq : IsSquare (-1 : F)) {n : ℕ} (hmn : m = 2 ^ n) (h4 : 4 ∣ m) :
    ∑ P ∈ Finset.univ.filter (fun P : PrincipalSeriesParameter F b m =>
        P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k),
      principalSeries F b m hm heven (torusCharacter F b m hm heven P)
        (involutionY F b m hm heven) ^ 2 =
      2 * (m : ℂ) * ((2 ^ (Nat.card F - 1).factorization 2 : ℕ) - 2) := by
  set T := splitTorus F b m hm heven with hT
  have hcomm : ∀ s t : T, s * t = t * s := fun s t =>
    Subtype.ext (splitTorus_mul_comm F b m hm heven s.2 t.2)
  set w := weylElement F b m hm heven with hw
  obtain ⟨t, ht, htA, hc⟩ := exists_splitTorus_isConj_involutionY (hm := hm) (heven := heven) hb hsq
  set t₁ : T := ⟨t, ht⟩ with ht₁
  set t₂ : T := weylConj F b m hm heven t₁ with ht₂
  have ht1 : t₁ ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, ht₁]
    exact sq_eq_one_of_isConj_involutionY h4 hc)
  have ht2 : t₂ ^ 2 = 1 := by rw [ht₂, ← map_pow, ht1, map_one]
  have hne : t₁ ≠ t₂ := by
    intro h
    apply htA
    rw [← splitTorus_weyl_fixed_iff hb ht, ← weylElement_inv_conj]
    exact (congrArg Subtype.val h).symm
  have hval : ∀ P : PrincipalSeriesParameter F b m,
      principalSeries F b m hm heven (torusCharacter F b m hm heven P)
        (involutionY F b m hm heven) =
        (torusCharacter F b m hm heven P t₁ : ℂ) + (torusCharacter F b m hm heven P t₂ : ℂ) := by
    intro P
    rw [classFunction_isConj (principalSeries_isClassFunction _) hc]
    exact principalSeries_splitTorus F b m hm heven hb _ ht htA
  have hfinT : Finite (T →* ℂˣ) :=
    Finite.of_surjective _ (torusCharacter_surjective (F := F) (b := b) (m := m) (hm := hm)
      (heven := heven))
  have : Fintype (T →* ℂˣ) := Fintype.ofFinite _
  set S₂ := Finset.univ.filter (fun P : PrincipalSeriesParameter F b m =>
    ∃ k : ℕ, orderOf P.1.1 = 2 ^ k) with hS₂
  set S₁ := Finset.univ.filter (fun P : PrincipalSeriesParameter F b m => P.1.1 = 1) with hS₁
  have hsplit : Finset.univ.filter (fun P : PrincipalSeriesParameter F b m =>
      P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k) = S₂ \ S₁ := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, hS₂, hS₁]
    tauto
  have hsub : S₁ ⊆ S₂ := by
    intro P hP
    simp only [hS₁, hS₂, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
    exact ⟨0, by rw [hP, orderOf_one, pow_zero]⟩
  have hfull : ∑ P ∈ S₂, ((torusCharacter F b m hm heven P t₁ : ℂ) +
      (torusCharacter F b m hm heven P t₂ : ℂ)) ^ 2 =
      2 * (Finset.univ.filter (fun θ : T →* ℂˣ => ∃ k : ℕ, orderOf θ = 2 ^ k)).card := by
    rw [← sum_two_pow_hom_units_add_sq hcomm ht1 ht2 hne]
    refine Finset.sum_nbij' (torusCharacter F b m hm heven)
      (fun θ => (torusCharacter_surjective (F := F) (b := b) (m := m) (hm := hm)
        (heven := heven) θ).choose) ?_ ?_ ?_ ?_ ?_
    · intro P hP
      simp only [hS₂, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
      exact (torusCharacter_two_pow_iff hmn P).mpr hP
    · intro θ hθ
      simp only [hS₂, Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
      rw [← torusCharacter_two_pow_iff hmn]
      rw [(torusCharacter_surjective (F := F) (b := b) (m := m) (hm := hm) (heven := heven)
        θ).choose_spec]
      exact hθ
    · intro P _
      apply torusCharacter_injective F b m hm heven
      exact (torusCharacter_surjective (F := F) (b := b) (m := m) (hm := hm) (heven := heven)
        _).choose_spec
    · intro θ _
      exact (torusCharacter_surjective (F := F) (b := b) (m := m) (hm := hm) (heven := heven)
        θ).choose_spec
    · intro P _
      rfl
  have hcardT : (Finset.univ.filter (fun θ : T →* ℂˣ => ∃ k : ℕ, orderOf θ = 2 ^ k)).card =
      S₂.card := by
    symm
    refine Finset.card_nbij' (torusCharacter F b m hm heven)
      (fun θ => (torusCharacter_surjective (F := F) (b := b) (m := m) (hm := hm)
        (heven := heven) θ).choose) ?_ ?_ ?_ ?_
    · intro P hP
      simp only [hS₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hP ⊢
      exact (torusCharacter_two_pow_iff hmn P).mpr hP
    · intro θ hθ
      simp only [hS₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hθ ⊢
      rw [← torusCharacter_two_pow_iff hmn]
      rw [(torusCharacter_surjective (F := F) (b := b) (m := m) (hm := hm) (heven := heven)
        θ).choose_spec]
      exact hθ
    · intro P _
      apply torusCharacter_injective F b m hm heven
      exact (torusCharacter_surjective (F := F) (b := b) (m := m) (hm := hm) (heven := heven)
        _).choose_spec
    · intro θ _
      exact (torusCharacter_surjective (F := F) (b := b) (m := m) (hm := hm) (heven := heven)
        θ).choose_spec
  have hS₂card : S₂.card = (2 ^ (Nat.card F - 1).factorization 2) * m := by
    rw [hS₂, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      card_principalSeriesParameter_filter F b m hm (fun η => ∃ k : ℕ, orderOf η = 2 ^ k),
      card_two_pow_units_hom]
  have hS₁card : S₁.card = m := by
    rw [hS₁, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      card_principalSeriesParameter_trivial F b m hm]
  have hfixed : ∑ P ∈ S₁, ((torusCharacter F b m hm heven P t₁ : ℂ) +
      (torusCharacter F b m hm heven P t₂ : ℂ)) ^ 2 = 4 * m := by
    have hterm : ∀ P ∈ S₁, ((torusCharacter F b m hm heven P t₁ : ℂ) +
        (torusCharacter F b m hm heven P t₂ : ℂ)) ^ 2 = 4 := by
      intro P hP
      simp only [hS₁, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      have hfixP : weylParameter F b m heven P = P :=
        (weylParameter_eq_self_iff F b m heven hb P).mpr hP
      have h2 : torusCharacter F b m hm heven P t₂ = torusCharacter F b m hm heven P t₁ := by
        rw [ht₂, ← MonoidHom.comp_apply, torusCharacter_comp_weylConj, hfixP]
      have h1 : (torusCharacter F b m hm heven P t₁ : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← map_pow, ht1, map_one, Units.val_one]
      rw [h2]
      linear_combination 4 * h1
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hS₁card, nsmul_eq_mul]
    ring
  rw [hsplit, Finset.sum_congr rfl fun P _ => by rw [hval P],
    Finset.sum_sdiff_eq_sub hsub, hfull, hfixed, hcardT, hS₂card]
  push_cast
  ring

end Split

section Nonsplit

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

theorem sum_cuspidalCharacter_involutionY_sq (hb : ¬ IsSquare b) (hsq : ¬ IsSquare (-1 : F))
    {n : ℕ} (hmn : m = 2 ^ n) (h4 : 4 ∣ m) (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (ψ : AddChar F ℂ)
    [Fintype (NonsplitParameter F E b m h2 z hz)] :
    ∑ P ∈ Finset.univ.filter (fun P : NonsplitParameter F E b m h2 z hz =>
        P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k),
      cuspidalCharacter hb ψ (nonsplitCharacter F b m hm heven E basis h2 z hz P)
        (involutionY F b m hm heven) ^ 2 =
      2 * (m : ℂ) * ((2 ^ (Nat.card F + 1).factorization 2 : ℕ) - 2) := by
  set T := nonsplitTorus F b m hm heven E basis with hT
  have hcomm : ∀ s t : T, s * t = t * s := fun s t =>
    Subtype.ext (nonsplitTorus_mul_comm z hz s.2 t.2)
  set eqv := nonsplitCharacterEquiv F b m hm heven E basis h2 z hz with heqv
  have := finite_of_basis F E basis
  obtain ⟨t, ht, htA, hc⟩ := exists_nonsplitTorus_isConj_involutionY (hm := hm) (heven := heven)
    basis hb hsq
  set t₁ : T := ⟨t, ht⟩ with ht₁
  set t₂ : T := minusWeylConj h2 y hy t₁ with ht₂
  have ht1 : t₁ ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, ht₁]
    exact sq_eq_one_of_isConj_involutionY h4 hc)
  have ht2 : t₂ ^ 2 = 1 := by rw [ht₂, ← map_pow, ht1, map_one]
  have hne : t₁ ≠ t₂ := by
    intro h
    apply htA
    rw [← nonsplitTorus_fixed_iff z hz y hy h2 hb ht, ← nonsplitWeyl_inv_conj y hy h2]
    exact (congrArg Subtype.val h).symm
  have hval : ∀ P : NonsplitParameter F E b m h2 z hz,
      cuspidalCharacter hb ψ (nonsplitCharacter F b m hm heven E basis h2 z hz P)
        (involutionY F b m hm heven) ^ 2 =
        ((nonsplitCharacter F b m hm heven E basis h2 z hz P t₁ : ℂ) +
          (nonsplitCharacter F b m hm heven E basis h2 z hz P t₂ : ℂ)) ^ 2 := by
    intro P
    rw [classFunction_isConj (cuspidalCharacter_classFunction hb ψ _) hc]
    change cuspidalCharacter hb ψ _ (t₁ : CentralExtension F b m hm heven) ^ 2 = _
    rw [cuspidalCharacter_nonsplit hb y hy h2 ψ _ htA]
    ring
  have : Finite (T →* ℂˣ) := Finite.of_equiv _ eqv
  have : Fintype (T →* ℂˣ) := Fintype.ofFinite _
  set S₂ := Finset.univ.filter (fun P : NonsplitParameter F E b m h2 z hz =>
    ∃ k : ℕ, orderOf P.1.1 = 2 ^ k) with hS₂
  set S₁ := Finset.univ.filter (fun P : NonsplitParameter F E b m h2 z hz => P.1.1 = 1) with hS₁
  have hsplit : Finset.univ.filter (fun P : NonsplitParameter F E b m h2 z hz =>
      P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k) = S₂ \ S₁ := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, hS₂, hS₁]
    tauto
  have hsub : S₁ ⊆ S₂ := by
    intro P hP
    simp only [hS₁, hS₂, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
    exact ⟨0, by rw [hP, orderOf_one, pow_zero]⟩
  have hfull : ∑ P ∈ S₂, ((nonsplitCharacter F b m hm heven E basis h2 z hz P t₁ : ℂ) +
      (nonsplitCharacter F b m hm heven E basis h2 z hz P t₂ : ℂ)) ^ 2 =
      2 * (Finset.univ.filter (fun θ : T →* ℂˣ => ∃ k : ℕ, orderOf θ = 2 ^ k)).card := by
    rw [← sum_two_pow_hom_units_add_sq hcomm ht1 ht2 hne]
    refine Finset.sum_nbij' eqv eqv.symm ?_ ?_ ?_ ?_ ?_
    · intro P hP
      simp only [hS₂, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
      exact (nonsplitCharacter_two_pow_iff F E basis b hm heven h2 z hz hmn P).mpr hP
    · intro θ hθ
      simp only [hS₂, Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
      rw [← nonsplitCharacter_two_pow_iff F E basis b hm heven h2 z hz hmn]
      change ∃ k, orderOf (eqv (eqv.symm θ)) = 2 ^ k
      rw [eqv.apply_symm_apply]
      exact hθ
    · intro P _
      exact eqv.symm_apply_apply P
    · intro θ _
      exact eqv.apply_symm_apply θ
    · intro P _
      rfl
  have hcardT : (Finset.univ.filter (fun θ : T →* ℂˣ => ∃ k : ℕ, orderOf θ = 2 ^ k)).card =
      S₂.card := by
    symm
    refine Finset.card_nbij' eqv eqv.symm ?_ ?_ ?_ ?_
    · intro P hP
      simp only [hS₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hP ⊢
      exact (nonsplitCharacter_two_pow_iff F E basis b hm heven h2 z hz hmn P).mpr hP
    · intro θ hθ
      simp only [hS₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hθ ⊢
      rw [← nonsplitCharacter_two_pow_iff F E basis b hm heven h2 z hz hmn]
      change ∃ k, orderOf (eqv (eqv.symm θ)) = 2 ^ k
      rw [eqv.apply_symm_apply]
      exact hθ
    · intro P _
      exact eqv.symm_apply_apply P
    · intro θ _
      exact eqv.apply_symm_apply θ
  have hS₂card : S₂.card = (2 ^ (Nat.card F + 1).factorization 2) * m := by
    rw [hS₂, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      card_nonsplitParameter_filter F E basis b hm h2 z hz (fun α => ∃ k : ℕ, orderOf α = 2 ^ k),
      card_two_pow_hom_units, card_normOne F E basis]
  have hS₁card : S₁.card = m := by
    rw [hS₁, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_parameter_trivial_of_isCyclic (normOne F E) hm (cMinus F E b m h2 z hz)
  have hfixed : ∑ P ∈ S₁, ((nonsplitCharacter F b m hm heven E basis h2 z hz P t₁ : ℂ) +
      (nonsplitCharacter F b m hm heven E basis h2 z hz P t₂ : ℂ)) ^ 2 = 4 * m := by
    have hterm : ∀ P ∈ S₁, ((nonsplitCharacter F b m hm heven E basis h2 z hz P t₁ : ℂ) +
        (nonsplitCharacter F b m hm heven E basis h2 z hz P t₂ : ℂ)) ^ 2 = 4 := by
      intro P hP
      simp only [hS₁, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      have h2' : nonsplitCharacter F b m hm heven E basis h2 z hz P t₂ =
          nonsplitCharacter F b m hm heven E basis h2 z hz P t₁ := by
        rw [ht₂, ← MonoidHom.comp_apply,
          (minusWeyl_fixed_iff hb y hy h2 z hz P).mpr hP]
      have h1 : (nonsplitCharacter F b m hm heven E basis h2 z hz P t₁ : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← map_pow, ht1, map_one, Units.val_one]
      rw [h2']
      linear_combination 4 * h1
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, hS₁card, nsmul_eq_mul]
    ring
  rw [hsplit, Finset.sum_congr rfl fun P _ => hval P, Finset.sum_sdiff_eq_sub hsub, hfull,
    hfixed, hcardT, hS₂card]
  push_cast
  ring

end Nonsplit

end CFSG.Wreathed
