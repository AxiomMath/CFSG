module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSubfieldCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoEven

public noncomputable section

namespace CFSG.CGT.PushingUpLit.CGT6X.End3

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield mem_fixedSubfield)
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer (subfieldD subfieldD_mk
  subfieldD_injective subfieldD_surj_mk subfieldD_G fieldExtension_commute_subfieldD upperGL invGL
  map_upperGL map_invGL coordinateGLAction_upperGL coordinateGLAction_invGL)
open CFSG.ComponentClassification.CatalogueBLinearTwoFixed
  (coordinatePGLAction_mem_field_centralizer_iff)
open CFSG.ComponentClassification.CatalogueBHigherLinearField
  (pgl_fixed_iff_mem_subfield_range pglFieldAut_two)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (coordinateD_eq_G)

section Mult

variable {K : Type} [Field K]

theorem multiplier_mul (s t : Kˣ) : multiplier K s * multiplier K t = multiplier K (s * t) := by
  apply Equiv.ext
  intro x
  cases x with
  | none => rfl
  | some x => simp [mul_assoc]

theorem multiplier_one : multiplier K (1 : Kˣ) = 1 := by
  apply Equiv.ext
  intro x
  cases x with
  | none => rfl
  | some x => simp

@[expose] def multiplierHom (K : Type) [Field K] : Kˣ →* Equiv.Perm (Omega K) where
  toFun := multiplier K
  map_one' := multiplier_one
  map_mul' s t := (multiplier_mul s t).symm

theorem multiplier_conj_translation (s : Kˣ) (b : K) :
    multiplier K s * translation K b * (multiplier K s)⁻¹ = translation K ((s : K) * b) := by
  have hinv : (multiplier K s)⁻¹ = multiplier K s⁻¹ := by
    rw [inv_eq_iff_mul_eq_one, multiplier_mul, mul_inv_cancel, multiplier_one]
  rw [hinv]
  apply Equiv.ext
  intro x
  cases x with
  | none => rfl
  | some x =>
    simp only [Equiv.Perm.mul_apply, multiplier_some, translation_some, Option.some.injEq]
    rw [mul_add, ← mul_assoc, Units.mul_inv, one_mul]


end Mult

section Perm

variable {K : Type} [Field K] [Finite K]

@[expose] def jG (k : Subfield K) : Subgroup (Equiv.Perm (Omega K)) :=
  ((coordinateG k).subgroupOf (coordinateD k)).map ((coordinateD K).subtype.comp (subfieldD k))

theorem jG_le_G (k : Subfield K) : jG k ≤ coordinateG K := by
  rintro _ ⟨x, hx, rfl⟩
  exact subfieldD_G k x hx

theorem fixed_eq_jG [CharP K 2] (σ : K ≃+* K) (k : Subfield K) (hk : ∀ x, x ∈ k ↔ σ x = x) :
    coordinateG K ⊓ Subgroup.centralizer {fieldExtension K σ} = jG k := by
  classical
  have hkeq : k = fixedSubfield K σ :=
    Subfield.ext fun x => (hk x).trans (mem_fixedSubfield K σ x).symm
  subst hkeq
  set k := fixedSubfield K σ with hkdef
  have hσk : ∀ x ∈ k, σ x = x := fun x hx => (mem_fixedSubfield K σ x).mp hx
  have hDcent : coordinateD K ⊓ Subgroup.centralizer {fieldExtension K σ} =
      ((coordinateD K).subtype.comp (subfieldD k)).range := by
    apply le_antisymm
    · rintro g ⟨hgD, hgc⟩
      rw [← coordinatePGLAction_range_eq_D] at hgD
      obtain ⟨g', rfl⟩ := hgD
      have hfix := (coordinatePGLAction_mem_field_centralizer_iff K σ g').mp hgc
      rw [← pglFieldAut_two] at hfix
      obtain ⟨y, hy⟩ := (pgl_fixed_iff_mem_subfield_range (Fin 2) K σ g').mp hfix
      obtain ⟨B, rfl⟩ := ProjGenLinGroup.mk_surjective y
      refine ⟨pglEquivCoordinateD k (ProjGenLinGroup.mk B), ?_⟩
      change (subfieldD k (pglEquivCoordinateD k (ProjGenLinGroup.mk B)) :
        Equiv.Perm (Omega K)) = _
      rw [subfieldD_mk, ← hy]
      rfl
    · rintro _ ⟨y, rfl⟩
      exact ⟨(subfieldD k y).2, Subgroup.mem_centralizer_singleton_iff.mpr
        (fieldExtension_commute_subfieldD k σ hσk y).symm⟩
  apply le_antisymm
  · rintro g ⟨hgG, hgc⟩
    obtain ⟨y, hy⟩ := hDcent.le ⟨coordinateG_le_D K hgG, hgc⟩
    refine Subgroup.mem_map.mpr ⟨y, ?_, hy⟩
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.ext_iff.mp (coordinateD_eq_G (K := k)) (y : Equiv.Perm (Omega k))).mp y.2
  · rintro _ ⟨y, hyG, rfl⟩
    exact ⟨subfieldD_G k y hyG, (hDcent.ge ⟨y, rfl⟩).2⟩

theorem translation_mem_jG (k : Subfield K) (t : k) : translation K (t : K) ∈ jG k := by
  refine Subgroup.mem_map.mpr ⟨pglEquivCoordinateD k (ProjGenLinGroup.mk (upperGL t)), ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    change coordinateGLAction k (upperGL t) ∈ coordinateG k
    rw [coordinateGLAction_upperGL]
    exact Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)
  · change (subfieldD k (pglEquivCoordinateD k (ProjGenLinGroup.mk (upperGL t))) :
      Equiv.Perm (Omega K)) = _
    rw [subfieldD_mk, map_upperGL, coordinateGLAction_upperGL]

theorem inversion_mem_jG (k : Subfield K) : inversion K ∈ jG k := by
  refine Subgroup.mem_map.mpr ⟨pglEquivCoordinateD k (ProjGenLinGroup.mk invGL), ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    change coordinateGLAction k invGL ∈ coordinateG k
    rw [coordinateGLAction_invGL]
    exact Subgroup.subset_closure (Or.inr rfl)
  · change (subfieldD k (pglEquivCoordinateD k (ProjGenLinGroup.mk invGL)) :
      Equiv.Perm (Omega K)) = _
    rw [subfieldD_mk, map_invGL, coordinateGLAction_invGL]

theorem multiplier_mem_jG [CharP K 2] (k : Subfield K) (a : kˣ) (s : Kˣ) (hs : (s : K) = (a : k)) :
    multiplier K s ∈ jG k := by
  have hD : multiplier k a ∈ coordinateD k := Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
  refine Subgroup.mem_map.mpr ⟨⟨multiplier k a, hD⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    change multiplier k a ∈ coordinateG k
    rw [← coordinateD_eq_G (K := k)]
    exact hD
  · have h1 : (⟨multiplier k a, hD⟩ : coordinateD k) =
        pglEquivCoordinateD k (ProjGenLinGroup.mk (diagonalGL k a)) :=
      Subtype.ext (coordinatePGLAction_diagonal k a).symm
    have h2 : GeneralLinearGroup.map k.subtype (diagonalGL k a) = diagonalGL K s := by
      apply GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [diagonalGL, GeneralLinearGroup.map_apply, hs]
    change (subfieldD k ⟨multiplier k a, hD⟩ : Equiv.Perm (Omega K)) = _
    rw [h1, subfieldD_mk, h2]
    exact coordinatePGLAction_diagonal K s

theorem exists_add_mul (k : Subfield K) (hkK : Nat.card K = Nat.card k ^ 2) {s : K} (hs : s ∉ k)
    (b : K) : ∃ t t' : k, b = (t : K) + s * (t' : K) := by
  let F : k × k → K := fun p => (p.1 : K) + s * (p.2 : K)
  have hinj : Function.Injective F := by
    rintro ⟨t, t'⟩ ⟨u, u'⟩ h
    have h' : (t : K) + s * (t' : K) = (u : K) + s * (u' : K) := h
    have hee : t' = u' := by
      by_contra hne
      apply hs
      have hne' : ((u' : K) - (t' : K)) ≠ 0 := by
        intro h0
        exact hne (Subtype.ext (sub_eq_zero.mp h0).symm)
      have : s = ((t : K) - u) / ((u' : K) - t') := by
        field_simp
        linear_combination -h'
      rw [this]
      exact k.div_mem (k.sub_mem t.2 u.2) (k.sub_mem u'.2 t'.2)
    subst hee
    have : (t : K) = u := by simpa using h'
    exact Prod.ext (Subtype.ext this) rfl
  have hbij : Function.Bijective F :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hkK, sq])
  obtain ⟨⟨t, t'⟩, hp⟩ := hbij.2 b
  exact ⟨t, t', hp.symm⟩

theorem sup_conj_eq_top [CharP K 2] (k : Subfield K) (hkK : Nat.card K = Nat.card k ^ 2) (s : Kˣ)
    (hs : (s : K) ∉ k) :
    jG k ⊔ (jG k).map (MulAut.conj (multiplier K s)).toMonoidHom = coordinateG K := by
  have hmG : multiplier K s ∈ coordinateG K := by
    rw [← coordinateD_eq_G (K := K)]
    exact Subgroup.subset_closure (Or.inr ⟨s, rfl⟩)
  apply le_antisymm
  · refine sup_le (jG_le_G k) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hmG (jG_le_G k hy)) (inv_mem hmG)
  · rw [coordinateG, Subgroup.closure_le]
    rintro _ (⟨b, rfl⟩ | h)
    · obtain ⟨t, t', hb⟩ := exists_add_mul k hkK hs b
      have h1 : translation K (t : K) ∈
          jG k ⊔ (jG k).map (MulAut.conj (multiplier K s)).toMonoidHom :=
        Subgroup.mem_sup_left (translation_mem_jG k t)
      have h2 : translation K ((s : K) * (t' : K)) ∈
          jG k ⊔ (jG k).map (MulAut.conj (multiplier K s)).toMonoidHom := by
        apply Subgroup.mem_sup_right
        refine ⟨translation K (t' : K), translation_mem_jG k t', ?_⟩
        exact multiplier_conj_translation s t'
      have h3 : translation K ((t : K) + (s : K) * (t' : K)) =
          translation K (t : K) * translation K ((s : K) * (t' : K)) := by
        apply Equiv.ext
        intro x
        cases x with
        | none => rfl
        | some x =>
          simp only [Equiv.Perm.mul_apply, translation_some, Option.some.injEq]
          ring
      change translation K b ∈ _
      rw [hb, h3]
      exact mul_mem h1 h2
    · rw [Set.mem_singleton_iff.mp h]
      exact Subgroup.mem_sup_left (inversion_mem_jG k)

theorem exists_gen_cartan_perm [CharP K 2] (k : Subfield K) (hkK : Nat.card K = Nat.card k ^ 2)
    (hk4 : 4 ≤ Nat.card k) :
    ∃ m ∈ coordinateG K, jG k ⊔ (jG k).map (MulAut.conj m).toMonoidHom = coordinateG K ∧
      ∃ c ∈ jG k ⊓ (jG k).map (MulAut.conj m).toMonoidHom,
        Odd (orderOf c) ∧ 1 < orderOf c := by
  obtain ⟨s, hs⟩ : ∃ s : K, s ∉ k := by
    by_contra h
    push Not at h
    have hcard : Nat.card k = Nat.card K := Nat.card_congr (Equiv.subtypeUnivEquiv h)
    rw [hkK] at hcard
    nlinarith
  have hs0 : s ≠ 0 := fun h => hs (h ▸ k.zero_mem)
  let sU : Kˣ := Units.mk0 s hs0
  have hmG : multiplier K sU ∈ coordinateG K := by
    rw [← coordinateD_eq_G (K := K)]
    exact Subgroup.subset_closure (Or.inr ⟨sU, rfl⟩)
  refine ⟨multiplier K sU, hmG, sup_conj_eq_top k hkK sU hs, ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : kˣ, a ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : Nat.card kˣ = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => by rw [h x, h y]⟩, ⟨1⟩⟩
    rw [Nat.card_units] at h1
    omega
  let aK : Kˣ := Units.map (k.subtype : k →* K) a
  have haK : (aK : K) = ((a : k) : K) := rfl
  have hmem : multiplier K aK ∈ jG k := multiplier_mem_jG k a aK haK
  refine ⟨multiplier K aK, ⟨hmem, ⟨multiplier K aK, hmem, ?_⟩⟩, ?_, ?_⟩
  · change multiplier K sU * multiplier K aK * (multiplier K sU)⁻¹ = multiplier K aK
    rw [multiplier_mul, mul_comm sU aK, ← multiplier_mul, mul_inv_cancel_right]
  · have hpow : aK ^ (Nat.card k - 1) = 1 := by
      have h1 : a ^ (Nat.card k - 1) = 1 := by
        rw [← Nat.card_units]
        exact pow_card_eq_one'
      have h2 : aK ^ (Nat.card k - 1) = Units.map (k.subtype : k →* K) (a ^ (Nat.card k - 1)) := by
        rw [map_pow]
      rw [h2, h1, map_one]
    have hc : multiplier K aK ^ (Nat.card k - 1) = 1 := by
      have := map_pow (multiplierHom K) aK (Nat.card k - 1)
      change multiplier K (aK ^ (Nat.card k - 1)) = multiplier K aK ^ (Nat.card k - 1) at this
      rw [← this, hpow, multiplier_one]
    have hodd : Odd (Nat.card k - 1) := by
      have : Fintype k := Fintype.ofFinite k
      have h2 := FiniteField.even_card_of_char_two (ringChar.eq k 2)
      rw [← Nat.card_eq_fintype_card] at h2
      rw [Nat.odd_iff]
      omega
    exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hc)
  · have hne : multiplier K aK ≠ 1 := by
      intro h
      have h1 := congrArg (fun g : Equiv.Perm (Omega K) => g (some 1)) h
      simp only [multiplier_some, Equiv.Perm.one_apply, Option.some.injEq, mul_one] at h1
      apply ha
      apply Units.ext
      apply Subtype.ext
      exact h1
    have hpos : 0 < orderOf (multiplier K aK) := orderOf_pos _
    have hne1 : orderOf (multiplier K aK) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    omega

end Perm

end CFSG.CGT.PushingUpLit.CGT6X.End3
