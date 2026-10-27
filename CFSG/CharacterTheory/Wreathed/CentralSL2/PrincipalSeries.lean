module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.PrincipalSeriesValues
public import CFSG.CharacterTheory.Wreathed.CentralSL2.Augmentation
public import CFSG.CharacterTheory.Wreathed.CentralSL2.CharacterTools

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section LinearTwist

variable {K : Type} [Group K] [Fintype K]

theorem linearTwist_mem_blocksIrr (χ : K →* ℂˣ) {θ : K → ℂ} (hθ : θ ∈ BlocksIrr K) :
    (fun g => (χ g : ℂ) * θ g) ∈ BlocksIrr K := by
  have hθθ : BlocksInnerProduct θ θ = 1 := by
    have h := blocksInnerProduct_irreducible ⟨θ, hθ⟩ ⟨θ, hθ⟩
    rw [ite_eq_left rfl] at h
    exact h
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hθ
  let ρ' : Representation ℂ K V :=
    { toFun := fun g => (χ g : ℂ) • ρ g
      map_one' := by simp
      map_mul' := fun g h => by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul] }
  have hchar : ρ'.character = fun g => (χ g : ℂ) * ρ.character g := by
    funext g
    change LinearMap.trace ℂ V ((χ g : ℂ) • ρ g) = _
    rw [map_smul, smul_eq_mul]
    rfl
  rw [← hchar]
  apply CFSG.Wreathed.mem_blocksIrr_of_norm_one ρ'
  rw [hchar]
  rw [← hθθ]
  unfold BlocksInnerProduct
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_mul, conj_units_hom]
  have h1 : (χ g : ℂ) * (χ g⁻¹ : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  linear_combination (ρ.character g * starRingEnd ℂ (ρ.character g)) * h1

end LinearTwist

section Irreducibility

variable (F : Type) [Field F] [Fintype F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

omit [Fintype F] in
theorem hom_eq_one_of_inv_eq_one {η : Fˣ →* ℂˣ} (h : η⁻¹ = 1) : η = 1 := by
  ext c
  have := DFunLike.congr_fun h c
  simpa using this

theorem ne_weylParameter (hb : ¬ IsSquare b) {P : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1) : P ≠ weylParameter F b m heven P :=
  fun h => hP ((weylParameter_eq_self_iff F b m heven hb P).mp h.symm)

omit [Fintype F] in
theorem weylParameter_ne_one {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1) :
    (weylParameter F b m heven P).1.1 ≠ 1 :=
  fun h => hP (hom_eq_one_of_inv_eq_one F h)

theorem principalSeries_one (lam : splitTorus F b m hm heven →* ℂˣ) :
    principalSeries F b m hm heven lam 1 = (Nat.card F : ℂ) + 1 := by
  have h := principalSeries_cyclicGenerator_sq_zpow F b m hm heven lam 0
  rw [zpow_zero, zpow_zero, mul_one] at h
  exact h

theorem principalSeries_mem_blocksIrr (hb : ¬ IsSquare b) (P : PrincipalSeriesParameter F b m)
    (hP : P.1.1 ≠ 1) :
    principalSeries F b m hm heven (torusCharacter F b m hm heven P) ∈
      BlocksIrr (CentralExtension F b m hm heven) := by
  have hlin : (fun g : borelSubgroup F b m hm heven =>
      (borelInflation F b m hm heven (torusCharacter F b m hm heven P) g : ℂ)) ∈
        BlocksIrr (borelSubgroup F b m hm heven) :=
    monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp
      (borelInflation F b m hm heven (torusCharacter F b m hm heven P)))
  obtain ⟨W, _, _, _, τ, hτ⟩ :=
    CFSG.Wreathed.exists_representation_inducedFunction (borelSubgroup F b m hm heven) hlin
  have hnorm : BlocksInnerProduct τ.character τ.character = 1 := by
    rw [hτ]
    change BlocksInnerProduct (principalSeries F b m hm heven (torusCharacter F b m hm heven P))
      (principalSeries F b m hm heven (torusCharacter F b m hm heven P)) = 1
    rw [principalSeries_inner_parameter, ite_eq_left rfl,
      ite_eq_right (ne_weylParameter F b m heven hb hP), add_zero]
  have h := CFSG.Wreathed.mem_blocksIrr_of_norm_one τ hnorm
  rw [hτ] at h
  exact h

theorem principalSeries_eq_iff (hb : ¬ IsSquare b) {P Q : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1) (hQ : Q.1.1 ≠ 1) :
    principalSeries F b m hm heven (torusCharacter F b m hm heven P) =
        principalSeries F b m hm heven (torusCharacter F b m hm heven Q) ↔
      Q = P ∨ Q = weylParameter F b m heven P := by
  have hPw := ne_weylParameter F b m heven hb hP
  constructor
  · intro h
    have h1 := principalSeries_inner_parameter F b m hm heven P Q
    rw [← h, principalSeries_inner_parameter, ite_eq_left rfl, ite_eq_right hPw] at h1
    by_contra hne
    obtain ⟨hne1, hne2⟩ := not_or.mp hne
    have hPQ : P ≠ Q := fun h => hne1 h.symm
    have hPwQ : P ≠ weylParameter F b m heven Q := fun h =>
      hne2 (by rw [h, weylParameter_involutive])
    rw [ite_eq_right hPQ, ite_eq_right hPwQ] at h1
    norm_num at h1
  · rintro (rfl | rfl)
    · rfl
    · have hirrP := principalSeries_mem_blocksIrr F b m hm heven hb P hP
      have hirrQ := principalSeries_mem_blocksIrr F b m hm heven hb _
        (weylParameter_ne_one F b m heven hP)
      have h1 := principalSeries_inner_parameter F b m hm heven P (weylParameter F b m heven P)
      rw [ite_eq_right hPw, weylParameter_involutive, ite_eq_left rfl, zero_add] at h1
      have h2 := blocksInnerProduct_irreducible ⟨_, hirrP⟩ ⟨_, hirrQ⟩
      change BlocksInnerProduct (principalSeries F b m hm heven (torusCharacter F b m hm heven P))
        (principalSeries F b m hm heven (torusCharacter F b m hm heven
          (weylParameter F b m heven P))) = _ at h2
      rw [h1] at h2
      by_contra hne
      rw [ite_eq_right (fun h => hne (congrArg Subtype.val h))] at h2
      norm_num at h2

end Irreducibility

section Count

variable (F : Type) [Field F] [Fintype F] (b : Fˣ) (m : ℕ)

theorem card_pow_eq (hm : 0 < m) (c : ℂˣ) : Nat.card {z : ℂˣ // z ^ m = c} = m := by
  obtain ⟨z₀, hz₀⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ) hm
  have hz0 : z₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hz₀
    exact c.ne_zero hz₀.symm
  let u₀ : ℂˣ := Units.mk0 z₀ hz0
  have hu₀ : u₀ ^ m = c := Units.ext (by simp [u₀, hz₀])
  have : NeZero m := ⟨hm.ne'⟩
  let e : {z : ℂˣ // z ^ m = c} ≃ rootsOfUnity m ℂ :=
    { toFun := fun z => ⟨z.1 * u₀⁻¹, by
        rw [mem_rootsOfUnity, mul_pow, z.2, inv_pow, hu₀, mul_inv_cancel]⟩
      invFun := fun ζ => ⟨ζ.1 * u₀, by
        rw [mul_pow, (mem_rootsOfUnity _ _).mp ζ.2, hu₀, one_mul]⟩
      left_inv := fun z => by
        apply Subtype.ext
        simp
      right_inv := fun ζ => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Complex.card_rootsOfUnity]

theorem card_units_hom : Nat.card (Fˣ →* ℂˣ) = Nat.card F - 1 := by
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Fˣ ℂ
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_units,
    Nat.card_eq_fintype_card]

theorem finite_units_hom : Finite (Fˣ →* ℂˣ) := by
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self Fˣ ℂ
  exact Finite.of_equiv _ e.toEquiv.symm

theorem card_principalSeriesParameter (hm : 0 < m) :
    Nat.card (PrincipalSeriesParameter F b m) = (Nat.card F - 1) * m := by
  have := finite_units_hom F
  have : Fintype (Fˣ →* ℂˣ) := Fintype.ofFinite _
  have hfin : ∀ η : Fˣ →* ℂˣ, Finite {z : ℂˣ // z ^ m = η (torusConstant F b m)} := fun η =>
    Nat.finite_of_card_ne_zero (by rw [card_pow_eq m hm]; exact hm.ne')
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    fun (η : Fˣ →* ℂˣ) (z : ℂˣ) => z ^ m = η (torusConstant F b m)), Nat.card_sigma]
  simp only [card_pow_eq m hm]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    card_units_hom]

omit [Fintype F] in
theorem card_principalSeriesParameter_trivial (hm : 0 < m) :
    Nat.card {P : PrincipalSeriesParameter F b m // P.1.1 = 1} = m := by
  let e : {P : PrincipalSeriesParameter F b m // P.1.1 = 1} ≃ {z : ℂˣ // z ^ m = 1} :=
    { toFun := fun P => ⟨P.1.1.2, by rw [P.1.2, P.2]; rfl⟩
      invFun := fun z => ⟨⟨(1, z.1), by rw [z.2]; rfl⟩, rfl⟩
      left_inv := fun P => by
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext P.2.symm rfl
      right_inv := fun z => rfl }
  rw [Nat.card_congr e, card_pow_eq m hm]

variable (hm : 0 < m) (heven : Even m)

theorem principalSeries_ncard (hb : ¬ IsSquare b) :
    Set.ncard ((fun P => principalSeries F b m hm heven (torusCharacter F b m hm heven P)) ''
      {P : PrincipalSeriesParameter F b m | P.1.1 ≠ 1}) = m * (Nat.card F - 2) / 2 := by
  have hcardP := card_principalSeriesParameter F b m hm
  have hfinP : Finite (PrincipalSeriesParameter F b m) := Nat.finite_of_card_ne_zero (by
    rw [hcardP]
    have : 2 ≤ Nat.card F := Finite.one_lt_card
    exact Nat.mul_ne_zero (by omega) hm.ne')
  have : Fintype (PrincipalSeriesParameter F b m) := Fintype.ofFinite _
  set f := fun P => principalSeries F b m hm heven (torusCharacter F b m hm heven P) with hf
  set s := Finset.univ.filter (fun P : PrincipalSeriesParameter F b m => P.1.1 ≠ 1) with hs
  have hset : {P : PrincipalSeriesParameter F b m | P.1.1 ≠ 1} = ↑s := by
    ext P
    simp [hs]
  have hfibre : ∀ y ∈ s.image f, (s.filter (fun P => f P = y)).card = 2 := by
    intro y hy
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hy
    have hP₀' : P₀.1.1 ≠ 1 := (Finset.mem_filter.mp hP₀).2
    have hpair : s.filter (fun P => f P = f P₀) = {P₀, weylParameter F b m heven P₀} := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, hs,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hQ, hfQ⟩
        exact (principalSeries_eq_iff F b m hm heven hb hP₀' hQ).mp hfQ.symm
      · rintro (rfl | rfl)
        · exact ⟨hP₀', rfl⟩
        · refine ⟨weylParameter_ne_one F b m heven hP₀', ?_⟩
          exact ((principalSeries_eq_iff F b m hm heven hb hP₀'
            (weylParameter_ne_one F b m heven hP₀')).mpr (Or.inr rfl)).symm
    rw [hpair, Finset.card_pair (ne_weylParameter F b m heven hb hP₀')]
  have h2 : s.card = 2 * (s.image f).card := by
    rw [Finset.card_eq_sum_card_image f s, Finset.sum_congr rfl hfibre, Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hcomp : s.card + (Finset.univ.filter
      (fun P : PrincipalSeriesParameter F b m => P.1.1 = 1)).card = (Nat.card F - 1) * m := by
    rw [← hcardP, Nat.card_eq_fintype_card, add_comm, hs]
    convert Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun P : PrincipalSeriesParameter F b m => P.1.1 = 1)
    exact Finset.card_univ.symm
  have htriv : (Finset.univ.filter
      (fun P : PrincipalSeriesParameter F b m => P.1.1 = 1)).card = m := by
    have h := card_principalSeriesParameter_trivial F b m hm
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
    exact h
  rw [htriv] at hcomp
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h3 : (Nat.card F - 1) * m = m * (Nat.card F - 2) + m := by
    have : Nat.card F - 1 = (Nat.card F - 2) + 1 := by omega
    rw [this, add_mul, one_mul, mul_comm]
  have hs' : s.card = m * (Nat.card F - 2) := by omega
  rw [hset, ← Finset.coe_image, Set.ncard_coe_finset]
  omega

end Count

section TrivialCharacter

variable (F : Type) [Field F] [Fintype F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem steinberg_mem_blocksIrr :
    (fun g => fixedPointCount (CentralExtension F b m hm heven) (Omega F) g - 1) ∈
      BlocksIrr (CentralExtension F b m hm heven) := by
  have h2 := centralExtension_isMultiplyPretransitive F b m hm heven
  have ht : MulAction.IsPretransitive (CentralExtension F b m hm heven) (Omega F) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  exact ((permutation_character_orbit_count (CentralExtension F b m hm heven)
    (Omega F)).2.2.2 ht (two_le_card_omega F)).mp h2

theorem fixedPointCount_one :
    fixedPointCount (CentralExtension F b m hm heven) (Omega F) 1 = (Nat.card F : ℂ) + 1 := by
  have huniv : MulAction.fixedBy (Omega F) (1 : CentralExtension F b m hm heven) = Set.univ := by
    ext y
    simp
  rw [fixedPointCount, huniv, Nat.card_congr (Equiv.Set.univ _), card_omega]
  push_cast
  rfl

theorem principalSeries_of_restrict (lam : splitTorus F b m hm heven →* ℂˣ)
    (χ : CentralExtension F b m hm heven →* ℂˣ)
    (hχ : ∀ g : borelSubgroup F b m hm heven, borelInflation F b m hm heven lam g = χ g)
    (g : CentralExtension F b m hm heven) :
    principalSeries F b m hm heven lam g =
      (χ g : ℂ) * fixedPointCount (CentralExtension F b m hm heven) (Omega F) g := by
  rw [principalSeries_apply]
  have hterm : ∀ p : Omega F, extendByZero (borelSubgroup F b m hm heven)
      (fun g => (borelInflation F b m hm heven lam g : ℂ))
      ((borelRep F b m hm heven p)⁻¹ * g * borelRep F b m hm heven p) =
        if g • p = p then (χ g : ℂ) else 0 := by
    intro p
    by_cases hp : g • p = p
    · rw [ite_eq_left hp]
      have hmem : (borelRep F b m hm heven p)⁻¹ * g * borelRep F b m hm heven p ∈
          borelSubgroup F b m hm heven := by
        rw [conj_mem_iff_of_stabilizer (mem_borelSubgroup_iff F b m hm heven), borelRep_smul]
        exact hp
      rw [extendByZero_of_mem _ _ hmem, hχ]
      have hc := units_hom_conj χ (borelRep F b m hm heven p)⁻¹ g
      rw [inv_inv] at hc
      exact congrArg Units.val hc
    · rw [ite_eq_right hp]
      exact principalSeries_term_of_not_fixed F b m hm heven lam hp
  rw [Finset.sum_congr rfl fun p _ => hterm p, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_comm]
  congr 1
  rw [fixedPointCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact_mod_cast congrArg Finset.card (Finset.filter_congr fun p _ => Iff.rfl)

omit [Fintype F] in
theorem rootCharacter_baseResidue_quotientClass (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : ℕ)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    (rootCharacter m hm ζ hζ r (baseResidue F b m hm heven
      (quotientClass F b m hm heven X j)) : ℂ) = ζ ^ (r * j.val) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  rw [baseResidue_quotientClass]
  conv_lhs => rw [← ZMod.natCast_zmod_val j, map_natCast]
  exact rootCharacter_natCast m hm ζ hζ r j.val

theorem principalSeries_trivial (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : Fin m)
    (P : PrincipalSeriesParameter F b m) (hP1 : P.1.1 = 1) (hP2 : (P.1.2 : ℂ) = ζ ^ r.val) :
    principalSeries F b m hm heven (torusCharacter F b m hm heven P) = fun g =>
      (rootCharacter m hm ζ hζ r.val (baseResidue F b m hm heven g) : ℂ) +
        (rootCharacter m hm ζ hζ r.val (baseResidue F b m hm heven g) : ℂ) *
          (fixedPointCount (CentralExtension F b m hm heven) (Omega F) g - 1) := by
  let χ : CentralExtension F b m hm heven →* ℂˣ :=
    (rootCharacter m hm ζ hζ r.val).comp (baseResidue F b m hm heven)
  have hT : torusCharacter F b m hm heven P = χ.comp (splitTorus F b m hm heven).subtype := by
    symm
    apply splitTorusCharacter_unique
    · intro c
      change rootCharacter m hm ζ hζ r.val
        (baseResidue F b m hm heven (torusDiag F b m hm heven c)) = P.1.1 c
      rw [baseResidue_torusDiag, map_one, hP1, MonoidHom.one_apply]
    · apply Units.ext
      change (rootCharacter m hm ζ hζ r.val
        (baseResidue F b m hm heven (torusGenerator F b m hm heven)) : ℂ) = P.1.2
      rw [baseResidue_torusGenerator, hP2]
      have h1 := rootCharacter_natCast m hm ζ hζ r.val 1
      rw [Nat.cast_one, mul_one] at h1
      exact h1
  have hB : ∀ g : borelSubgroup F b m hm heven,
      borelInflation F b m hm heven (torusCharacter F b m hm heven P) g = χ g := by
    intro g
    simp only [borelInflation, MonoidHom.comp_apply, hT]
    change χ (borelProjectionFun F b m hm heven g) = χ g
    rw [borelProjectionFun, map_mul, map_inv]
    have hU : χ (unipotentElement F b m hm heven (borelTranslation F b m hm heven g)) = 1 := by
      change rootCharacter m hm ζ hζ r.val (baseResidue F b m hm heven
        (specialInclusion F b m hm heven _)) = 1
      rw [baseResidue_specialInclusion, map_one]
    rw [hU, inv_one, one_mul]
  funext g
  rw [principalSeries_of_restrict F b m hm heven _ χ hB g]
  change (χ g : ℂ) * _ = (χ g : ℂ) + (χ g : ℂ) * _
  ring

end TrivialCharacter

section Projective

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem centralExtension_projective (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m))
    (y z : Fin 2 → F) (hy : y ≠ 0) (hz : z ≠ 0)
    (hzy : z = (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
      GeneralLinearGroup (Fin 2) F).val *ᵥ y) :
    coordinateEquiv F (quotientClass F b m hm heven X j •
      (coordinateEquiv F).symm (Projectivization.mk F y hy)) = Projectivization.mk F z hz := by
  set C := SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val with hC
  rw [centralExtension_smul_def, projAction_quotientClass]
  change coordinateEquiv F (coordinatePGLAction F (Matrix.ProjGenLinGroup.mk C) _) = _
  rw [coordinatePGLAction_point, (coordinateEquiv F).apply_symm_apply,
    Projectivization.PGL.mk_smul_mk]
  congr 1
  rw [hzy, Units.smul_def]
  rfl

end Projective

theorem base_principal_series_character_family {F : Type} [Field F] [Fintype F]
    {p f : ℕ} (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hcard : Nat.card F = p ^ f)
    (b : Fˣ) (hb : ¬ IsSquare b) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    let G := CentralExtension F b m hm heven
    let B := borelSubgroup F b m hm heven
    let T := splitTorus F b m hm heven
    let U := unipotentSubgroup F b m hm heven
    let u := cyclicGenerator F b m hm heven
    let h := torusDiag F b m hm heven
    let w := weylElement F b m hm heven
    let v := torusGenerator F b m hm heven
    let a := u ^ 2
    let x := u ^ m
    let c₀ := torusConstant F b m
    let St : G → ℂ := fun g => fixedPointCount G (Omega F) g - 1
    let Ψ : PrincipalSeriesParameter F b m → G → ℂ := fun P =>
      principalSeries F b m hm heven (torusCharacter F b m hm heven P)
    (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (y z : Fin 2 → F) (hy : y ≠ 0)
        (hz : z ≠ 0),
      z = (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
        GeneralLinearGroup (Fin 2) F).val *ᵥ y →
      coordinateEquiv F (quotientClass F b m hm heven X j •
        (coordinateEquiv F).symm (Projectivization.mk F y hy)) = Projectivization.mk F z hz) ∧
    (∀ c : Fˣ, h c = specialInclusion F b m hm heven (diagSL F c) ∧
      (diagSL F c : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)]) ∧
    w = specialInclusion F b m hm heven (weyl F) ∧
    (weyl F : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] ∧ v = w⁻¹ * u ∧
    x = specialInclusion F b m hm heven (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) ∧
    (∀ g, g ∈ U ↔ ∃ t : F, g = specialInclusion F b m hm heven (upperSL F t)) ∧
    (∀ t : F, (upperSL F t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1]) ∧
    B = MulAction.stabilizer G (none : Omega F) ∧
    T = B ⊓ MulAction.stabilizer G (some 0 : Omega F) ∧
    U ≤ B ∧ T ≤ B ∧ U ⊓ T = ⊥ ∧ (∀ g ∈ B, ∃ n ∈ U, ∃ t ∈ T, g = n * t) ∧
    (∀ g ∈ B, ∀ n ∈ U, g * n * g⁻¹ ∈ U) ∧
    (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) ∧ Nat.card T = m * (Nat.card F - 1) ∧
    (∀ c d : Fˣ, h (c * d) = h c * h d) ∧ Function.Injective h ∧
    T = Subgroup.closure (Set.range h ∪ {v}) ∧ (∀ c : Fˣ, v * h c = h c * v) ∧ v ^ m = h c₀ ∧
    c₀ = -((-b⁻¹) ^ (m / 2)) ∧
    (∀ (K : Type) [Group K] (η : Fˣ →* K) (z : K), (∀ c, z * η c = η c * z) →
      z ^ m = η c₀ →
      ∃! φ : T →* K, (∀ c, φ ⟨h c, torusDiag_mem_splitTorus F b m hm heven c⟩ = η c) ∧
        φ ⟨v, torusGenerator_mem_splitTorus F b m hm heven⟩ = z) ∧
    (∀ g ∈ T, ∃! ck : Fˣ × Fin m, g = h ck.1 * v ^ (ck.2 : ℕ)) ∧
    (∀ P : PrincipalSeriesParameter F b m,
      (∀ c, torusCharacter F b m hm heven P
        ⟨h c, torusDiag_mem_splitTorus F b m hm heven c⟩ = P.1.1 c) ∧
      torusCharacter F b m hm heven P ⟨v, torusGenerator_mem_splitTorus F b m hm heven⟩ = P.1.2 ∧
      ∀ φ : T →* ℂˣ, (∀ c, φ ⟨h c, torusDiag_mem_splitTorus F b m hm heven c⟩ = P.1.1 c) →
        φ ⟨v, torusGenerator_mem_splitTorus F b m hm heven⟩ = P.1.2 →
          φ = torusCharacter F b m hm heven P) ∧
    Function.Surjective (borelProjection F b m hm heven) ∧
    (∀ g : B, borelProjection F b m hm heven g = 1 ↔ (g : G) ∈ U) ∧
    (∀ (g : B) (t : T), (g : G) * (t : G)⁻¹ ∈ U → borelProjection F b m hm heven g = t) ∧
    (∀ P, Ψ P = inducedFunction B fun g =>
      (torusCharacter F b m hm heven P (borelProjection F b m hm heven g) : ℂ)) ∧
    (∀ P, (weylParameter F b m heven P).1 = (P.1.1⁻¹, P.1.1 b * P.1.2)) ∧
    Function.Involutive (weylParameter F b m heven) ∧
    (∀ P Q, BlocksInnerProduct (Ψ P) (Ψ Q) =
      (if P = Q then 1 else 0) + (if P = weylParameter F b m heven Q then 1 else 0)) ∧
    (∀ P, weylParameter F b m heven P = P ↔ P.1.1 = 1) ∧
    (∀ P, P.1.1 ≠ 1 → Ψ P ∈ BlocksIrr G ∧ Ψ P 1 = Nat.card F + 1) ∧
    (∀ P Q, P.1.1 ≠ 1 → Q.1.1 ≠ 1 → (Ψ P = Ψ Q ↔ Q = P ∨ Q = weylParameter F b m heven P)) ∧
    Set.ncard (Ψ '' {P | P.1.1 ≠ 1}) = m * (Nat.card F - 2) / 2 ∧
    (∀ (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : Fin m) (P : PrincipalSeriesParameter F b m),
      P.1.1 = 1 → (P.1.2 : ℂ) = ζ ^ r.val →
      let χ : G → ℂ := fun g =>
        (rootCharacter m hm ζ hζ r.val (baseResidue F b m hm heven g) : ℂ)
      (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)),
        χ (quotientClass F b m hm heven X j) = ζ ^ (r.val * j.val)) ∧
      Ψ P = (fun g => χ g + χ g * St g) ∧ χ ∈ BlocksIrr G ∧
      (fun g => χ g * St g) ∈ BlocksIrr G ∧ χ 1 = 1 ∧ χ 1 * St 1 = Nat.card F) ∧
    (∀ P (k : ℤ), Ψ P (a ^ k) = ((Nat.card F : ℂ) + 1) *
      (torusCharacter F b m hm heven P ⟨a, cyclicGenerator_sq_mem_splitTorus F b m hm heven⟩ :
        ℂ) ^ k) ∧
    (∀ P (k : ℤ) (t : F), t ≠ 0 →
      Ψ P (a ^ k * specialInclusion F b m hm heven (upperSL F t)) =
        (torusCharacter F b m hm heven P ⟨a, cyclicGenerator_sq_mem_splitTorus F b m hm heven⟩ :
          ℂ) ^ k) ∧
    (∀ P g (hg : g ∈ T), g ∉ Subgroup.zpowers a →
      Ψ P g = (torusCharacter F b m hm heven P ⟨g, hg⟩ : ℂ) +
        (torusCharacter F b m hm heven P
          ⟨w⁻¹ * g * w, weyl_conj_mem_splitTorus F b m hm heven hg⟩ : ℂ)) ∧
    (∀ P g, (∀ q : Omega F, g • q ≠ q) → Ψ P g = 0) ∧
    (∀ P, Ψ P x = ((Nat.card F : ℂ) + 1) * (P.1.1 (-1) : ℂ)) := by
  intro G B T U u h w v a x c₀ St Ψ
  refine ⟨centralExtension_projective F b m hm heven, fun c => ⟨rfl, rfl⟩, rfl, rfl, rfl,
    cyclicGenerator_pow_m F b m hm heven, ?_, fun t => rfl, rfl, rfl,
    unipotentSubgroup_le_borel F b m hm heven, splitTorus_le_borel F b m hm heven,
    unipotentSubgroup_inf_splitTorus F b m hm heven, ?_,
    unipotentSubgroup_normal_in_borel F b m hm heven,
    fun s hs t ht => splitTorus_mul_comm F b m hm heven hs ht, card_splitTorus F b m hm heven,
    torusDiag_mul F b m hm heven, torusDiag_injective F b m hm heven,
    splitTorus_eq_closure F b m hm heven, torusGenerator_mul_torusDiag F b m hm heven,
    torusGenerator_pow_m F b m hm heven, rfl,
    fun K _ η z hcomm hz => splitTorus_lift F b m hm heven η z hcomm hz, ?_, ?_,
    borelProjection_surjective F b m hm heven, ?_, ?_, fun P => rfl,
    weylParameter_fst F b m heven, weylParameter_involutive F b m heven,
    principalSeries_inner_parameter F b m hm heven, weylParameter_eq_self_iff F b m heven hb,
    fun P hP => ⟨principalSeries_mem_blocksIrr F b m hm heven hb P hP,
      principalSeries_one F b m hm heven _⟩,
    fun P Q hP hQ => principalSeries_eq_iff F b m hm heven hb hP hQ,
    principalSeries_ncard F b m hm heven hb, ?_,
    fun P => principalSeries_cyclicGenerator_sq_zpow F b m hm heven _,
    fun P k t ht => principalSeries_unipotent F b m hm heven _ k ht,
    fun P g hg hga => principalSeries_splitTorus F b m hm heven hb _ hg hga,
    fun P g hg => principalSeries_eq_zero F b m hm heven _ hg,
    principalSeries_x F b m hm heven⟩
  · intro g
    rw [mem_unipotentSubgroup_iff]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩
  · intro g hg
    obtain ⟨β, hβ⟩ := borel_decomposition F b m hm heven g hg
    exact ⟨unipotentElement F b m hm heven β,
      (mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨β, rfl⟩, _, hβ,
      (mul_inv_cancel_left _ _).symm⟩
  · intro g hg
    obtain ⟨c, k, hck⟩ := splitTorus_normalForm F b m hm heven g hg
    refine ⟨(c, k), hck, ?_⟩
    rintro ⟨c', k'⟩ hck'
    obtain ⟨h1, h2⟩ := splitTorus_normalForm_unique F b m hm heven (hck'.symm.trans hck)
    exact Prod.ext h1 h2
  · intro P
    exact ⟨torusCharacter_torusDiag F b m hm heven P,
      torusCharacter_torusGenerator F b m hm heven P,
      fun φ h1 h2 => splitTorusCharacter_unique F b m hm heven P.1.1 P.1.2 P.2 φ h1 h2⟩
  · intro g
    constructor
    · intro hg1
      have h1 : borelProjectionFun F b m hm heven g = 1 := congrArg Subtype.val hg1
      rw [← unipotentElement_mul_borelProjectionFun F b m hm heven g, h1, mul_one]
      exact (mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨_, rfl⟩
    · intro hg
      exact borelProjection_of_mem_unipotent F b m hm heven g hg
  · intro g t hgt
    exact borelProjection_eq F b m hm heven g hgt t.2 (inv_mul_cancel_right _ _).symm
  · intro ζ hζ r P hP1 hP2 χ
    refine ⟨fun X j => rootCharacter_baseResidue_quotientClass F b m hm heven ζ hζ r.val X j,
      principalSeries_trivial F b m hm heven ζ hζ r P hP1 hP2,
      monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp
        ((rootCharacter m hm ζ hζ r.val).comp (baseResidue F b m hm heven))),
      linearTwist_mem_blocksIrr ((rootCharacter m hm ζ hζ r.val).comp
        (baseResidue F b m hm heven)) (steinberg_mem_blocksIrr F b m hm heven), ?_, ?_⟩
    · simp [χ]
    · have h1 : χ 1 = 1 := by simp [χ]
      rw [h1, one_mul]
      change fixedPointCount G (Omega F) 1 - 1 = _
      rw [fixedPointCount_one]
      ring

end CFSG.Wreathed.CentralSL2
