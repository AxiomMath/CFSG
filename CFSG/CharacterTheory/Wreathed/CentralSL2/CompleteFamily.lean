module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.CuspidalIrreducible
public import CFSG.CharacterTheory.OddOrderBasics.ClassAlgebra

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Completeness

variable {K : Type} [Group K]

theorem blocksIrr_one_eq_natCast {θ : K → ℂ} (hθ : θ ∈ BlocksIrr K) :
    ∃ d : ℕ, 0 < d ∧ θ 1 = d := by
  have hpos : 0 < (θ 1).re := blocksIrr_identity_re_pos ⟨θ, hθ⟩
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hθ
  refine ⟨Module.finrank ℂ V, ?_, Representation.char_one ρ⟩
  rw [Representation.char_one, Complex.natCast_re] at hpos
  exact_mod_cast hpos

theorem blocksIrr_eq_of_sum_sq [Fintype K] (s : Finset (K → ℂ))
    (hs : ∀ θ ∈ s, θ ∈ BlocksIrr K) (hsum : ∑ θ ∈ s, θ 1 ^ 2 = Nat.card K) :
    BlocksIrr K = ↑s := by
  have hI := (CFSG.OddOrderBasics.regular_character_degree_square_sum K).2
  set I := (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite K).toFinset with hIdef
  have hsub : s ⊆ I := fun θ hθ => (Set.Finite.mem_toFinset _).mpr (hs θ hθ)
  have hdiff : ∑ θ ∈ I \ s, θ 1 ^ 2 = 0 := by
    have h := Finset.sum_sdiff hsub (f := fun θ : K → ℂ => θ 1 ^ 2)
    rw [hI, hsum] at h
    linear_combination h
  have hempty : I \ s = ∅ := by
    by_contra hne
    obtain ⟨θ, hθ⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hdeg : ∀ χ ∈ I \ s, 0 < (χ 1 ^ 2).re := by
      intro χ hχ
      obtain ⟨d, hd, hχd⟩ := blocksIrr_one_eq_natCast
        ((Set.Finite.mem_toFinset _).mp (Finset.mem_sdiff.mp hχ).1)
      rw [hχd, ← Nat.cast_pow, Complex.natCast_re]
      exact_mod_cast pow_pos hd 2
    have hpos : 0 < (∑ χ ∈ I \ s, χ 1 ^ 2).re := by
      rw [Complex.re_sum]
      exact Finset.sum_pos (fun χ hχ => hdeg χ hχ) ⟨θ, hθ⟩
    rw [hdiff, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  ext θ
  constructor
  · intro hθ
    by_contra hθs
    have hmem : θ ∈ I \ s :=
      Finset.mem_sdiff.mpr ⟨(Set.Finite.mem_toFinset _).mpr hθ, hθs⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  · intro hθ
    exact hs θ hθ

theorem sum_sq_of_const {S : Set (K → ℂ)} (hS : S.Finite) {d : ℂ} (hd : ∀ θ ∈ S, θ 1 = d) :
    ∑ θ ∈ hS.toFinset, θ 1 ^ 2 = (S.ncard : ℂ) * d ^ 2 := by
  rw [Finset.sum_congr rfl fun θ hθ => by rw [hd θ ((Set.Finite.mem_toFinset hS).mp hθ)],
    Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card S hS]

theorem sum_sq_union {S T : Set (K → ℂ)} (hS : S.Finite) (hT : T.Finite) (hST : Disjoint S T) :
    ∑ θ ∈ (hS.union hT).toFinset, θ 1 ^ 2 =
      ∑ θ ∈ hS.toFinset, θ 1 ^ 2 + ∑ θ ∈ hT.toFinset, θ 1 ^ 2 := by
  rw [Set.Finite.toFinset_union hS hT, Finset.sum_union (Set.Finite.disjoint_toFinset.mpr hST)]

theorem disjoint_of_degree {S T : Set (K → ℂ)} {d e : ℂ} (hd : ∀ θ ∈ S, θ 1 = d)
    (he : ∀ θ ∈ T, θ 1 = e) (hde : d ≠ e) : Disjoint S T :=
  Set.disjoint_left.mpr fun θ hS hT => hde ((hd θ hS).symm.trans (he θ hT))

end Completeness

section SplitWeyl

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

omit [Fintype F] in
theorem weylConj_involutive (t : splitTorus F b m hm heven) :
    weylConj F b m hm heven (weylConj F b m hm heven t) = t := by
  apply Subtype.ext
  rw [weylConj_apply, weylConj_apply,
    weylElement_inv_conj F b m hm heven (t : CentralExtension F b m hm heven)]
  group

omit [Fintype F] in
theorem comp_weylConj_involutive (θ : splitTorus F b m hm heven →* ℂˣ) :
    (θ.comp (weylConj F b m hm heven)).comp (weylConj F b m hm heven) = θ :=
  MonoidHom.ext fun t => by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, weylConj_involutive]

theorem principalSeries_mem_blocksIrr' (θ : splitTorus F b m hm heven →* ℂˣ)
    (hθ : θ.comp (weylConj F b m hm heven) ≠ θ) :
    principalSeries F b m hm heven θ ∈ BlocksIrr (CentralExtension F b m hm heven) := by
  have hlin : (fun g : borelSubgroup F b m hm heven =>
      (borelInflation F b m hm heven θ g : ℂ)) ∈ BlocksIrr (borelSubgroup F b m hm heven) :=
    monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp (borelInflation F b m hm heven θ))
  obtain ⟨W, _, _, _, τ, hτ⟩ :=
    CFSG.Wreathed.exists_representation_inducedFunction (borelSubgroup F b m hm heven) hlin
  have hnorm : BlocksInnerProduct τ.character τ.character = 1 := by
    rw [hτ]
    change BlocksInnerProduct (principalSeries F b m hm heven θ)
      (principalSeries F b m hm heven θ) = 1
    rw [principalSeries_inner, ite_eq_left rfl, ite_eq_right (Ne.symm hθ), add_zero]
  have h := CFSG.Wreathed.mem_blocksIrr_of_norm_one τ hnorm
  rw [hτ] at h
  exact h

theorem principalSeries_weyl (θ : splitTorus F b m hm heven →* ℂˣ) :
    principalSeries F b m hm heven (θ.comp (weylConj F b m hm heven)) =
      principalSeries F b m hm heven θ := by
  by_cases hfix : θ.comp (weylConj F b m hm heven) = θ
  · rw [hfix]
  have hfix' : (θ.comp (weylConj F b m hm heven)).comp (weylConj F b m hm heven) ≠
      θ.comp (weylConj F b m hm heven) := by
    rw [comp_weylConj_involutive]
    exact fun h => hfix h.symm
  have hirr1 := principalSeries_mem_blocksIrr' θ hfix
  have hirr2 := principalSeries_mem_blocksIrr' _ hfix'
  have h1 := principalSeries_inner F b m hm heven (θ.comp (weylConj F b m hm heven)) θ
  rw [ite_eq_right hfix, ite_eq_left rfl, zero_add] at h1
  have h3 := blocksInnerProduct_irreducible ⟨_, hirr2⟩ ⟨_, hirr1⟩
  change BlocksInnerProduct (principalSeries F b m hm heven (θ.comp (weylConj F b m hm heven)))
    (principalSeries F b m hm heven θ) = _ at h3
  rw [h1] at h3
  by_contra hne
  rw [ite_eq_right (fun h => hne (congrArg Subtype.val h))] at h3
  exact one_ne_zero h3

theorem principalSeries_eq_iff' {θ θ' : splitTorus F b m hm heven →* ℂˣ}
    (hθ : θ.comp (weylConj F b m hm heven) ≠ θ) :
    principalSeries F b m hm heven θ = principalSeries F b m hm heven θ' ↔
      θ' = θ ∨ θ' = θ.comp (weylConj F b m hm heven) := by
  constructor
  · intro h
    have h1 := principalSeries_inner F b m hm heven θ θ'
    rw [← h, principalSeries_inner, ite_eq_left rfl, ite_eq_right (Ne.symm hθ), add_zero] at h1
    by_cases h3 : θ = θ'
    · exact Or.inl h3.symm
    · by_cases h4 : θ = θ'.comp (weylConj F b m hm heven)
      · right
        rw [h4, comp_weylConj_involutive]
      · rw [ite_eq_right h3, ite_eq_right h4] at h1
        norm_num at h1
  · rintro (rfl | rfl)
    · rfl
    · exact (principalSeries_weyl θ).symm

omit [Fintype F] in
theorem torusCharacter_surjective : Function.Surjective (torusCharacter F b m hm heven) := by
  intro θ
  let η : Fˣ →* ℂˣ := MonoidHom.mk'
    (fun c => θ ⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c⟩)
    (fun c d => by
      rw [← map_mul]
      congr 1
      exact Subtype.ext (torusDiag_mul F b m hm heven c d))
  let z : ℂˣ := θ ⟨torusGenerator F b m hm heven, torusGenerator_mem_splitTorus F b m hm heven⟩
  have hz : z ^ m = η (torusConstant F b m) := by
    change (θ ⟨torusGenerator F b m hm heven, _⟩) ^ m = θ ⟨torusDiag F b m hm heven _, _⟩
    rw [← map_pow]
    congr 1
    exact Subtype.ext (torusGenerator_pow_m F b m hm heven)
  exact ⟨⟨(η, z), hz⟩,
    (splitTorusCharacter_unique F b m hm heven η z hz θ (fun _ => rfl) rfl).symm⟩

theorem splitWeyl_fixed_iff (hb : ¬ IsSquare b) (P : PrincipalSeriesParameter F b m) :
    (torusCharacter F b m hm heven P).comp (weylConj F b m hm heven) =
        torusCharacter F b m hm heven P ↔ P.1.1 = 1 := by
  rw [torusCharacter_comp_weylConj, (torusCharacter_injective F b m hm heven).eq_iff,
    weylParameter_eq_self_iff F b m heven hb]

theorem splitWeyl_nonfixed_eq (hb : ¬ IsSquare b) :
    {θ : splitTorus F b m hm heven →* ℂˣ | θ.comp (weylConj F b m hm heven) ≠ θ} =
      torusCharacter F b m hm heven '' {P : PrincipalSeriesParameter F b m | P.1.1 ≠ 1} := by
  ext θ
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hθ
    obtain ⟨P, rfl⟩ := torusCharacter_surjective θ
    exact ⟨P, fun h => hθ ((splitWeyl_fixed_iff hb P).mpr h), rfl⟩
  · rintro ⟨P, hP, rfl⟩ h
    exact hP ((splitWeyl_fixed_iff hb P).mp h)

theorem principalSeries_ncard' (hb : ¬ IsSquare b) :
    Set.ncard ((fun θ => principalSeries F b m hm heven θ) ''
      {θ : splitTorus F b m hm heven →* ℂˣ | θ.comp (weylConj F b m hm heven) ≠ θ}) =
        m * (Nat.card F - 2) / 2 := by
  rw [splitWeyl_nonfixed_eq hb, Set.image_image]
  exact principalSeries_ncard F b m hm heven hb

theorem finite_splitTorus_characters :
    Finite (splitTorus F b m hm heven →* ℂˣ) := by
  have hcardP := card_principalSeriesParameter F b m hm
  have hfinP : Finite (PrincipalSeriesParameter F b m) := Nat.finite_of_card_ne_zero (by
    rw [hcardP]
    have : 2 ≤ Nat.card F := two_le_card F
    exact Nat.mul_ne_zero (by omega) hm.ne')
  exact Finite.of_surjective _ (torusCharacter_surjective (hm := hm) (heven := heven))

end SplitWeyl

section Linear

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

omit [Fintype F] in
theorem linearCharacter_cyclicGenerator (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : ℕ) :
    (linearCharacter (F := F) (b := b) (heven := heven) hm ζ hζ r
      (cyclicGenerator F b m hm heven) : ℂ) = ζ ^ r := by
  rw [linearCharacter_apply, cyclicGenerator, baseResidue_quotientClass, map_one]
  have h := rootCharacter_natCast m hm ζ hζ r 1
  rw [Nat.cast_one, mul_one] at h
  exact h

omit [Fintype F] in
theorem linearCharacter_torusGenerator (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : ℕ) :
    (linearCharacter (F := F) (b := b) (heven := heven) hm ζ hζ r
      (torusGenerator F b m hm heven) : ℂ) = ζ ^ r := by
  rw [linearCharacter_apply, baseResidue_torusGenerator]
  have h := rootCharacter_natCast m hm ζ hζ r 1
  rw [Nat.cast_one, mul_one] at h
  exact h

theorem steinberg_torusGenerator (hb : ¬ IsSquare b) :
    fixedPointCount (CentralExtension F b m hm heven) (Omega F)
      (torusGenerator F b m hm heven) - 1 = 1 := by
  rw [fixedPointCount_eq_card, card_fixed_splitTorus hb
    (torusGenerator_mem_splitTorus F b m hm heven) (torusGenerator_not_mem_zpowers hb)]
  norm_num

omit [Fintype F] in
theorem linearCharacter_injective (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
    Function.Injective fun (r : Fin m) (g : CentralExtension F b m hm heven) =>
      (linearCharacter hm ζ hζ r.val g : ℂ) := by
  intro r s h
  have h1 := congrFun h (cyclicGenerator F b m hm heven)
  simp only at h1
  rw [linearCharacter_cyclicGenerator, linearCharacter_cyclicGenerator] at h1
  exact Fin.ext (hζ.pow_inj r.2 s.2 h1)

theorem linearSteinberg_injective (hb : ¬ IsSquare b) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) :
    Function.Injective fun (r : Fin m) (g : CentralExtension F b m hm heven) =>
      (linearCharacter hm ζ hζ r.val g : ℂ) *
        (fixedPointCount (CentralExtension F b m hm heven) (Omega F) g - 1) := by
  intro r s h
  have h1 := congrFun h (torusGenerator F b m hm heven)
  simp only at h1
  rw [steinberg_torusGenerator hb, mul_one, mul_one, linearCharacter_torusGenerator,
    linearCharacter_torusGenerator] at h1
  exact Fin.ext (hζ.pow_inj r.2 s.2 h1)

end Linear

section Borel

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}

omit [Fintype F] in
theorem mem_borelSubgroup_iff_upper (g : CentralExtension F b m hm heven) :
    g ∈ borelSubgroup F b m hm heven ↔
      ∃ M : GL (Fin 2) F, (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        ProjGenLinGroup.mk M = projectiveMap F b m hm heven g := by
  rw [mem_borelSubgroup_iff]
  constructor
  · intro hg
    obtain ⟨M, hM⟩ := ProjGenLinGroup.mk_surjective (projectiveMap F b m hm heven g)
    refine ⟨M, ?_, hM⟩
    rw [smul_eq_coordinateGLAction hM.symm] at hg
    exact (coordinateGLAction_none_eq_none_iff M).mp hg
  · rintro ⟨M, hM1, hM⟩
    rw [smul_eq_coordinateGLAction hM.symm]
    exact (coordinateGLAction_none_eq_none_iff M).mpr hM1

@[expose] noncomputable def auProductHom :
    Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) × unipotentSubgroup F b m hm heven →*
      auSubgroup F b m hm heven where
  toFun pr := ⟨pr.1 * pr.2, (auSubgroup F b m hm heven).mul_mem (Subgroup.mem_sup_left pr.1.2)
    (Subgroup.mem_sup_right pr.2.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' pr pr' := Subtype.ext (by
    have hc := cyclicGenerator_sq_zpowers_comm pr'.1.2 (pr.2 : CentralExtension F b m hm heven)
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [mul_assoc, ← mul_assoc (pr'.1 : CentralExtension F b m hm heven), hc]
    simp only [mul_assoc])

omit [Fintype F] in
theorem auProductHom_bijective (hb : ¬ IsSquare b) :
    Function.Bijective (auProductHom (F := F) (b := b) (m := m) (hm := hm) (heven := heven)) := by
  constructor
  · rintro ⟨α, n⟩ ⟨α', n'⟩ h
    have h' : (α : CentralExtension F b m hm heven) * n = α' * n' := congrArg Subtype.val h
    obtain ⟨t, ht⟩ := (mem_unipotentSubgroup_iff F b m hm heven n).mp n.2
    obtain ⟨t', ht'⟩ := (mem_unipotentSubgroup_iff F b m hm heven n').mp n'.2
    rw [← ht, ← ht'] at h'
    obtain ⟨h1, h2⟩ := alpha_unipotent_injective α.2 α'.2 h'
    refine Prod.ext (Subtype.ext h1) (Subtype.ext ?_)
    rw [← ht, ← ht', h2]
  · rintro ⟨g, hg⟩
    obtain ⟨α, hα, t, rfl⟩ := (mem_auSubgroup_iff hb g).mp hg
    exact ⟨(⟨α, hα⟩, ⟨unipotentElement F b m hm heven t,
      (mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨t, rfl⟩⟩), rfl⟩

end Borel

section Families

theorem degree_square_sum_identity (m q : ℕ) (heven : Even m) (hq : 3 ≤ q) :
    m * 1 ^ 2 + m * q ^ 2 + m * (q - 2) / 2 * (q + 1) ^ 2 + m * q / 2 * (q - 1) ^ 2 =
      m * q * (q ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := heven
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 := ⟨q - 3, by omega⟩
  have e1 : (k + k) * (r + 3 - 2) / 2 = k * (r + 1) := by
    rw [show (k + k) * (r + 3 - 2) = 2 * (k * (r + 1)) by
      rw [show r + 3 - 2 = r + 1 by omega]
      ring]
    exact Nat.mul_div_cancel_left _ two_pos
  have e2 : (k + k) * (r + 3) / 2 = k * (r + 3) := by
    rw [show (k + k) * (r + 3) = 2 * (k * (r + 3)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [e1, e2, show r + 3 - 1 = r + 2 by omega,
    show (r + 3) ^ 2 - 1 = r ^ 2 + 6 * r + 8 from Nat.sub_eq_of_eq_add (by ring)]
  ring

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

omit [Fintype F] in
theorem three_le_card [Finite F] (hb : ¬ IsSquare b) : 3 ≤ Nat.card F := by
  have : Fintype F := Fintype.ofFinite F
  have h2 := two_ne_zero_of_not_isSquare hb
  obtain ⟨k, hk⟩ := odd_card F h2
  have hq := two_le_card F
  omega

variable {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b) (y : Eˣ)
  (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
  (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)

@[expose] noncomputable def linearFamily : Set (CentralExtension F b m hm heven → ℂ) :=
  Set.range fun (r : Fin m) (g : CentralExtension F b m hm heven) =>
    (linearCharacter hm ζ hζ r.val g : ℂ)

@[expose] noncomputable def steinbergFamily : Set (CentralExtension F b m hm heven → ℂ) :=
  Set.range fun (r : Fin m) (g : CentralExtension F b m hm heven) =>
    (linearCharacter hm ζ hζ r.val g : ℂ) *
      (fixedPointCount (CentralExtension F b m hm heven) (Omega F) g - 1)

@[expose] noncomputable def principalFamily : Set (CentralExtension F b m hm heven → ℂ) :=
  (fun θ => principalSeries F b m hm heven θ) ''
    {θ : splitTorus F b m hm heven →* ℂˣ | θ.comp (weylConj F b m hm heven) ≠ θ}

@[expose] noncomputable def cuspidalFamily : Set (CentralExtension F b m hm heven → ℂ) :=
  (fun lam => cuspidalCharacter hb ψ lam) ''
    {lam : nonsplitTorus F b m hm heven E basis →* ℂˣ | lam.comp (minusWeylConj h2 y hy) ≠ lam}

omit [Fintype F] in
theorem linearFamily_degree :
    ∀ θ ∈ linearFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ, θ 1 = 1 := by
  rintro θ ⟨r, rfl⟩
  simp

theorem steinbergFamily_degree :
    ∀ θ ∈ steinbergFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ,
      θ 1 = Nat.card F := by
  rintro θ ⟨r, rfl⟩
  simp only [map_one, Units.val_one, one_mul]
  rw [fixedPointCount_one]
  ring

theorem principalFamily_degree :
    ∀ θ ∈ principalFamily (F := F) (b := b) (heven := heven) (hm := hm), θ 1 = Nat.card F + 1 := by
  rintro θ ⟨φ, -, rfl⟩
  exact principalSeries_one F b m hm heven φ

theorem cuspidalFamily_degree :
    ∀ θ ∈ cuspidalFamily (basis := basis) (hm := hm) (heven := heven) hb y hy h2 (ψ := ψ),
      θ 1 = Nat.card F - 1 := by
  rintro θ ⟨lam, -, rfl⟩
  exact cuspidalCharacter_one hb ψ lam

omit [Fintype F] in
theorem linearFamily_ncard :
    Set.ncard (linearFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ) = m := by
  rw [linearFamily, Set.ncard_range_of_injective (linearCharacter_injective ζ hζ), Nat.card_fin]

include hb in
theorem steinbergFamily_ncard :
    Set.ncard (steinbergFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ) = m := by
  rw [steinbergFamily, Set.ncard_range_of_injective (linearSteinberg_injective hb ζ hζ),
    Nat.card_fin]

include hpodd hψ

theorem blocksIrr_eq_families :
    BlocksIrr (CentralExtension F b m hm heven) =
      linearFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ ∪
        steinbergFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ ∪
        principalFamily (F := F) (b := b) (heven := heven) (hm := hm) ∪
        cuspidalFamily (basis := basis) (hm := hm) (heven := heven) hb y hy h2 (ψ := ψ) ∧
    Disjoint (linearFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ)
      (steinbergFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ) ∧
    Disjoint (linearFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ)
      (principalFamily (F := F) (b := b) (heven := heven) (hm := hm)) ∧
    Disjoint (linearFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ)
      (cuspidalFamily (basis := basis) (hm := hm) (heven := heven) hb y hy h2 (ψ := ψ)) ∧
    Disjoint (steinbergFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ)
      (principalFamily (F := F) (b := b) (heven := heven) (hm := hm)) ∧
    Disjoint (steinbergFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ)
      (cuspidalFamily (basis := basis) (hm := hm) (heven := heven) hb y hy h2 (ψ := ψ)) ∧
    Disjoint (principalFamily (F := F) (b := b) (heven := heven) (hm := hm))
      (cuspidalFamily (basis := basis) (hm := hm) (heven := heven) hb y hy h2 (ψ := ψ)) := by
  set F1 := linearFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ with hF1
  set F2 := steinbergFamily (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ with hF2
  set F3 := principalFamily (F := F) (b := b) (heven := heven) (hm := hm) with hF3
  set F4 := cuspidalFamily (basis := basis) (hm := hm) (heven := heven) hb y hy h2 (ψ := ψ) with hF4
  have hq3 := three_le_card (F := F) hb
  have hne : ∀ a c : ℕ, a ≠ c → (a : ℂ) ≠ c := fun a c h => by exact_mod_cast h
  have h12 : (1 : ℂ) ≠ Nat.card F := by
    have := hne 1 (Nat.card F) (by omega)
    rwa [Nat.cast_one] at this
  have h13 : (1 : ℂ) ≠ Nat.card F + 1 := by
    have := hne 1 (Nat.card F + 1) (by omega)
    rwa [Nat.cast_one, Nat.cast_add_one] at this
  have h14 : (1 : ℂ) ≠ Nat.card F - 1 := by
    have := hne 2 (Nat.card F) (by omega)
    intro h
    apply this
    push_cast
    linear_combination h
  have h23 : (Nat.card F : ℂ) ≠ Nat.card F + 1 := by
    intro h
    have : (0 : ℂ) = 1 := by linear_combination h
    exact zero_ne_one this
  have h24 : (Nat.card F : ℂ) ≠ Nat.card F - 1 := by
    intro h
    have : (0 : ℂ) = -1 := by linear_combination h
    norm_num at this
  have h34 : (Nat.card F : ℂ) + 1 ≠ Nat.card F - 1 := by
    intro h
    have : (2 : ℂ) = 0 := by linear_combination h
    norm_num at this
  have d1 := linearFamily_degree (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ
  have d2 := steinbergFamily_degree (F := F) (b := b) (heven := heven) (hm := hm) ζ hζ
  have d3 := principalFamily_degree (F := F) (b := b) (heven := heven) (hm := hm)
  have d4 := cuspidalFamily_degree (basis := basis) (hm := hm) (heven := heven) hb y hy h2
    (ψ := ψ)
  have D12 := disjoint_of_degree d1 d2 h12
  have D13 := disjoint_of_degree d1 d3 h13
  have D14 := disjoint_of_degree d1 d4 h14
  have D23 := disjoint_of_degree d2 d3 h23
  have D24 := disjoint_of_degree d2 d4 h24
  have D34 := disjoint_of_degree d3 d4 h34
  refine ⟨?_, D12, D13, D14, D23, D24, D34⟩
  have hfin1 : F1.Finite := Set.finite_range _
  have hfin2 : F2.Finite := Set.finite_range _
  have := finite_splitTorus_characters (F := F) (b := b) (hm := hm) (heven := heven)
  have := finite_nonsplitTorus_characters h2 (b := b) (hm := hm) (heven := heven) (basis := basis)
  have hfin3 : F3.Finite := Set.Finite.image _ (Set.toFinite _)
  have hfin4 : F4.Finite := Set.Finite.image _ (Set.toFinite _)
  set hfin := ((hfin1.union hfin2).union hfin3).union hfin4 with hfindef
  have hcoe : (hfin.toFinset : Set (CentralExtension F b m hm heven → ℂ)) = F1 ∪ F2 ∪ F3 ∪ F4 :=
    Set.Finite.coe_toFinset hfin
  rw [← hcoe]
  apply blocksIrr_eq_of_sum_sq
  · intro θ hθ
    rw [Set.Finite.mem_toFinset] at hθ
    rcases hθ with ((hθ | hθ) | hθ) | hθ
    · obtain ⟨r, rfl⟩ := hθ
      exact monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp (linearCharacter hm ζ hζ r.val))
    · obtain ⟨r, rfl⟩ := hθ
      exact linearTwist_mem_blocksIrr (linearCharacter hm ζ hζ r.val)
        (steinberg_mem_blocksIrr F b m hm heven)
    · obtain ⟨φ, hφ, rfl⟩ := hθ
      exact principalSeries_mem_blocksIrr' φ hφ
    · obtain ⟨lam, hlam, rfl⟩ := hθ
      exact cuspidalCharacter_mem_blocksIrr hpodd hb y hy h2 hψ lam hlam
  · rw [sum_sq_union ((hfin1.union hfin2).union hfin3) hfin4 (Set.disjoint_union_left.mpr
        ⟨Set.disjoint_union_left.mpr ⟨D14, D24⟩, D34⟩),
      sum_sq_union (hfin1.union hfin2) hfin3 (Set.disjoint_union_left.mpr ⟨D13, D23⟩),
      sum_sq_union hfin1 hfin2 D12, sum_sq_of_const hfin1 d1, sum_sq_of_const hfin2 d2,
      sum_sq_of_const hfin3 d3, sum_sq_of_const hfin4 d4,
      linearFamily_ncard ζ hζ, steinbergFamily_ncard hb ζ hζ, hF3, principalFamily,
      principalSeries_ncard' hb, hF4, cuspidalFamily, cuspidalCharacter_ncard hpodd hb y hy h2 hψ,
      card_centralExtension_eq, ← degree_square_sum_identity m (Nat.card F) heven hq3]
    have h1 : 1 ≤ Nat.card F := by omega
    push_cast [Nat.cast_sub h1]
    ring

end Families

end CFSG.Wreathed.CentralSL2
