module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.CuspidalCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Types

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E]

theorem classFunction_isConj {K : Type} [Group K] {f : K → ℂ} (hf : BlocksIsClassFunction f)
    {x y : K} (h : IsConj x y) : f x = f y := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact (hf x c).symm

theorem eq_of_eq_on_types (basis : Module.Basis (Fin 2) F E) (hb : ¬ IsSquare b)
    {f g : CentralExtension F b m hm heven → ℂ}
    (hf : BlocksIsClassFunction f) (hg : BlocksIsClassFunction g)
    (h1 : ∀ α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2), f α = g α)
    (h2 : ∀ α ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2),
      f (α * unipotentElement F b m hm heven 1) = g (α * unipotentElement F b m hm heven 1))
    (h3 : ∀ t ∈ splitTorus F b m hm heven,
      t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) → f t = g t)
    (h4 : ∀ t ∈ nonsplitTorus F b m hm heven E basis,
      t ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) → f t = g t) : f = g := by
  funext x
  rcases conjugacy_type_exists basis hb x with hx | ⟨α, hα, hc⟩ | ⟨t, ht, htA, hc⟩ |
      ⟨t, ht, htA, hc⟩
  · exact h1 x hx
  · rw [classFunction_isConj hf hc, classFunction_isConj hg hc]
    exact h2 α hα
  · rw [classFunction_isConj hf hc, classFunction_isConj hg hc]
    exact h3 t ht htA
  · rw [classFunction_isConj hf hc, classFunction_isConj hg hc]
    exact h4 t ht htA

end Types

section Parameters

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

theorem minusWeyl_fixed_iff (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b)
    (P : NonsplitParameter F E b m h2 z hz) :
    (nonsplitCharacter F b m hm heven E basis h2 z hz P).comp (minusWeylConj h2 y hy) =
        nonsplitCharacter F b m hm heven E basis h2 z hz P ↔ P.1.1 = 1 := by
  have hinj : Function.Injective (nonsplitCharacter F b m hm heven E basis h2 z hz) :=
    (nonsplitCharacterEquiv F b m hm heven E basis h2 z hz).injective
  rw [minusWeylConj_eq h2 z hz y hy, nonsplitCharacter_comp_weylConj, hinj.eq_iff,
    nonsplitWeylParameter_eq_self_iff F b m heven E basis h2 z hz hb]

theorem ncard_minusWeyl_nonfixed (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0) :
    Set.ncard {lam : nonsplitTorus F b m hm heven E basis →* ℂˣ |
      lam.comp (minusWeylConj h2 y hy) ≠ lam} = m * Nat.card F := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  set e := nonsplitCharacterEquiv F b m hm heven E basis h2 z hz with he
  have hset : {lam : nonsplitTorus F b m hm heven E basis →* ℂˣ |
      lam.comp (minusWeylConj h2 y hy) ≠ lam} =
        e '' {P : NonsplitParameter F E b m h2 z hz | P.1.1 ≠ 1} := by
    ext lam
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hlam
      refine ⟨e.symm lam, fun h => hlam ?_, e.apply_symm_apply lam⟩
      have h' := (minusWeyl_fixed_iff (hm := hm) (heven := heven) (basis := basis) hb y hy h2 z hz
        (e.symm lam)).mpr h
      rw [show nonsplitCharacter F b m hm heven E basis h2 z hz (e.symm lam) = e (e.symm lam)
        from rfl, e.apply_symm_apply] at h'
      exact h'
    · rintro ⟨P, hP, rfl⟩ h
      exact hP ((minusWeyl_fixed_iff (hm := hm) (heven := heven) (basis := basis) hb y hy h2 z hz
        P).mp h)
  rw [hset, Set.ncard_image_of_injective _ e.injective,
    (nonsplitParameter_orbits F b m hm heven E basis h2 z hz hb).1]

theorem finite_nonsplitTorus_characters (h2 : (2 : F) ≠ 0) :
    Finite (nonsplitTorus F b m hm heven E basis →* ℂˣ) := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  apply Nat.finite_of_card_ne_zero
  rw [card_nonsplitTorus_characters F b m hm heven E basis h2 z hz]
  exact Nat.mul_ne_zero hm.ne' (by omega)

end Parameters

section Irreducible

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

theorem cuspidalCharacter_mem_blocksVChar (hb : ¬ IsSquare b) (ψ : AddChar F ℂ)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    cuspidalCharacter hb ψ lam ∈ BlocksVChar (CentralExtension F b m hm heven) :=
  sub_mem (inducedFunction_mem_blocksVChar _ (auCharacter hb (restrictA hb lam) ψ))
    (inducedFunction_mem_blocksVChar _ ((Units.coeHom ℂ).comp lam))

theorem cuspidalCharacter_one (hb : ¬ IsSquare b) (ψ : AddChar F ℂ)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    cuspidalCharacter hb ψ lam 1 = (Nat.card F : ℂ) - 1 := by
  have h := cuspidalCharacter_central hb ψ lam 1
  rw [map_one, Units.val_one, mul_one, OneMemClass.coe_one] at h
  exact h

theorem minusWeylConj_involutive (h2 : (2 : F) ≠ 0) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (t : nonsplitTorus F b m hm heven E basis) :
    minusWeylConj h2 y hy (minusWeylConj h2 y hy t) = t := by
  apply Subtype.ext
  rw [minusWeylConj_apply, minusWeylConj_apply,
    nonsplitWeyl_inv_conj y hy h2 (t : CentralExtension F b m hm heven)]
  group

theorem comp_minusWeylConj_involutive (h2 : (2 : F) ≠ 0) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    (lam.comp (minusWeylConj h2 y hy)).comp (minusWeylConj h2 y hy) = lam :=
  MonoidHom.ext fun t => by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, minusWeylConj_involutive]

variable {p : ℕ} (hpodd : Odd p) [CharP F p] (hb : ¬ IsSquare b) (y : Eˣ)
  (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
include hpodd hψ

theorem cuspidalCharacter_mem_blocksIrr (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ)
    (hlam : lam.comp (minusWeylConj h2 y hy) ≠ lam) :
    cuspidalCharacter hb ψ lam ∈ BlocksIrr (CentralExtension F b m hm heven) := by
  apply mem_blocksIrr_of_virtual_norm_one (cuspidalCharacter_mem_blocksVChar hb ψ lam)
  · rw [inner_cuspidal hpodd hb y hy h2 hψ, ite_eq_left rfl, ite_eq_right (Ne.symm hlam),
      add_zero]
  · rw [cuspidalCharacter_one, Complex.sub_re, Complex.natCast_re, Complex.one_re]
    have hq : (2 : ℝ) ≤ Nat.card F := by exact_mod_cast two_le_card F
    linarith

theorem cuspidalCharacter_weyl (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    cuspidalCharacter hb ψ (lam.comp (minusWeylConj h2 y hy)) = cuspidalCharacter hb ψ lam := by
  by_cases hfix : lam.comp (minusWeylConj h2 y hy) = lam
  · rw [hfix]
  have hfix' : (lam.comp (minusWeylConj h2 y hy)).comp (minusWeylConj h2 y hy) ≠
      lam.comp (minusWeylConj h2 y hy) := by
    rw [comp_minusWeylConj_involutive]
    exact fun h => hfix h.symm
  have hirr1 := cuspidalCharacter_mem_blocksIrr hpodd hb y hy h2 hψ lam hfix
  have hirr2 := cuspidalCharacter_mem_blocksIrr hpodd hb y hy h2 hψ _ hfix'
  have h1 := inner_cuspidal hpodd hb y hy h2 hψ (lam.comp (minusWeylConj h2 y hy)) lam
  rw [ite_eq_right hfix, ite_eq_left rfl, zero_add] at h1
  have h3 := blocksInnerProduct_irreducible ⟨_, hirr2⟩ ⟨_, hirr1⟩
  change BlocksInnerProduct (cuspidalCharacter hb ψ (lam.comp (minusWeylConj h2 y hy)))
    (cuspidalCharacter hb ψ lam) = _ at h3
  rw [h1] at h3
  by_contra hne
  rw [ite_eq_right (fun h => hne (congrArg Subtype.val h))] at h3
  exact one_ne_zero h3

theorem cuspidalCharacter_eq_iff {lam μ : nonsplitTorus F b m hm heven E basis →* ℂˣ}
    (hlam : lam.comp (minusWeylConj h2 y hy) ≠ lam) :
    cuspidalCharacter hb ψ lam = cuspidalCharacter hb ψ μ ↔
      μ = lam ∨ μ = lam.comp (minusWeylConj h2 y hy) := by
  constructor
  · intro h
    have h1 := inner_cuspidal hpodd hb y hy h2 hψ lam μ
    rw [← h, inner_cuspidal hpodd hb y hy h2 hψ lam lam, ite_eq_left rfl,
      ite_eq_right (Ne.symm hlam), add_zero] at h1
    by_cases h3 : lam = μ
    · exact Or.inl h3.symm
    · by_cases h4 : lam = μ.comp (minusWeylConj h2 y hy)
      · right
        rw [h4, comp_minusWeylConj_involutive]
      · rw [ite_eq_right h3, ite_eq_right h4] at h1
        norm_num at h1
  · rintro (rfl | rfl)
    · rfl
    · exact (cuspidalCharacter_weyl hpodd hb y hy h2 hψ lam).symm

theorem cuspidalCharacter_ncard :
    Set.ncard ((fun lam => cuspidalCharacter hb ψ lam) ''
      {lam : nonsplitTorus F b m hm heven E basis →* ℂˣ |
        lam.comp (minusWeylConj h2 y hy) ≠ lam}) = m * Nat.card F / 2 := by
  have := finite_nonsplitTorus_characters h2 (b := b) (hm := hm) (heven := heven) (basis := basis)
  have h := two_mul_ncard_image_of_pairs (fun lam => cuspidalCharacter hb ψ lam)
    (fun lam => lam.comp (minusWeylConj h2 y hy))
    {lam : nonsplitTorus F b m hm heven E basis →* ℂˣ | lam.comp (minusWeylConj h2 y hy) ≠ lam}
    ?_ ?_
  · rw [ncard_minusWeyl_nonfixed hb y hy h2] at h
    omega
  · intro lam hlam
    refine ⟨?_, hlam⟩
    show (lam.comp (minusWeylConj h2 y hy)).comp (minusWeylConj h2 y hy) ≠
      lam.comp (minusWeylConj h2 y hy)
    rw [comp_minusWeylConj_involutive]
    exact fun h => hlam h.symm
  · intro lam hlam μ _
    exact cuspidalCharacter_eq_iff hpodd hb y hy h2 hψ hlam

theorem cuspidalCharacter_indep {ψ' : AddChar F ℂ} (hψ' : ψ' ≠ 1)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    cuspidalCharacter hb ψ lam = cuspidalCharacter hb ψ' lam := by
  have h2 := two_ne_zero_of_not_isSquare hb
  obtain ⟨y, hy⟩ : ∃ y : Eˣ, (y : E) * (y : E) ^ Nat.card F = -1 :=
    exists_norm_eq F E basis (-1) |>.imp fun y' hy' => by rw [hy']; simp
  apply eq_of_eq_on_types basis hb (cuspidalCharacter_classFunction hb ψ lam)
    (cuspidalCharacter_classFunction hb ψ' lam)
  · intro α hα
    exact (cuspidalCharacter_central hb ψ lam ⟨α, hα⟩).trans
      (cuspidalCharacter_central hb ψ' lam ⟨α, hα⟩).symm
  · intro α hα
    exact (cuspidalCharacter_unipotent hpodd hb hψ lam ⟨α, hα⟩ one_ne_zero).trans
      (cuspidalCharacter_unipotent hpodd hb hψ' lam ⟨α, hα⟩ one_ne_zero).symm
  · intro t ht htA
    rw [cuspidalCharacter_split hb ψ lam ht htA, cuspidalCharacter_split hb ψ' lam ht htA]
  · intro t ht htA
    exact (cuspidalCharacter_nonsplit hb y hy h2 ψ lam (t := ⟨t, ht⟩) htA).trans
      (cuspidalCharacter_nonsplit hb y hy h2 ψ' lam (t := ⟨t, ht⟩) htA).symm

end Irreducible

section Involution

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

omit [Fintype F] in
theorem cyclicGenerator_pow_m_mem_zpowers :
    cyclicGenerator F b m hm heven ^ m ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  obtain ⟨k, hk⟩ := id heven
  refine ⟨k, ?_⟩
  simp only [zpow_natCast]
  rw [← pow_mul]
  congr 1
  omega

theorem cuspidalCharacter_x (hb : ¬ IsSquare b) (ψ : AddChar F ℂ)
    (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    cuspidalCharacter hb ψ lam (cyclicGenerator F b m hm heven ^ m) =
      ((Nat.card F : ℂ) - 1) *
        (lam ⟨cyclicGenerator F b m hm heven ^ m,
          zpowers_le_nonsplitTorus hb cyclicGenerator_pow_m_mem_zpowers⟩ : ℂ) :=
  cuspidalCharacter_central hb ψ lam ⟨_, cyclicGenerator_pow_m_mem_zpowers⟩

theorem exists_nonfixed_x_eq_neg_one (hb : ¬ IsSquare b) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) (h2 : (2 : F) ≠ 0) :
    ∃ lam : nonsplitTorus F b m hm heven E basis →* ℂˣ,
      lam.comp (minusWeylConj h2 y hy) ≠ lam ∧
        (lam ⟨cyclicGenerator F b m hm heven ^ m,
          zpowers_le_nonsplitTorus hb cyclicGenerator_pow_m_mem_zpowers⟩ : ℂ) = -1 := by
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  have := finite_of_basis F E basis
  have hne : negOneE F E h2 ≠ 1 := by
    intro h
    have hv : (((negOneE F E h2 : normOne F E) : Eˣ) : E) = -1 := by simp [negOneE]
    rw [h] at hv
    have h1 : (((1 : normOne F E) : Eˣ) : E) = 1 := rfl
    rw [h1] at hv
    have h2E : (2 : E) ≠ 0 := by
      rw [← map_ofNat (algebraMap F E) 2]
      exact (map_ne_zero _).mpr h2
    apply h2E
    linear_combination hv
  obtain ⟨ν, hν⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (normOne F E) ℂ hne
  have hν1 : ((ν (negOneE F E h2) : ℂˣ) : ℂ) = -1 := by
    have hsq : (ν (negOneE F E h2)) ^ 2 = 1 := by
      rw [← map_pow]
      have : negOneE F E h2 ^ 2 = 1 := by
        apply Subtype.ext
        apply Units.ext
        simp [negOneE]
      rw [this, map_one]
    have hsq' : ((ν (negOneE F E h2) : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
    rcases sq_eq_one_iff.mp hsq' with h1 | h1
    · exact absurd (Units.ext h1) hν
    · exact h1
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_pow_nat_eq ((ν (cMinus F E b m h2 z hz) : ℂˣ) : ℂ) hm
  have hζ0 : ζ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hζ₀
    exact Units.ne_zero _ hζ₀.symm
  let P : NonsplitParameter F E b m h2 z hz :=
    ⟨(ν, Units.mk0 ζ₀ hζ0), Units.ext (by simp [hζ₀])⟩
  refine ⟨nonsplitCharacter F b m hm heven E basis h2 z hz P, ?_, ?_⟩
  · intro h
    have h1 := (minusWeyl_fixed_iff hb y hy h2 z hz P).mp h
    apply hν
    change P.1.1 (negOneE F E h2) = 1
    rw [h1, MonoidHom.one_apply]
  · rw [nonsplitCharacter_x F b m hm heven E basis h2 z hz P]
    exact hν1

end Involution

section Fixed

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {E : Type} [Field E] [Algebra F E] {basis : Module.Basis (Fin 2) F E}

@[expose] noncomputable def linearCharacter (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (r : ℕ) : CentralExtension F b m hm heven →* ℂˣ :=
  (rootCharacter m hm ζ hζ r).comp (baseResidue F b m hm heven)

omit [Fintype F] in
theorem linearCharacter_apply (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : ℕ)
    (g : CentralExtension F b m hm heven) :
    linearCharacter (F := F) (b := b) (heven := heven) hm ζ hζ r g =
      rootCharacter m hm ζ hζ r (baseResidue F b m hm heven g) := rfl

omit [Fintype F] in
theorem linearCharacter_specialInclusion (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : ℕ)
    (X : SpecialLinearGroup (Fin 2) F) :
    linearCharacter (F := F) (b := b) (heven := heven) hm ζ hζ r
      (specialInclusion F b m hm heven X) = 1 := by
  rw [linearCharacter_apply, baseResidue_specialInclusion, map_one]

omit [Fintype F] in
theorem linearCharacter_unipotent (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : ℕ) (t : F) :
    linearCharacter (F := F) (b := b) (heven := heven) hm ζ hζ r
      (unipotentElement F b m hm heven t) = 1 :=
  linearCharacter_specialInclusion ζ hζ r _

theorem linearCharacter_nonsplitGenerator (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : ℕ) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) :
    (linearCharacter (F := F) (b := b) (heven := heven) hm ζ hζ r
      (nonsplitGenerator F b m hm heven E basis z hz) : ℂ) = ζ ^ r := by
  rw [linearCharacter_apply, baseResidue_nonsplitGenerator]
  have h := rootCharacter_natCast m hm ζ hζ r 1
  rw [Nat.cast_one, mul_one] at h
  exact h

@[expose] noncomputable def linearRestrict (hm : 0 < m) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (r : ℕ) : nonsplitTorus F b m hm heven E basis →* ℂˣ :=
  (linearCharacter hm ζ hζ r).comp (nonsplitTorus F b m hm heven E basis).subtype

omit [Fintype F] in
theorem linearRestrict_apply (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m) (r : ℕ)
    (t : nonsplitTorus F b m hm heven E basis) :
    linearRestrict hm ζ hζ r t = linearCharacter hm ζ hζ r (t : CentralExtension F b m hm heven) :=
  rfl

variable (hb : ¬ IsSquare b) (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1)
  (h2 : (2 : F) ≠ 0) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)

theorem linearRestrict_fixed (r : ℕ) :
    (linearRestrict (b := b) (basis := basis) (heven := heven) hm ζ hζ r).comp
        (minusWeylConj h2 y hy) =
      linearRestrict hm ζ hζ r := by
  refine MonoidHom.ext fun t => ?_
  rw [MonoidHom.comp_apply]
  change linearCharacter hm ζ hζ r (minusWeylConj h2 y hy t : CentralExtension F b m hm heven) =
    linearCharacter hm ζ hζ r (t : CentralExtension F b m hm heven)
  rw [minusWeylConj_apply]
  have h := units_hom_conj (linearCharacter (F := F) (b := b) (heven := heven) hm ζ hζ r)
    (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ (t : CentralExtension F b m hm heven)
  rwa [inv_inv] at h

theorem linearRestrict_injective :
    Function.Injective fun r : Fin m =>
      linearRestrict (basis := basis) (heven := heven) (b := b) hm ζ hζ r.val := by
  intro r s h
  obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
  have h1 := congrArg (fun φ : nonsplitTorus F b m hm heven E basis →* ℂˣ =>
    (φ ⟨nonsplitGenerator F b m hm heven E basis z hz, nonsplitGenerator_mem z hz⟩ : ℂ)) h
  simp only at h1
  change (linearCharacter hm ζ hζ r.val (nonsplitGenerator F b m hm heven E basis z hz) : ℂ) =
    (linearCharacter hm ζ hζ s.val (nonsplitGenerator F b m hm heven E basis z hz) : ℂ) at h1
  rw [linearCharacter_nonsplitGenerator, linearCharacter_nonsplitGenerator] at h1
  exact Fin.ext (hζ.pow_inj r.2 s.2 h1)

include hb in
theorem minusWeyl_fixed_iff_linear (lam : nonsplitTorus F b m hm heven E basis →* ℂˣ) :
    lam.comp (minusWeylConj h2 y hy) = lam ↔ ∃ r : Fin m, lam = linearRestrict hm ζ hζ r.val := by
  constructor
  · intro hfix
    obtain ⟨z, hz⟩ := exists_norm_eq F E basis b
    set e := nonsplitCharacterEquiv F b m hm heven E basis h2 z hz with he
    set P := e.symm lam with hP
    have hlamP : nonsplitCharacter F b m hm heven E basis h2 z hz P = lam := e.apply_symm_apply lam
    have hP1 : P.1.1 = 1 := by
      rw [← minusWeyl_fixed_iff hb y hy h2 z hz P, hlamP]
      exact hfix
    have hP2 : (P.1.2 : ℂ) ^ m = 1 := by
      have h := P.2
      rw [hP1, MonoidHom.one_apply] at h
      rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
    have : NeZero m := ⟨hm.ne'⟩
    obtain ⟨i, hi, hζi⟩ := hζ.eq_pow_of_pow_eq_one hP2
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [← hlamP]
    symm
    apply nonsplitCharacter_unique
    · intro t
      rw [hP1, MonoidHom.one_apply]
      change linearCharacter hm ζ hζ i (nonsplitDiag F b m hm heven E basis t) = 1
      exact linearCharacter_specialInclusion ζ hζ i _
    · apply Units.ext
      change (linearCharacter hm ζ hζ i (nonsplitGenerator F b m hm heven E basis z hz) : ℂ) = _
      rw [linearCharacter_nonsplitGenerator, hζi]
  · rintro ⟨r, rfl⟩
    exact linearRestrict_fixed y hy h2 ζ hζ r.val

omit [Fintype F] in
theorem fixedPointCount_eq_card [Finite F] (g : CentralExtension F b m hm heven) :
    fixedPointCount (CentralExtension F b m hm heven) (Omega F) g =
      (Nat.card {p : Omega F // g • p = p} : ℂ) := rfl

theorem linearTwist_steinberg_classFunction (χ : CentralExtension F b m hm heven →* ℂˣ) :
    BlocksIsClassFunction fun g : CentralExtension F b m hm heven =>
      (χ g : ℂ) * (fixedPointCount (CentralExtension F b m hm heven) (Omega F) g - 1 - 1) := by
  intro g k
  simp only [fixedPointCount_eq_card]
  rw [units_hom_conj, card_fixed_conj (Ω := Omega F) k g]

include hb in
theorem cuspidalCharacter_linearRestrict {p : ℕ} (hpodd : Odd p) [CharP F p] {ψ : AddChar F ℂ}
    (hψ : ψ ≠ 1) (r : ℕ) :
    cuspidalCharacter hb ψ (linearRestrict (basis := basis) hm ζ hζ r) = fun g =>
      (linearCharacter hm ζ hζ r g : ℂ) *
        (fixedPointCount (CentralExtension F b m hm heven) (Omega F) g - 1 - 1) := by
  have hq : 2 ≤ Nat.card F := two_le_card F
  have h2 := two_ne_zero_of_not_isSquare hb
  obtain ⟨y, hy⟩ : ∃ y : Eˣ, (y : E) * (y : E) ^ Nat.card F = -1 :=
    exists_norm_eq F E basis (-1) |>.imp fun y' hy' => by rw [hy']; simp
  refine eq_of_eq_on_types basis hb (cuspidalCharacter_classFunction hb ψ _)
    (linearTwist_steinberg_classFunction _) ?_ ?_ ?_ ?_
  · intro α hα
    refine (cuspidalCharacter_central hb ψ _ ⟨α, hα⟩).trans ?_
    rw [fixedPointCount_eq_card, card_fixed_of_mem_zpowers hα]
    change ((Nat.card F : ℂ) - 1) * (linearCharacter hm ζ hζ r α : ℂ) = _
    push_cast
    ring
  · intro α hα
    refine (cuspidalCharacter_unipotent hpodd hb hψ _ ⟨α, hα⟩ one_ne_zero).trans ?_
    rw [fixedPointCount_eq_card, card_fixed_unipotent hα one_ne_zero, map_mul,
      linearCharacter_unipotent, mul_one]
    change -(linearCharacter hm ζ hζ r α : ℂ) = _
    push_cast
    ring
  · intro t ht htA
    rw [cuspidalCharacter_split hb ψ _ ht htA]
    rw [fixedPointCount_eq_card, card_fixed_splitTorus hb ht htA]
    push_cast
    ring
  · intro t ht htA
    refine (cuspidalCharacter_nonsplit hb y hy h2 ψ _ (t := ⟨t, ht⟩) htA).trans ?_
    rw [fixedPointCount_eq_card, card_fixed_nonsplitTorus hb ht htA]
    have hfix := linearRestrict_fixed (b := b) (basis := basis) (hm := hm) (heven := heven) y hy h2
      ζ hζ r
    have h3 : linearRestrict (b := b) (basis := basis) (heven := heven) hm ζ hζ r
        (minusWeylConj h2 y hy ⟨t, ht⟩) = linearRestrict hm ζ hζ r ⟨t, ht⟩ := by
      rw [← MonoidHom.comp_apply, hfix]
    rw [h3, linearRestrict_apply]
    push_cast
    ring

end Fixed

end CFSG.Wreathed.CentralSL2
