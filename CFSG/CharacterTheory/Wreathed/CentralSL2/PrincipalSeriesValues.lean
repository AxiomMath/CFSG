module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.BaseBorel
public import CFSG.CharacterTheory.Wreathed.CentralSL2.InducedStabilizer

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Parameters

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ)

abbrev PrincipalSeriesParameter : Type :=
  {P : (Fˣ →* ℂˣ) × ℂˣ // P.2 ^ m = P.1 (torusConstant F b m)}

theorem torusConstant_sq_mul (heven : Even m) : torusConstant F b m ^ 2 * b ^ m = 1 := by
  rw [torusConstant, neg_sq, ← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp heven),
    ← mul_pow, neg_mul, inv_mul_cancel, heven.neg_one_pow]

theorem weylParameter_spec (heven : Even m) (P : PrincipalSeriesParameter F b m) :
    (P.1.1 b * P.1.2) ^ m = P.1.1⁻¹ (torusConstant F b m) := by
  rw [mul_pow, P.2, ← map_pow, ← map_mul, MonoidHom.inv_apply, ← map_inv]
  congr 1
  rw [eq_inv_iff_mul_eq_one, mul_assoc, ← pow_two, mul_comm, torusConstant_sq_mul F b m heven]

@[expose] noncomputable def weylParameter (heven : Even m) (P : PrincipalSeriesParameter F b m) :
    PrincipalSeriesParameter F b m :=
  ⟨(P.1.1⁻¹, P.1.1 b * P.1.2), weylParameter_spec F b m heven P⟩

theorem weylParameter_fst (heven : Even m) (P : PrincipalSeriesParameter F b m) :
    (weylParameter F b m heven P).1 = (P.1.1⁻¹, P.1.1 b * P.1.2) := rfl

theorem weylParameter_involutive (heven : Even m) :
    Function.Involutive (weylParameter F b m heven) := by
  intro P
  apply Subtype.ext
  refine Prod.ext (MonoidHom.ext fun x => ?_) ?_
  · change ((P.1.1 x)⁻¹)⁻¹ = P.1.1 x
    exact inv_inv _
  · change (P.1.1 b)⁻¹ * (P.1.1 b * P.1.2) = P.1.2
    exact inv_mul_cancel_left _ _

theorem weylParameter_eq_self_iff [Finite F] (heven : Even m) (hb : ¬ IsSquare b)
    (P : PrincipalSeriesParameter F b m) : weylParameter F b m heven P = P ↔ P.1.1 = 1 := by
  constructor
  · intro h
    have h1 : P.1.1⁻¹ = P.1.1 := congrArg (fun Q : PrincipalSeriesParameter F b m => Q.1.1) h
    have h2 : P.1.1 b * P.1.2 = P.1.2 :=
      congrArg (fun Q : PrincipalSeriesParameter F b m => Q.1.2) h
    have hηb : P.1.1 b = 1 := mul_eq_right.mp h2
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := Fˣ)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ b)
    have hodd : Odd k := by
      by_contra hev
      rw [Int.not_odd_iff_even] at hev
      obtain ⟨j, hj⟩ := hev
      exact hb ⟨g₀ ^ j, by rw [← hk, hj, _root_.zpow_add]⟩
    have hsq : P.1.1 g₀ * P.1.1 g₀ = 1 := by
      have h3 := congrArg (fun χ : Fˣ →* ℂˣ => χ g₀) h1
      simp only [MonoidHom.inv_apply] at h3
      calc P.1.1 g₀ * P.1.1 g₀ = (P.1.1 g₀)⁻¹ * P.1.1 g₀ := by rw [h3]
        _ = 1 := inv_mul_cancel _
    have hg : P.1.1 g₀ = 1 := by
      obtain ⟨j, hj⟩ := hodd
      have h4 : P.1.1 (g₀ ^ k) = P.1.1 g₀ ^ k := map_zpow _ _ _
      rw [hk, hηb, hj, _root_.zpow_add, _root_.zpow_mul, zpow_one, zpow_two, hsq,
        _root_.one_zpow, one_mul] at h4
      exact h4.symm
    refine MonoidHom.ext fun x => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ x)
    rw [map_zpow, hg, _root_.one_zpow, MonoidHom.one_apply]
  · intro h
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · refine MonoidHom.ext fun x => ?_
      change (P.1.1 x)⁻¹ = P.1.1 x
      simp [h]
    · change P.1.1 b * P.1.2 = P.1.2
      simp [h]

end Parameters

section TorusCharacters

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

@[expose] noncomputable def torusCharacter (P : PrincipalSeriesParameter F b m) :
    splitTorus F b m hm heven →* ℂˣ :=
  splitTorusCharacter F b m hm heven P.1.1 P.1.2 P.2

theorem torusCharacter_torusDiag (P : PrincipalSeriesParameter F b m) (c : Fˣ) :
    torusCharacter F b m hm heven P
      ⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c⟩ = P.1.1 c :=
  (splitTorusCharacter_spec F b m hm heven P.1.1 P.1.2 P.2).1 c

theorem torusCharacter_torusGenerator (P : PrincipalSeriesParameter F b m) :
    torusCharacter F b m hm heven P
      ⟨torusGenerator F b m hm heven, torusGenerator_mem_splitTorus F b m hm heven⟩ = P.1.2 :=
  (splitTorusCharacter_spec F b m hm heven P.1.1 P.1.2 P.2).2

theorem torusCharacter_injective : Function.Injective (torusCharacter F b m hm heven) := by
  intro P Q h
  apply Subtype.ext
  refine Prod.ext (MonoidHom.ext fun c => ?_) ?_
  · rw [← torusCharacter_torusDiag F b m hm heven P, h, torusCharacter_torusDiag]
  · rw [← torusCharacter_torusGenerator F b m hm heven P, h, torusCharacter_torusGenerator]

theorem torusCharacter_comp_weylConj (P : PrincipalSeriesParameter F b m) :
    (torusCharacter F b m hm heven P).comp (weylConj F b m hm heven) =
      torusCharacter F b m hm heven (weylParameter F b m heven P) := by
  apply splitTorusCharacter_unique
  · intro c
    rw [MonoidHom.comp_apply]
    have hc : weylConj F b m hm heven
        ⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c⟩ =
          ⟨torusDiag F b m hm heven c⁻¹, torusDiag_mem_splitTorus F b m hm heven c⁻¹⟩ :=
      Subtype.ext (weylElement_inv_conj_torusDiag F b m hm heven c)
    rw [hc, torusCharacter_torusDiag, map_inv]
    rfl
  · rw [MonoidHom.comp_apply]
    let T := splitTorus F b m hm heven
    let hd : Fˣ → T := fun c =>
      ⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c⟩
    let v : T := ⟨torusGenerator F b m hm heven, torusGenerator_mem_splitTorus F b m hm heven⟩
    have hv : weylConj F b m hm heven v = hd (-b) * v ^ 2 * hd (-1) * v⁻¹ :=
      Subtype.ext (weylElement_inv_conj_torusGenerator F b m hm heven)
    rw [hv, map_mul, map_mul, map_mul, map_inv, map_pow, torusCharacter_torusDiag,
      torusCharacter_torusDiag, torusCharacter_torusGenerator]
    change P.1.1 (-b) * P.1.2 ^ 2 * P.1.1 (-1) * P.1.2⁻¹ = P.1.1 b * P.1.2
    have hb : P.1.1 (-b) * P.1.1 (-1) = P.1.1 b := by rw [← map_mul, neg_mul_neg, mul_one]
    rw [← hb]
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have hz : (P.1.2 : ℂ) ≠ 0 := Units.ne_zero _
    field_simp

@[expose] noncomputable def borelInflation (lam : splitTorus F b m hm heven →* ℂˣ) :
    borelSubgroup F b m hm heven →* ℂˣ :=
  lam.comp (borelProjection F b m hm heven)

theorem mem_borelSubgroup_iff (g : CentralExtension F b m hm heven) :
    g ∈ borelSubgroup F b m hm heven ↔ g • (none : Omega F) = none := Iff.rfl

@[expose] noncomputable def borelRep (p : Omega F) : CentralExtension F b m hm heven :=
  p.elim 1 fun y => unipotentElement F b m hm heven y * weylElement F b m hm heven

theorem borelRep_smul (p : Omega F) :
    borelRep F b m hm heven p • (none : Omega F) = p := by
  cases p with
  | none => exact one_smul _ _
  | some y =>
    change (unipotentElement F b m hm heven y * weylElement F b m hm heven) •
      (none : Omega F) = some y
    rw [mul_smul, weylElement_smul_none, unipotentElement_smul_some, zero_add]

theorem units_hom_conj {K : Type*} [Group K] (χ : K →* ℂˣ) (s t : K) :
    χ (s * t * s⁻¹) = χ t := by
  rw [map_mul, map_mul, map_inv, mul_comm (χ s), mul_inv_cancel_right]

theorem borelInflation_classFunction (lam : splitTorus F b m hm heven →* ℂˣ)
    (s t : borelSubgroup F b m hm heven) :
    (borelInflation F b m hm heven lam (s * t * s⁻¹) : ℂ) = borelInflation F b m hm heven lam t :=
  congrArg Units.val (units_hom_conj _ s t)

theorem principalSeries_term_of_not_fixed (lam : splitTorus F b m hm heven →* ℂˣ)
    {g : CentralExtension F b m hm heven} {p : Omega F} (hp : g • p ≠ p) :
    extendByZero (borelSubgroup F b m hm heven)
        (fun g => (borelInflation F b m hm heven lam g : ℂ))
        ((borelRep F b m hm heven p)⁻¹ * g * borelRep F b m hm heven p) = 0 := by
  apply extendByZero_of_not_mem
  rw [conj_mem_iff_of_stabilizer (mem_borelSubgroup_iff F b m hm heven), borelRep_smul]
  exact hp

theorem extendByZero_borelInflation_of_mem_splitTorus (lam : splitTorus F b m hm heven →* ℂˣ)
    {g : CentralExtension F b m hm heven} (hg : g ∈ splitTorus F b m hm heven) :
    extendByZero (borelSubgroup F b m hm heven)
        (fun g => (borelInflation F b m hm heven lam g : ℂ)) g = (lam ⟨g, hg⟩ : ℂ) := by
  rw [extendByZero_of_mem _ _ (splitTorus_le_borel F b m hm heven hg)]
  simp only [borelInflation, MonoidHom.comp_apply]
  rw [borelProjection_of_mem_splitTorus F b m hm heven _ hg]

theorem cyclicGenerator_pow_m_mem_splitTorus :
    cyclicGenerator F b m hm heven ^ m ∈ splitTorus F b m hm heven := by
  rw [← torusDiag_neg_one]
  exact torusDiag_mem_splitTorus F b m hm heven (-1)

end TorusCharacters

section Characters

variable (F : Type) [Field F] [Fintype F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

@[expose] noncomputable def principalSeries (lam : splitTorus F b m hm heven →* ℂˣ) :
    CentralExtension F b m hm heven → ℂ :=
  inducedFunction (borelSubgroup F b m hm heven)
    fun g => (borelInflation F b m hm heven lam g : ℂ)

theorem principalSeries_apply (lam : splitTorus F b m hm heven →* ℂˣ)
    (g : CentralExtension F b m hm heven) :
    principalSeries F b m hm heven lam g = ∑ p : Omega F,
      extendByZero (borelSubgroup F b m hm heven)
        (fun g => (borelInflation F b m hm heven lam g : ℂ))
        ((borelRep F b m hm heven p)⁻¹ * g * borelRep F b m hm heven p) :=
  inducedFunction_stabilizer (mem_borelSubgroup_iff F b m hm heven) _
    (borelInflation_classFunction F b m hm heven lam) (borelRep F b m hm heven)
    (borelRep_smul F b m hm heven) g

theorem principalSeries_of_central (lam : splitTorus F b m hm heven →* ℂˣ)
    {g : CentralExtension F b m hm heven} (hgT : g ∈ splitTorus F b m hm heven)
    (hcomm : ∀ x, g * x = x * g) :
    principalSeries F b m hm heven lam g = ((Nat.card F : ℂ) + 1) * (lam ⟨g, hgT⟩ : ℂ) := by
  rw [principalSeries_apply]
  have hterm : ∀ p : Omega F, extendByZero (borelSubgroup F b m hm heven)
      (fun g => (borelInflation F b m hm heven lam g : ℂ))
      ((borelRep F b m hm heven p)⁻¹ * g * borelRep F b m hm heven p) = (lam ⟨g, hgT⟩ : ℂ) := by
    intro p
    rw [mul_assoc, hcomm, inv_mul_cancel_left,
      extendByZero_borelInflation_of_mem_splitTorus F b m hm heven lam hgT]
  rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_const, Finset.card_univ,
    Fintype.card_option, nsmul_eq_mul, Nat.card_eq_fintype_card]
  push_cast
  ring

theorem principalSeries_cyclicGenerator_sq_zpow (lam : splitTorus F b m hm heven →* ℂˣ) (k : ℤ) :
    principalSeries F b m hm heven lam ((cyclicGenerator F b m hm heven ^ 2) ^ k) =
      ((Nat.card F : ℂ) + 1) * (lam ⟨cyclicGenerator F b m hm heven ^ 2,
        cyclicGenerator_sq_mem_splitTorus F b m hm heven⟩ : ℂ) ^ k := by
  have hT : (cyclicGenerator F b m hm heven ^ 2) ^ k ∈ splitTorus F b m hm heven :=
    zpow_mem (cyclicGenerator_sq_mem_splitTorus F b m hm heven) k
  rw [principalSeries_of_central F b m hm heven lam hT
    (fun x => (Commute.zpow_left (cyclicGenerator_sq_comm F b m hm heven x) k).eq)]
  have hpow : (⟨(cyclicGenerator F b m hm heven ^ 2) ^ k, hT⟩ : splitTorus F b m hm heven) =
      ⟨cyclicGenerator F b m hm heven ^ 2, cyclicGenerator_sq_mem_splitTorus F b m hm heven⟩ ^ k :=
    Subtype.ext (by simp)
  rw [hpow, map_zpow, Units.val_zpow_eq_zpow_val]

theorem principalSeries_unipotent (lam : splitTorus F b m hm heven →* ℂˣ) (k : ℤ) {t : F}
    (ht : t ≠ 0) :
    principalSeries F b m hm heven lam
        ((cyclicGenerator F b m hm heven ^ 2) ^ k * unipotentElement F b m hm heven t) =
      (lam ⟨cyclicGenerator F b m hm heven ^ 2,
        cyclicGenerator_sq_mem_splitTorus F b m hm heven⟩ : ℂ) ^ k := by
  set g := (cyclicGenerator F b m hm heven ^ 2) ^ k * unipotentElement F b m hm heven t with hg
  have hzk : (cyclicGenerator F b m hm heven ^ 2) ^ k ∈
      Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := zpow_mem (Subgroup.mem_zpowers _) k
  have hT : (cyclicGenerator F b m hm heven ^ 2) ^ k ∈ splitTorus F b m hm heven :=
    zpow_mem (cyclicGenerator_sq_mem_splitTorus F b m hm heven) k
  rw [principalSeries_apply, Fintype.sum_option]
  have hzero : ∀ y : F, extendByZero (borelSubgroup F b m hm heven)
      (fun g => (borelInflation F b m hm heven lam g : ℂ))
      ((borelRep F b m hm heven (some y))⁻¹ * g * borelRep F b m hm heven (some y)) = 0 := by
    intro y
    apply principalSeries_term_of_not_fixed
    rw [hg, mul_smul, unipotentElement_smul_some,
      zpowers_cyclicGenerator_sq_smul F b m hm heven hzk, Ne, Option.some.injEq]
    intro h
    exact ht (by linear_combination h)
  rw [Finset.sum_eq_zero fun y _ => hzero y, add_zero]
  change extendByZero (borelSubgroup F b m hm heven)
      (fun g => (borelInflation F b m hm heven lam g : ℂ))
      ((1 : CentralExtension F b m hm heven)⁻¹ * g * 1) = _
  have hcomm : g = unipotentElement F b m hm heven t * (cyclicGenerator F b m hm heven ^ 2) ^ k :=
    (Commute.zpow_left (cyclicGenerator_sq_comm F b m hm heven _) k).eq
  have hU : unipotentElement F b m hm heven t ∈ unipotentSubgroup F b m hm heven :=
    (mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨t, rfl⟩
  have hB : g ∈ borelSubgroup F b m hm heven := hcomm ▸ (borelSubgroup F b m hm heven).mul_mem
    (unipotentSubgroup_le_borel F b m hm heven hU) (splitTorus_le_borel F b m hm heven hT)
  rw [inv_one, one_mul, mul_one, extendByZero_of_mem _ _ hB]
  simp only [borelInflation, MonoidHom.comp_apply]
  rw [borelProjection_eq F b m hm heven ⟨g, hB⟩ hU hT hcomm]
  have hpow : (⟨(cyclicGenerator F b m hm heven ^ 2) ^ k, hT⟩ : splitTorus F b m hm heven) =
      ⟨cyclicGenerator F b m hm heven ^ 2, cyclicGenerator_sq_mem_splitTorus F b m hm heven⟩ ^ k :=
    Subtype.ext (by simp)
  rw [hpow, map_zpow, Units.val_zpow_eq_zpow_val]

theorem principalSeries_splitTorus (hb : ¬ IsSquare b) (lam : splitTorus F b m hm heven →* ℂˣ)
    {g : CentralExtension F b m hm heven} (hg : g ∈ splitTorus F b m hm heven)
    (hga : g ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) :
    principalSeries F b m hm heven lam g = (lam ⟨g, hg⟩ : ℂ) +
      (lam ⟨(weylElement F b m hm heven)⁻¹ * g * weylElement F b m hm heven,
        weyl_conj_mem_splitTorus F b m hm heven hg⟩ : ℂ) := by
  rw [principalSeries_apply, Fintype.sum_option, Finset.sum_eq_single (0 : F)]
  · congr 1
    · change extendByZero (borelSubgroup F b m hm heven)
        (fun g => (borelInflation F b m hm heven lam g : ℂ))
        ((1 : CentralExtension F b m hm heven)⁻¹ * g * 1) = _
      rw [inv_one, one_mul, mul_one,
        extendByZero_borelInflation_of_mem_splitTorus F b m hm heven lam hg]
    · change extendByZero (borelSubgroup F b m hm heven)
        (fun g => (borelInflation F b m hm heven lam g : ℂ))
        ((unipotentElement F b m hm heven 0 * weylElement F b m hm heven)⁻¹ * g *
          (unipotentElement F b m hm heven 0 * weylElement F b m hm heven)) = _
      simp only [unipotentElement_zero, one_mul]
      rw [extendByZero_borelInflation_of_mem_splitTorus F b m hm heven lam
        (weyl_conj_mem_splitTorus F b m hm heven hg)]
  · intro y _ hy
    apply principalSeries_term_of_not_fixed
    exact splitTorus_smul_some_ne F b m hm heven hb hg hga hy
  · intro h
    exact absurd (Finset.mem_univ 0) h

theorem principalSeries_eq_zero (lam : splitTorus F b m hm heven →* ℂˣ)
    {g : CentralExtension F b m hm heven} (hg : ∀ p : Omega F, g • p ≠ p) :
    principalSeries F b m hm heven lam g = 0 := by
  rw [principalSeries_apply]
  exact Finset.sum_eq_zero fun p _ => principalSeries_term_of_not_fixed F b m hm heven lam (hg p)

theorem principalSeries_x (P : PrincipalSeriesParameter F b m) :
    principalSeries F b m hm heven (torusCharacter F b m hm heven P)
        (cyclicGenerator F b m hm heven ^ m) = ((Nat.card F : ℂ) + 1) * (P.1.1 (-1) : ℂ) := by
  rw [principalSeries_of_central F b m hm heven _
    (cyclicGenerator_pow_m_mem_splitTorus F b m hm heven)
    (cyclicGenerator_pow_m_comm F b m hm heven)]
  have hx : (⟨cyclicGenerator F b m hm heven ^ m,
      cyclicGenerator_pow_m_mem_splitTorus F b m hm heven⟩ : splitTorus F b m hm heven) =
        ⟨torusDiag F b m hm heven (-1), torusDiag_mem_splitTorus F b m hm heven (-1)⟩ :=
    Subtype.ext (torusDiag_neg_one F b m hm heven).symm
  rw [hx, torusCharacter_torusDiag]

theorem principalSeries_inner (lam mu : splitTorus F b m hm heven →* ℂˣ) :
    BlocksInnerProduct (principalSeries F b m hm heven lam) (principalSeries F b m hm heven mu) =
      (if lam = mu then 1 else 0) +
        (if lam = mu.comp (weylConj F b m hm heven) then 1 else 0) := by
  have hk : ∀ p : Omega F, p ≠ none →
      (p.elim 1 (unipotentElement F b m hm heven) : CentralExtension F b m hm heven) ∈
        borelSubgroup F b m hm heven ∧
      (p.elim 1 (unipotentElement F b m hm heven) : CentralExtension F b m hm heven) •
        (some 0 : Omega F) = p := by
    intro p hp
    cases p with
    | none => exact absurd rfl hp
    | some y =>
      refine ⟨unipotentSubgroup_le_borel F b m hm heven
        ((mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨y, rfl⟩), ?_⟩
      change unipotentElement F b m hm heven y • (some 0 : Omega F) = some y
      rw [unipotentElement_smul_some, zero_add]
  rw [principalSeries, principalSeries,
    blocksInnerProduct_inducedFunction_twoPoint' (mem_borelSubgroup_iff F b m hm heven) (some 0)
      (weylElement F b m hm heven) (weylElement_smul_none F b m hm heven)
      (Option.some_ne_none 0) _ hk (L := splitTorus F b m hm heven) (fun _ => Iff.rfl) _ _
      (borelInflation_classFunction F b m hm heven lam)
      (borelInflation_classFunction F b m hm heven mu)]
  congr 1
  · rw [blocksInnerProduct_units_hom]
    have hiff : borelInflation F b m hm heven lam = borelInflation F b m hm heven mu ↔
        lam = mu :=
      ⟨fun h => (MonoidHom.cancel_right (borelProjection_surjective F b m hm heven)).mp h,
        fun h => h ▸ rfl⟩
    simp only [hiff]
  · rw [← blocksInnerProduct_units_hom lam (mu.comp (weylConj F b m hm heven))]
    congr 1
    · funext l
      simp only [borelInflation, MonoidHom.comp_apply]
      rw [borelProjection_of_mem_splitTorus F b m hm heven _ l.2]
    · funext l
      simp only [borelInflation, MonoidHom.comp_apply]
      rw [borelProjection_of_mem_splitTorus F b m hm heven _
        (weyl_conj_mem_splitTorus F b m hm heven l.2)]
      rfl

theorem principalSeries_inner_parameter (P Q : PrincipalSeriesParameter F b m) :
    BlocksInnerProduct (principalSeries F b m hm heven (torusCharacter F b m hm heven P))
        (principalSeries F b m hm heven (torusCharacter F b m hm heven Q)) =
      (if P = Q then 1 else 0) + (if P = weylParameter F b m heven Q then 1 else 0) := by
  rw [principalSeries_inner, torusCharacter_comp_weylConj]
  simp only [(torusCharacter_injective F b m hm heven).eq_iff]

end Characters

end CFSG.Wreathed.CentralSL2
