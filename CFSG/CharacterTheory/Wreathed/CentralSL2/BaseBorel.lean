module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.BaseTorus

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Borel

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem unipotentElement_neg_eq (t : F) :
    (unipotentElement F b m hm heven t)⁻¹ = unipotentElement F b m hm heven (-t) := by
  rw [unipotentElement, unipotentElement, ← map_inv, upperSL_neg_eq_inv]

theorem unipotentSubgroup_inf_splitTorus :
    unipotentSubgroup F b m hm heven ⊓ splitTorus F b m hm heven = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgU, hgT⟩
  obtain ⟨t, rfl⟩ := (mem_unipotentSubgroup_iff F b m hm heven g).mp hgU
  have h0 := ((mem_splitTorus_iff F b m hm heven _).mp hgT).2
  rw [unipotentElement_smul_some, zero_add, Option.some.injEq] at h0
  rw [h0, unipotentElement_zero]
  exact Subgroup.one_mem _

theorem borel_decomposition (g : CentralExtension F b m hm heven)
    (hg : g ∈ borelSubgroup F b m hm heven) :
    ∃ β : F, (unipotentElement F b m hm heven β)⁻¹ * g ∈ splitTorus F b m hm heven := by
  have hginf : g • (none : Omega F) = none := hg
  obtain ⟨β, hβ⟩ : ∃ β : F, g • (some 0 : Omega F) = some β := by
    cases h : g • (some 0 : Omega F) with
    | none =>
      exfalso
      have := hginf.trans h.symm
      exact Option.some_ne_none 0 (smul_left_cancel g this).symm
    | some β => exact ⟨β, rfl⟩
  refine ⟨β, ?_, ?_⟩
  · change ((unipotentElement F b m hm heven β)⁻¹ * g) • (none : Omega F) = none
    rw [mul_smul, hginf, inv_smul_eq_iff, unipotentElement_smul_none]
  · change ((unipotentElement F b m hm heven β)⁻¹ * g) • (some 0 : Omega F) = some 0
    rw [mul_smul, hβ, inv_smul_eq_iff, unipotentElement_smul_some, zero_add]

theorem splitTorus_conj_unipotent (g : CentralExtension F b m hm heven)
    (hg : g ∈ splitTorus F b m hm heven) (t : F) :
    ∃ s : F, g * unipotentElement F b m hm heven t * g⁻¹ = unipotentElement F b m hm heven s := by
  obtain ⟨c, k, rfl⟩ := splitTorus_normalForm F b m hm heven g hg
  have hv : ∀ (n : ℕ) (t : F), ∃ s : F, torusGenerator F b m hm heven ^ n *
      unipotentElement F b m hm heven t * (torusGenerator F b m hm heven ^ n)⁻¹ =
        unipotentElement F b m hm heven s := by
    intro n
    induction n with
    | zero => intro t; exact ⟨t, by simp⟩
    | succ n ih =>
      intro t
      obtain ⟨s, hs⟩ := ih (t / b)
      refine ⟨s, ?_⟩
      rw [← hs, ← torusGenerator_conj_unipotent F b m hm heven t, pow_succ]
      group
  obtain ⟨s, hs⟩ := hv k t
  refine ⟨(c : F) ^ 2 * s, ?_⟩
  rw [← torusDiag_conj_unipotent F b m hm heven c s, ← hs]
  group

theorem unipotentSubgroup_normal_in_borel (g : CentralExtension F b m hm heven)
    (hg : g ∈ borelSubgroup F b m hm heven) (u : CentralExtension F b m hm heven)
    (hu : u ∈ unipotentSubgroup F b m hm heven) :
    g * u * g⁻¹ ∈ unipotentSubgroup F b m hm heven := by
  obtain ⟨β, hβ⟩ := borel_decomposition F b m hm heven g hg
  obtain ⟨t, rfl⟩ := (mem_unipotentSubgroup_iff F b m hm heven u).mp hu
  set τ := (unipotentElement F b m hm heven β)⁻¹ * g with hτ
  have hg' : g = unipotentElement F b m hm heven β * τ := by rw [hτ, mul_inv_cancel_left]
  obtain ⟨s, hs⟩ := splitTorus_conj_unipotent F b m hm heven τ hβ t
  rw [hg', mem_unipotentSubgroup_iff]
  refine ⟨β + s + -β, ?_⟩
  rw [unipotentElement_add, unipotentElement_add, ← hs, ← unipotentElement_neg_eq]
  group

end Borel

section Projection

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

@[expose] noncomputable def borelTranslation (g : CentralExtension F b m hm heven) : F :=
  (g • (some 0 : Omega F)).getD 0

theorem smul_zero_eq_borelTranslation {g : CentralExtension F b m hm heven}
    (hg : g ∈ borelSubgroup F b m hm heven) :
    g • (some 0 : Omega F) = some (borelTranslation F b m hm heven g) := by
  have hginf : g • (none : Omega F) = none := hg
  cases h : g • (some 0 : Omega F) with
  | none =>
    exfalso
    exact Option.some_ne_none 0 (smul_left_cancel g (h.trans hginf.symm))
  | some β => simp [borelTranslation, h]

@[expose] noncomputable def borelProjectionFun (g : CentralExtension F b m hm heven) :
    CentralExtension F b m hm heven :=
  (unipotentElement F b m hm heven (borelTranslation F b m hm heven g))⁻¹ * g

theorem borelProjectionFun_mem {g : CentralExtension F b m hm heven}
    (hg : g ∈ borelSubgroup F b m hm heven) :
    borelProjectionFun F b m hm heven g ∈ splitTorus F b m hm heven := by
  have hginf : g • (none : Omega F) = none := hg
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · change (_ * g) • (none : Omega F) = none
    rw [mul_smul, hginf, inv_smul_eq_iff, unipotentElement_smul_none]
  · change (_ * g) • (some 0 : Omega F) = some 0
    rw [mul_smul, smul_zero_eq_borelTranslation F b m hm heven hg, inv_smul_eq_iff,
      unipotentElement_smul_some, zero_add]

theorem unipotentElement_mul_borelProjectionFun (g : CentralExtension F b m hm heven) :
    unipotentElement F b m hm heven (borelTranslation F b m hm heven g) *
      borelProjectionFun F b m hm heven g = g :=
  mul_inv_cancel_left _ _

theorem eq_of_unipotent_mul_eq {u u' t t' : CentralExtension F b m hm heven}
    (hu : u ∈ unipotentSubgroup F b m hm heven) (hu' : u' ∈ unipotentSubgroup F b m hm heven)
    (ht : t ∈ splitTorus F b m hm heven) (ht' : t' ∈ splitTorus F b m hm heven)
    (h : u * t = u' * t') : t = t' := by
  have hmem : u'⁻¹ * u = t' * t⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have h1 : t' * t⁻¹ ∈ unipotentSubgroup F b m hm heven ⊓ splitTorus F b m hm heven :=
    Subgroup.mem_inf.mpr ⟨hmem ▸ (unipotentSubgroup F b m hm heven).mul_mem
      ((unipotentSubgroup F b m hm heven).inv_mem hu') hu,
      (splitTorus F b m hm heven).mul_mem ht' ((splitTorus F b m hm heven).inv_mem ht)⟩
  rw [unipotentSubgroup_inf_splitTorus, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1.symm

theorem borelProjectionFun_eq {g u t : CentralExtension F b m hm heven}
    (hu : u ∈ unipotentSubgroup F b m hm heven) (ht : t ∈ splitTorus F b m hm heven)
    (h : g = u * t) : borelProjectionFun F b m hm heven g = t := by
  have hg : g ∈ borelSubgroup F b m hm heven := h ▸ (borelSubgroup F b m hm heven).mul_mem
    (unipotentSubgroup_le_borel F b m hm heven hu) (splitTorus_le_borel F b m hm heven ht)
  refine eq_of_unipotent_mul_eq F b m hm heven
    ((mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨borelTranslation F b m hm heven g, rfl⟩) hu
    (borelProjectionFun_mem F b m hm heven hg) ht ?_
  rw [unipotentElement_mul_borelProjectionFun, h]

@[expose] noncomputable def borelProjection :
    borelSubgroup F b m hm heven →* splitTorus F b m hm heven where
  toFun g := ⟨borelProjectionFun F b m hm heven g, borelProjectionFun_mem F b m hm heven g.2⟩
  map_one' := Subtype.ext (borelProjectionFun_eq F b m hm heven
    (unipotentSubgroup F b m hm heven).one_mem (splitTorus F b m hm heven).one_mem
    (mul_one 1).symm)
  map_mul' g g' := by
    apply Subtype.ext
    set t := borelProjectionFun F b m hm heven g
    set t' := borelProjectionFun F b m hm heven g'
    have ht : t ∈ splitTorus F b m hm heven := borelProjectionFun_mem F b m hm heven g.2
    have ht' : t' ∈ splitTorus F b m hm heven := borelProjectionFun_mem F b m hm heven g'.2
    obtain ⟨s, hs⟩ := splitTorus_conj_unipotent F b m hm heven t ht
      (borelTranslation F b m hm heven g')
    refine borelProjectionFun_eq F b m hm heven (u := unipotentElement F b m hm heven
      (borelTranslation F b m hm heven g) * unipotentElement F b m hm heven s)
      ((unipotentSubgroup F b m hm heven).mul_mem
        ((mem_unipotentSubgroup_iff F b m hm heven _).mpr
          ⟨borelTranslation F b m hm heven g, rfl⟩)
        ((mem_unipotentSubgroup_iff F b m hm heven _).mpr ⟨s, rfl⟩))
      ((splitTorus F b m hm heven).mul_mem ht ht') ?_
    rw [← hs]
    change ((g * g' : borelSubgroup F b m hm heven) : CentralExtension F b m hm heven) =
      _ * (t * t')
    calc ((g * g' : borelSubgroup F b m hm heven) : CentralExtension F b m hm heven)
        = (unipotentElement F b m hm heven (borelTranslation F b m hm heven g) * t) *
            (unipotentElement F b m hm heven (borelTranslation F b m hm heven g') * t') := by
          rw [unipotentElement_mul_borelProjectionFun, unipotentElement_mul_borelProjectionFun]
          rfl
      _ = _ := by group

theorem borelProjection_apply (g : borelSubgroup F b m hm heven) :
    (borelProjection F b m hm heven g : CentralExtension F b m hm heven) =
      borelProjectionFun F b m hm heven g := rfl

theorem borelProjection_eq (g : borelSubgroup F b m hm heven)
    {u t : CentralExtension F b m hm heven}
    (hu : u ∈ unipotentSubgroup F b m hm heven) (ht : t ∈ splitTorus F b m hm heven)
    (h : (g : CentralExtension F b m hm heven) = u * t) :
    borelProjection F b m hm heven g = ⟨t, ht⟩ :=
  Subtype.ext (borelProjectionFun_eq F b m hm heven hu ht h)

theorem borelProjection_of_mem_splitTorus (g : borelSubgroup F b m hm heven)
    (hg : (g : CentralExtension F b m hm heven) ∈ splitTorus F b m hm heven) :
    borelProjection F b m hm heven g = ⟨g, hg⟩ :=
  borelProjection_eq F b m hm heven g (unipotentSubgroup F b m hm heven).one_mem hg
    (one_mul _).symm

theorem borelProjection_of_mem_unipotent (g : borelSubgroup F b m hm heven)
    (hg : (g : CentralExtension F b m hm heven) ∈ unipotentSubgroup F b m hm heven) :
    borelProjection F b m hm heven g = 1 :=
  (borelProjection_eq F b m hm heven g hg (splitTorus F b m hm heven).one_mem
    (mul_one _).symm).trans rfl

theorem borelProjection_surjective : Function.Surjective (borelProjection F b m hm heven) :=
  fun t => ⟨⟨t, splitTorus_le_borel F b m hm heven t.2⟩,
    borelProjection_of_mem_splitTorus F b m hm heven _ t.2⟩

end Projection

section WeylConjugation

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem weylElement_inv_smul_zero :
    (weylElement F b m hm heven)⁻¹ • (some 0 : Omega F) = none := by
  rw [inv_smul_eq_iff, weylElement_smul_none]

theorem weylElement_inv_smul_none :
    (weylElement F b m hm heven)⁻¹ • (none : Omega F) = some 0 := by
  rw [inv_smul_eq_iff, weylElement_smul_zero]

theorem weyl_conj_mem_splitTorus {t : CentralExtension F b m hm heven}
    (ht : t ∈ splitTorus F b m hm heven) :
    (weylElement F b m hm heven)⁻¹ * t * weylElement F b m hm heven ∈
      splitTorus F b m hm heven := by
  obtain ⟨h1, h2⟩ := (mem_splitTorus_iff F b m hm heven t).mp ht
  rw [mem_splitTorus_iff, mul_smul, mul_smul, mul_smul, mul_smul, weylElement_smul_none, h2,
    weylElement_inv_smul_zero, weylElement_smul_zero, h1, weylElement_inv_smul_none]
  exact ⟨rfl, rfl⟩

@[expose] noncomputable def weylConj : splitTorus F b m hm heven →* splitTorus F b m hm heven where
  toFun t := ⟨(weylElement F b m hm heven)⁻¹ * t * weylElement F b m hm heven,
    weyl_conj_mem_splitTorus F b m hm heven t.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem weylConj_apply (t : splitTorus F b m hm heven) :
    (weylConj F b m hm heven t : CentralExtension F b m hm heven) =
      (weylElement F b m hm heven)⁻¹ * t * weylElement F b m hm heven := rfl

theorem weylElement_inv_conj_torusDiag (c : Fˣ) :
    (weylElement F b m hm heven)⁻¹ * torusDiag F b m hm heven c * weylElement F b m hm heven =
      torusDiag F b m hm heven c⁻¹ := by
  rw [weylElement_inv_conj, weylElement_conj_torusDiag]

theorem cyclicGenerator_sq_eq :
    cyclicGenerator F b m hm heven ^ 2 =
      torusDiag F b m hm heven (-b) * torusGenerator F b m hm heven ^ 2 := by
  rw [torusGenerator_sq, ← mul_assoc, ← torusDiag_mul]
  have : -b * -b⁻¹ = 1 := by rw [neg_mul_neg, mul_inv_cancel]
  rw [this, torusDiag_one, one_mul]

theorem weylElement_inv_conj_torusGenerator :
    (weylElement F b m hm heven)⁻¹ * torusGenerator F b m hm heven * weylElement F b m hm heven =
      torusDiag F b m hm heven (-b) * torusGenerator F b m hm heven ^ 2 *
        torusDiag F b m hm heven (-1) * (torusGenerator F b m hm heven)⁻¹ := by
  rw [weylElement_inv_conj, weylElement_conj_torusGenerator, cyclicGenerator_sq_eq,
    torusDiag_neg_one]

end WeylConjugation

section ActionFacts

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem zpowers_cyclicGenerator_sq_smul {g : CentralExtension F b m hm heven}
    (hg : g ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) (x : Omega F) :
    g • x = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [centralExtension_smul_def, map_zpow, projAction_cyclicGenerator_sq, _root_.one_zpow]
  rfl

theorem fixes_all_iff (hb : ¬ IsSquare b) (g : CentralExtension F b m hm heven) :
    (∀ x : Omega F, g • x = x) ↔ g ∈ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  refine ⟨fun hfix => ?_, fun hg x => zpowers_cyclicGenerator_sq_smul F b m hm heven hg x⟩
  have hSigma : ∀ σ ∈ (⊥ : Subgroup (F ≃+* F)), σ (b : F) = b := by
    intro σ hσ
    rw [Subgroup.mem_bot.mp hσ]
    rfl
  have hker := semilinearAction_ker F b m hm heven ⊥ hSigma hb
  have hmem : (SemidirectProduct.inl g : SemilinearExtension F b m hm heven ⊥ hSigma) ∈
      (semilinearAction F b m hm heven ⊥ hSigma).ker := by
    rw [MonoidHom.mem_ker, semilinearAction_inl]
    exact Equiv.ext fun x => hfix x
  rw [hker, Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  rw [← map_zpow] at hk
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, SemidirectProduct.inl_injective hk⟩

theorem torusGenerator_pow_smul_some (k : ℕ) (y : F) :
    torusGenerator F b m hm heven ^ k • (some y : Omega F) = some (y / (b : F) ^ k) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_smul, torusGenerator_smul_some, ih]
    congr 1
    rw [div_div, ← pow_succ']

theorem splitTorus_smul_some {g : CentralExtension F b m hm heven}
    (hg : g ∈ splitTorus F b m hm heven) :
    ∃ α : F, α ≠ 0 ∧ ∀ y : F, g • (some y : Omega F) = some (α * y) := by
  obtain ⟨c, k, rfl⟩ := splitTorus_normalForm F b m hm heven g hg
  have hb : (b : F) ^ (k : ℕ) ≠ 0 := pow_ne_zero _ b.ne_zero
  refine ⟨(c : F) ^ 2 / (b : F) ^ (k : ℕ), div_ne_zero (pow_ne_zero _ c.ne_zero) hb,
    fun y => ?_⟩
  rw [mul_smul, torusGenerator_pow_smul_some, torusDiag_smul_some]
  congr 1
  ring

theorem splitTorus_smul_some_ne (hb : ¬ IsSquare b) {g : CentralExtension F b m hm heven}
    (hg : g ∈ splitTorus F b m hm heven)
    (hga : g ∉ Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2)) {y : F} (hy : y ≠ 0) :
    g • (some y : Omega F) ≠ some y := by
  obtain ⟨α, -, hα⟩ := splitTorus_smul_some F b m hm heven hg
  intro hfix
  rw [hα, Option.some.injEq] at hfix
  have hα1 : α = 1 := by
    have h' : (α - 1) * y = 0 := by rw [sub_mul, hfix, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hy)
  apply hga
  rw [← fixes_all_iff F b m hm heven hb]
  intro x
  cases x with
  | none => exact ((mem_splitTorus_iff F b m hm heven g).mp hg).1
  | some y' => rw [hα, hα1, one_mul]

theorem unipotentElement_smul_some_ne {t : F} (ht : t ≠ 0) (y : F) :
    unipotentElement F b m hm heven t • (some y : Omega F) ≠ some y := by
  rw [unipotentElement_smul_some, Ne, Option.some.injEq]
  intro h
  exact ht (by linear_combination h)

theorem centralExtension_isMultiplyPretransitive :
    MulAction.IsMultiplyPretransitive (CentralExtension F b m hm heven) (Omega F) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a a' c d haa' hcd
  obtain ⟨Y, hY1, hY2⟩ := exists_SL_infinity_zero F a a' haa'
  obtain ⟨X, hX1, hX2⟩ := exists_SL_infinity_zero F c d hcd
  refine ⟨specialInclusion F b m hm heven (X * Y⁻¹), ?_, ?_⟩
  · rw [specialInclusion_smul, map_mul, map_mul, map_inv, map_inv, Equiv.Perm.mul_apply,
      (Equiv.Perm.inv_eq_iff_eq.mpr hY1.symm), hX1]
  · rw [specialInclusion_smul, map_mul, map_mul, map_inv, map_inv, Equiv.Perm.mul_apply,
      (Equiv.Perm.inv_eq_iff_eq.mpr hY2.symm), hX2]

end ActionFacts

end CFSG.Wreathed.CentralSL2
