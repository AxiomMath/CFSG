module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.BaseElements
public import CFSG.CharacterTheory.Wreathed.CentralSL2.ActionKernel

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Action

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem specialInclusion_smul (X : SpecialLinearGroup (Fin 2) F) (x : Omega F) :
    specialInclusion F b m hm heven X • x = coordinateGLAction F (SpecialLinearGroup.toGL X) x := by
  rw [centralExtension_smul_def, specialInclusion_apply, projAction_quotientClass, ZMod.val_zero,
    pow_zero, mul_one]

theorem toGL_val (X : SpecialLinearGroup (Fin 2) F) (i j : Fin 2) :
    (SpecialLinearGroup.toGL X : Matrix (Fin 2) (Fin 2) F) i j = X i j := rfl

theorem specialInclusion_smul_none (X : SpecialLinearGroup (Fin 2) F) :
    specialInclusion F b m hm heven X • (none : Omega F) =
      if X 1 0 = 0 then none else some (X 0 0 / X 1 0) := by
  rw [specialInclusion_smul, coordinateGLAction_toGL_none]

theorem specialInclusion_smul_some (X : SpecialLinearGroup (Fin 2) F) (y : F) :
    specialInclusion F b m hm heven X • (some y : Omega F) =
      if X 1 0 * y + X 1 1 = 0 then none else some ((X 0 0 * y + X 0 1) / (X 1 0 * y + X 1 1)) := by
  rw [specialInclusion_smul]
  split_ifs with h
  · exact coordinateGLAction_finite_denominator_zero F _ y h
  · exact coordinateGLAction_finite F _ y h

theorem torusDiag_smul_none (c : Fˣ) : torusDiag F b m hm heven c • (none : Omega F) = none := by
  rw [torusDiag, specialInclusion_smul_none, ite_eq_left (by simp [diagSL])]

theorem torusDiag_smul_some (c : Fˣ) (y : F) :
    torusDiag F b m hm heven c • (some y : Omega F) = some ((c : F) ^ 2 * y) := by
  rw [torusDiag, specialInclusion_smul_some]
  have hc : ((c⁻¹ : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have hc0 : (c : F) ≠ 0 := Units.ne_zero _
  simp only [diagSL, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one, zero_mul, zero_add, add_zero]
  rw [ite_eq_right hc]
  congr 1
  rw [Units.val_inv_eq_inv_val]
  field_simp

theorem unipotentElement_smul_none (t : F) :
    unipotentElement F b m hm heven t • (none : Omega F) = none := by
  rw [unipotentElement, specialInclusion_smul_none, ite_eq_left (by simp [upperSL])]

theorem unipotentElement_smul_some (t y : F) :
    unipotentElement F b m hm heven t • (some y : Omega F) = some (y + t) := by
  rw [unipotentElement, specialInclusion_smul_some]
  simp [upperSL]

theorem weylElement_smul_none : weylElement F b m hm heven • (none : Omega F) = some 0 := by
  rw [weylElement, specialInclusion_smul_none]
  simp [weyl]

theorem weylElement_smul_zero : weylElement F b m hm heven • (some 0 : Omega F) = none := by
  rw [weylElement, specialInclusion_smul_some]
  simp [weyl]

theorem cyclicGenerator_sq_smul (x : Omega F) :
    cyclicGenerator F b m hm heven ^ 2 • x = x := by
  rw [centralExtension_smul_def, projAction_cyclicGenerator_sq, Equiv.Perm.one_apply]

theorem torusGenerator_smul_none :
    torusGenerator F b m hm heven • (none : Omega F) = none := by
  rw [torusGenerator, mul_smul, centralExtension_smul_def F b m hm heven
    (cyclicGenerator F b m hm heven), projAction_cyclicGenerator]
  rw [show coordJ F b none = some 0 by
      rw [coordJ, coordinateGLAction_infinity F _ (by simp [nonsquareMatrix_val])]
      simp [nonsquareMatrix_val]]
  rw [inv_smul_eq_iff, weylElement_smul_none]

theorem torusGenerator_smul_some (y : F) :
    torusGenerator F b m hm heven • (some y : Omega F) = some (y / b) := by
  rw [torusGenerator, mul_smul, inv_smul_eq_iff, centralExtension_smul_def F b m hm heven
    (cyclicGenerator F b m hm heven), projAction_cyclicGenerator, weylElement,
    specialInclusion_smul_some]
  have hb : (b : F) ≠ 0 := b.ne_zero
  by_cases hy : y = 0
  · subst hy
    rw [show coordJ F b (some 0) = none by
      rw [coordJ]
      exact coordinateGLAction_finite_denominator_zero F _ 0 (by simp [nonsquareMatrix_val])]
    simp [weyl]
  · rw [show coordJ F b (some y) = some (-(b : F) / y) by
      rw [coordJ, coordinateGLAction_finite F _ y (by simpa [nonsquareMatrix_val] using hy)]
      congr 1
      simp [nonsquareMatrix_val]]
    have hdiv : y / (b : F) ≠ 0 := div_ne_zero hy hb
    simp only [weyl, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, one_mul, add_zero, zero_mul, zero_add]
    rw [ite_eq_right hdiv]
    congr 1
    field_simp

end Action

section Subgroups

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

@[expose] noncomputable def borelSubgroup : Subgroup (CentralExtension F b m hm heven) :=
  MulAction.stabilizer (CentralExtension F b m hm heven) (none : Omega F)

@[expose] noncomputable def splitTorus : Subgroup (CentralExtension F b m hm heven) :=
  borelSubgroup F b m hm heven ⊓
    MulAction.stabilizer (CentralExtension F b m hm heven) (some 0 : Omega F)

@[expose] noncomputable def unipotentSubgroup : Subgroup (CentralExtension F b m hm heven) :=
  ((specialInclusion F b m hm heven).comp (upperHom F)).range

theorem mem_splitTorus_iff (g : CentralExtension F b m hm heven) :
    g ∈ splitTorus F b m hm heven ↔ g • (none : Omega F) = none ∧ g • (some 0 : Omega F) = some 0 :=
  Iff.rfl

theorem mem_unipotentSubgroup_iff (g : CentralExtension F b m hm heven) :
    g ∈ unipotentSubgroup F b m hm heven ↔ ∃ t : F, unipotentElement F b m hm heven t = g := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.toAdd, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩

theorem torusDiag_mem_splitTorus (c : Fˣ) :
    torusDiag F b m hm heven c ∈ splitTorus F b m hm heven := by
  rw [mem_splitTorus_iff, torusDiag_smul_none, torusDiag_smul_some, mul_zero]
  exact ⟨rfl, rfl⟩

theorem torusGenerator_mem_splitTorus :
    torusGenerator F b m hm heven ∈ splitTorus F b m hm heven := by
  rw [mem_splitTorus_iff, torusGenerator_smul_none, torusGenerator_smul_some, zero_div]
  exact ⟨rfl, rfl⟩

theorem cyclicGenerator_sq_mem_splitTorus :
    cyclicGenerator F b m hm heven ^ 2 ∈ splitTorus F b m hm heven := by
  rw [mem_splitTorus_iff, cyclicGenerator_sq_smul, cyclicGenerator_sq_smul]
  exact ⟨rfl, rfl⟩

theorem unipotentSubgroup_le_borel :
    unipotentSubgroup F b m hm heven ≤ borelSubgroup F b m hm heven := by
  intro g hg
  obtain ⟨t, rfl⟩ := (mem_unipotentSubgroup_iff F b m hm heven g).mp hg
  exact unipotentElement_smul_none F b m hm heven t

theorem splitTorus_le_borel : splitTorus F b m hm heven ≤ borelSubgroup F b m hm heven :=
  inf_le_left

end Subgroups

section NormalForm

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem baseResidue_torusDiag (c : Fˣ) :
    baseResidue F b m hm heven (torusDiag F b m hm heven c) = 1 :=
  baseResidue_specialInclusion F b m hm heven _

theorem baseResidue_torusGenerator :
    baseResidue F b m hm heven (torusGenerator F b m hm heven) = Multiplicative.ofAdd 1 := by
  rw [torusGenerator_eq, baseResidue_quotientClass, map_one]

theorem baseResidue_torusGenerator_pow (k : ℕ) :
    baseResidue F b m hm heven (torusGenerator F b m hm heven ^ k) =
      Multiplicative.ofAdd (k : ZMod m) := by
  rw [map_pow, baseResidue_torusGenerator, ← ofAdd_nsmul, nsmul_one]

theorem torusDiag_injective : Function.Injective (torusDiag F b m hm heven) := by
  intro c d h
  have h' := specialInclusion_injective F b m hm heven h
  have h00 := congrArg (fun X : SpecialLinearGroup (Fin 2) F => X 0 0) h'
  apply Units.ext
  simpa [diagSL] using h00

theorem specialInclusion_mem_splitTorus_iff (Y : SpecialLinearGroup (Fin 2) F) :
    specialInclusion F b m hm heven Y ∈ splitTorus F b m hm heven ↔ Y 1 0 = 0 ∧ Y 0 1 = 0 := by
  rw [mem_splitTorus_iff, specialInclusion_smul_none, specialInclusion_smul_some]
  have hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = 1 := by
    rw [← det_fin_two]
    exact Y.2
  constructor
  · rintro ⟨h1, h2⟩
    have h10 : Y 1 0 = 0 := by
      by_contra h
      rw [ite_eq_right h] at h1
      exact Option.some_ne_none _ h1
    refine ⟨h10, ?_⟩
    have h11 : Y 1 1 ≠ 0 := by
      intro h11
      rw [h10, h11] at hdet
      simp at hdet
    rw [mul_zero, zero_add, ite_eq_right h11, Option.some.injEq, mul_zero, zero_add,
      div_eq_zero_iff] at h2
    exact h2.resolve_right h11
  · rintro ⟨h10, h01⟩
    have h11 : Y 1 1 ≠ 0 := by
      intro h11
      rw [h10, h11] at hdet
      simp at hdet
    refine ⟨by rw [ite_eq_left h10], ?_⟩
    rw [mul_zero, zero_add, ite_eq_right h11, mul_zero, zero_add, h01, zero_div]

theorem eq_diagSL_of_diag (Y : SpecialLinearGroup (Fin 2) F) (h10 : Y 1 0 = 0)
    (h01 : Y 0 1 = 0) : ∃ c : Fˣ, Y = diagSL F c := by
  have hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = 1 := by
    rw [← det_fin_two]
    exact Y.2
  rw [h10, mul_zero, sub_zero] at hdet
  have h00 : Y 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 (Y 0 0) h00, ?_⟩
  have h11 : Y 1 1 = (Y 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  apply SL_eq_of_val
  rw [diagSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, h11]

theorem splitTorus_normalForm (g : CentralExtension F b m hm heven)
    (hg : g ∈ splitTorus F b m hm heven) :
    ∃ c : Fˣ, ∃ k : Fin m,
      g = torusDiag F b m hm heven c * torusGenerator F b m hm heven ^ (k : ℕ) := by
  have : NeZero m := ⟨hm.ne'⟩
  set k : Fin m := ⟨(baseResidue F b m hm heven g).toAdd.val, ZMod.val_lt _⟩ with hk
  have hres : baseResidue F b m hm heven (g * (torusGenerator F b m hm heven ^ (k : ℕ))⁻¹) = 1 := by
    rw [map_mul, map_inv, baseResidue_torusGenerator_pow, hk]
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    rw [ofAdd_toAdd, mul_inv_cancel]
  have hmem : g * (torusGenerator F b m hm heven ^ (k : ℕ))⁻¹ ∈
      (specialInclusion F b m hm heven).range := by
    rw [← baseResidue_ker, MonoidHom.mem_ker]
    exact hres
  obtain ⟨Y, hY⟩ := hmem
  have hYT : specialInclusion F b m hm heven Y ∈ splitTorus F b m hm heven := by
    rw [hY]
    exact (splitTorus F b m hm heven).mul_mem hg ((splitTorus F b m hm heven).inv_mem
      ((splitTorus F b m hm heven).pow_mem (torusGenerator_mem_splitTorus F b m hm heven) _))
  obtain ⟨h10, h01⟩ := (specialInclusion_mem_splitTorus_iff F b m hm heven Y).mp hYT
  obtain ⟨c, rfl⟩ := eq_diagSL_of_diag F Y h10 h01
  refine ⟨c, k, ?_⟩
  rw [torusDiag, hY, inv_mul_cancel_right]

theorem splitTorus_normalForm_unique {c c' : Fˣ} {k k' : Fin m}
    (h : torusDiag F b m hm heven c * torusGenerator F b m hm heven ^ (k : ℕ) =
      torusDiag F b m hm heven c' * torusGenerator F b m hm heven ^ (k' : ℕ)) :
    c = c' ∧ k = k' := by
  have : NeZero m := ⟨hm.ne'⟩
  have hres := congrArg (baseResidue F b m hm heven) h
  rw [map_mul, map_mul, baseResidue_torusDiag, baseResidue_torusDiag, one_mul, one_mul,
    baseResidue_torusGenerator_pow, baseResidue_torusGenerator_pow] at hres
  have hkk : k = k' := by
    have := congrArg ZMod.val (congrArg Multiplicative.toAdd hres)
    simp only [toAdd_ofAdd, ZMod.val_natCast, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2] at this
    exact Fin.ext this
  subst hkk
  exact ⟨torusDiag_injective F b m hm heven (mul_right_cancel h), rfl⟩

theorem card_splitTorus [Finite F] :
    Nat.card (splitTorus F b m hm heven) = m * (Nat.card F - 1) := by
  have : Fintype F := Fintype.ofFinite F
  let e : Fˣ × Fin m → splitTorus F b m hm heven := fun p =>
    ⟨torusDiag F b m hm heven p.1 * torusGenerator F b m hm heven ^ (p.2 : ℕ),
      (splitTorus F b m hm heven).mul_mem (torusDiag_mem_splitTorus F b m hm heven _)
        ((splitTorus F b m hm heven).pow_mem (torusGenerator_mem_splitTorus F b m hm heven) _)⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨c, k⟩ ⟨c', k'⟩ h
      obtain ⟨h1, h2⟩ := splitTorus_normalForm_unique F b m hm heven (congrArg Subtype.val h)
      exact Prod.ext h1 h2
    · rintro ⟨g, hg⟩
      obtain ⟨c, k, rfl⟩ := splitTorus_normalForm F b m hm heven g hg
      exact ⟨(c, k), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_units, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
    Nat.card_eq_fintype_card, mul_comm]

theorem splitTorus_mul_comm {g g' : CentralExtension F b m hm heven}
    (hg : g ∈ splitTorus F b m hm heven) (hg' : g' ∈ splitTorus F b m hm heven) :
    g * g' = g' * g := by
  obtain ⟨c, k, rfl⟩ := splitTorus_normalForm F b m hm heven g hg
  obtain ⟨c', k', rfl⟩ := splitTorus_normalForm F b m hm heven g' hg'
  have hcomm : ∀ (d : Fˣ) (n : ℕ), Commute (torusGenerator F b m hm heven ^ n)
      (torusDiag F b m hm heven d) := fun d n =>
    Commute.pow_left (torusGenerator_mul_torusDiag F b m hm heven d) n
  have hdd : ∀ d d' : Fˣ, Commute (torusDiag F b m hm heven d) (torusDiag F b m hm heven d') :=
    fun d d' => by
      change _ * _ = _ * _
      rw [← torusDiag_mul, ← torusDiag_mul, mul_comm]
  calc torusDiag F b m hm heven c * torusGenerator F b m hm heven ^ (k : ℕ) *
        (torusDiag F b m hm heven c' * torusGenerator F b m hm heven ^ (k' : ℕ))
      = torusDiag F b m hm heven c * torusDiag F b m hm heven c' *
          (torusGenerator F b m hm heven ^ (k : ℕ) * torusGenerator F b m hm heven ^ (k' : ℕ)) := by
        rw [mul_assoc, ← mul_assoc (torusGenerator F b m hm heven ^ (k : ℕ)),
          (hcomm c' k).eq, mul_assoc, mul_assoc]
    _ = torusDiag F b m hm heven c' * torusDiag F b m hm heven c *
          (torusGenerator F b m hm heven ^ (k' : ℕ) * torusGenerator F b m hm heven ^ (k : ℕ)) := by
        rw [(hdd c c').eq, ← pow_add, ← pow_add, add_comm]
    _ = _ := by
        rw [mul_assoc, ← mul_assoc (torusDiag F b m hm heven c),
          ← (hcomm c k').eq, mul_assoc, mul_assoc]

instance splitTorus_isMulCommutative :
    IsMulCommutative (splitTorus F b m hm heven) :=
  ⟨⟨fun x y => Subtype.ext (splitTorus_mul_comm F b m hm heven x.2 y.2)⟩⟩

theorem splitTorus_eq_closure :
    splitTorus F b m hm heven = Subgroup.closure
      (Set.range (torusDiag F b m hm heven) ∪ {torusGenerator F b m hm heven}) := by
  set S := Set.range (torusDiag F b m hm heven) ∪ {torusGenerator F b m hm heven} with hS
  apply le_antisymm
  · intro g hg
    obtain ⟨c, k, rfl⟩ := splitTorus_normalForm F b m hm heven g hg
    have h1 : torusDiag F b m hm heven c ∈ Subgroup.closure S :=
      Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
    have h2 : torusGenerator F b m hm heven ∈ Subgroup.closure S :=
      Subgroup.subset_closure (Or.inr rfl)
    exact (Subgroup.closure S).mul_mem h1 ((Subgroup.closure S).pow_mem h2 _)
  · rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | h)
    · exact torusDiag_mem_splitTorus F b m hm heven c
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact torusGenerator_mem_splitTorus F b m hm heven

end NormalForm

section Presentation

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

@[expose] noncomputable def torusDiagHom : Fˣ →* CentralExtension F b m hm heven where
  toFun := torusDiag F b m hm heven
  map_one' := torusDiag_one F b m hm heven
  map_mul' := torusDiag_mul F b m hm heven

@[expose] noncomputable def splitTorusCover :
    Fˣ × Multiplicative ℤ →* splitTorus F b m hm heven where
  toFun p := ⟨torusDiag F b m hm heven p.1 * torusGenerator F b m hm heven ^ p.2.toAdd,
    (splitTorus F b m hm heven).mul_mem (torusDiag_mem_splitTorus F b m hm heven _)
      ((splitTorus F b m hm heven).zpow_mem (torusGenerator_mem_splitTorus F b m hm heven) _)⟩
  map_one' := by
    apply Subtype.ext
    simp [torusDiag_one]
  map_mul' p q := by
    apply Subtype.ext
    have hcomm : Commute (torusGenerator F b m hm heven ^ p.2.toAdd)
        (torusDiag F b m hm heven q.1) :=
      Commute.zpow_left (torusGenerator_mul_torusDiag F b m hm heven q.1) _
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, Subgroup.coe_mul, torusDiag_mul,
      _root_.zpow_add]
    rw [mul_assoc (torusDiag F b m hm heven p.1) (torusGenerator F b m hm heven ^ p.2.toAdd),
      ← mul_assoc (torusGenerator F b m hm heven ^ p.2.toAdd), hcomm.eq]
    simp only [mul_assoc]

theorem splitTorusCover_apply (p : Fˣ × Multiplicative ℤ) :
    (splitTorusCover F b m hm heven p : CentralExtension F b m hm heven) =
      torusDiag F b m hm heven p.1 * torusGenerator F b m hm heven ^ p.2.toAdd := rfl

theorem splitTorusCover_surjective : Function.Surjective (splitTorusCover F b m hm heven) := by
  rintro ⟨g, hg⟩
  obtain ⟨c, k, rfl⟩ := splitTorus_normalForm F b m hm heven g hg
  refine ⟨(c, Multiplicative.ofAdd (k : ℤ)), Subtype.ext ?_⟩
  rw [splitTorusCover_apply, toAdd_ofAdd, zpow_natCast]

theorem splitTorusCover_ker_le {p : Fˣ × Multiplicative ℤ}
    (hp : p ∈ (splitTorusCover F b m hm heven).ker) :
    ∃ l : ℤ, p = ((torusConstant F b m) ^ (-l), Multiplicative.ofAdd ((m : ℤ) * l)) := by
  have : NeZero m := ⟨hm.ne'⟩
  rw [MonoidHom.mem_ker] at hp
  have hp' := congrArg Subtype.val hp
  rw [splitTorusCover_apply, Subgroup.coe_one] at hp'
  have hres := congrArg (baseResidue F b m hm heven) hp'
  have hv : baseResidue F b m hm heven (torusGenerator F b m hm heven ^ p.2.toAdd) =
      Multiplicative.ofAdd ((p.2.toAdd : ℤ) : ZMod m) := by
    rw [map_zpow, baseResidue_torusGenerator, ← ofAdd_zsmul, zsmul_one]
  rw [map_mul, baseResidue_torusDiag, one_mul, hv, map_one] at hres
  have hdvd : (m : ℤ) ∣ p.2.toAdd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
    (congrArg Multiplicative.toAdd hres)
  obtain ⟨l, hl⟩ := hdvd
  refine ⟨l, ?_⟩
  have hv : torusGenerator F b m hm heven ^ p.2.toAdd =
      torusDiag F b m hm heven (torusConstant F b m) ^ l := by
    rw [hl, _root_.zpow_mul, zpow_natCast, torusGenerator_pow_m]
  rw [hv] at hp'
  have hdiag : torusDiag F b m hm heven (p.1 * torusConstant F b m ^ l) = 1 := by
    change torusDiagHom F b m hm heven (p.1 * torusConstant F b m ^ l) = 1
    rw [map_mul, map_zpow]
    exact hp'
  have hc : p.1 * torusConstant F b m ^ l = 1 := torusDiag_injective F b m hm heven
    (hdiag.trans (torusDiag_one F b m hm heven).symm)
  apply Prod.ext
  · rw [_root_.zpow_neg, eq_inv_iff_mul_eq_one]
    exact hc
  · rw [← hl]
    rfl

theorem splitTorus_lift {K : Type*} [Group K] (η : Fˣ →* K) (z : K)
    (hcomm : ∀ c, z * η c = η c * z) (hz : z ^ m = η (torusConstant F b m)) :
    ∃! φ : splitTorus F b m hm heven →* K,
      (∀ c, φ ⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c⟩ = η c) ∧
      φ ⟨torusGenerator F b m hm heven, torusGenerator_mem_splitTorus F b m hm heven⟩ = z := by
  let ψ : Fˣ × Multiplicative ℤ →* K :=
    { toFun := fun p => η p.1 * z ^ p.2.toAdd
      map_one' := by simp
      map_mul' := fun p q => by
        have hc : Commute (z ^ p.2.toAdd) (η q.1) := Commute.zpow_left (hcomm q.1) _
        simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, map_mul, _root_.zpow_add]
        rw [mul_assoc (η p.1) (z ^ p.2.toAdd), ← mul_assoc (z ^ p.2.toAdd), hc.eq]
        simp only [mul_assoc] }
  have hle : (splitTorusCover F b m hm heven).ker ≤ ψ.ker := by
    intro p hp
    obtain ⟨l, rfl⟩ := splitTorusCover_ker_le F b m hm heven hp
    rw [MonoidHom.mem_ker]
    change η (torusConstant F b m ^ (-l)) * z ^ (Multiplicative.ofAdd ((m : ℤ) * l)).toAdd = 1
    rw [toAdd_ofAdd, _root_.zpow_mul, zpow_natCast, hz, map_zpow, _root_.zpow_neg, inv_mul_cancel]
  let e := QuotientGroup.quotientKerEquivOfSurjective _ (splitTorusCover_surjective F b m hm heven)
  let φ : splitTorus F b m hm heven →* K :=
    (QuotientGroup.lift _ ψ hle).comp e.symm.toMonoidHom
  have hφ : ∀ p, φ (splitTorusCover F b m hm heven p) = ψ p := by
    intro p
    change QuotientGroup.lift _ ψ hle (e.symm (splitTorusCover F b m hm heven p)) = ψ p
    have he : e.symm (splitTorusCover F b m hm heven p) = QuotientGroup.mk p := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [he, QuotientGroup.lift_mk]
  have hdiag : ∀ c, (⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c⟩ :
      splitTorus F b m hm heven) = splitTorusCover F b m hm heven (c, 1) := by
    intro c
    apply Subtype.ext
    rw [splitTorusCover_apply]
    simp
  have hgen : (⟨torusGenerator F b m hm heven, torusGenerator_mem_splitTorus F b m hm heven⟩ :
      splitTorus F b m hm heven) = splitTorusCover F b m hm heven (1, Multiplicative.ofAdd 1) := by
    apply Subtype.ext
    rw [splitTorusCover_apply]
    simp [torusDiag_one]
  refine ⟨φ, ⟨fun c => ?_, ?_⟩, ?_⟩
  · rw [hdiag, hφ]
    simp [ψ]
  · rw [hgen, hφ]
    simp [ψ]
  · rintro φ' ⟨h1, h2⟩
    apply MonoidHom.ext
    intro t
    obtain ⟨p, rfl⟩ := splitTorusCover_surjective F b m hm heven t
    rw [hφ]
    have hp : splitTorusCover F b m hm heven p = splitTorusCover F b m hm heven (p.1, 1) *
        splitTorusCover F b m hm heven (1, Multiplicative.ofAdd 1) ^ p.2.toAdd := by
      rw [← map_zpow, ← map_mul]
      congr 1
      ext
      · simp
      · simp [← ofAdd_zsmul]
    rw [hp, map_mul, map_zpow, ← hdiag, ← hgen, h1, h2]
    rfl

@[expose] noncomputable def splitTorusCharacter (η : Fˣ →* ℂˣ) (z : ℂˣ)
    (hz : z ^ m = η (torusConstant F b m)) : splitTorus F b m hm heven →* ℂˣ :=
  Classical.choose (splitTorus_lift F b m hm heven η z (fun _ => mul_comm _ _) hz)

theorem splitTorusCharacter_spec (η : Fˣ →* ℂˣ) (z : ℂˣ) (hz : z ^ m = η (torusConstant F b m)) :
    (∀ c, splitTorusCharacter F b m hm heven η z hz
        ⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c⟩ = η c) ∧
      splitTorusCharacter F b m hm heven η z hz
        ⟨torusGenerator F b m hm heven, torusGenerator_mem_splitTorus F b m hm heven⟩ = z :=
  (Classical.choose_spec (splitTorus_lift F b m hm heven η z (fun _ => mul_comm _ _) hz)).1

theorem splitTorusCharacter_unique (η : Fˣ →* ℂˣ) (z : ℂˣ)
    (hz : z ^ m = η (torusConstant F b m)) (φ : splitTorus F b m hm heven →* ℂˣ)
    (h1 : ∀ c, φ ⟨torusDiag F b m hm heven c, torusDiag_mem_splitTorus F b m hm heven c⟩ = η c)
    (h2 : φ ⟨torusGenerator F b m hm heven, torusGenerator_mem_splitTorus F b m hm heven⟩ = z) :
    φ = splitTorusCharacter F b m hm heven η z hz :=
  (Classical.choose_spec (splitTorus_lift F b m hm heven η z (fun _ => mul_comm _ _) hz)).2 φ
    ⟨h1, h2⟩

end Presentation

end CFSG.Wreathed.CentralSL2
