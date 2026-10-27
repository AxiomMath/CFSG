module

import all CFSG.Fischer.F4
public import CFSG.LieType.Chevalley.C2E6RootRestrictionTorus

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem torusWord_eq_torusWord_iff
    {n m : ℕ} (X : Fin n → Fin Tag.E6.rank)
    (Y : Fin m → Fin Tag.E6.rank) (c : Fin n → ZMod 3) (d : Fin m → ZMod 3) :
    torusWord X c = torusWord Y d ↔ ∀ l, (3 : ℤ) ∣ (∑ t, ((c t).val : ℤ) * Tag.E6.cartan (X t) l) -
      ∑ s, ((d s).val : ℤ) * Tag.E6.cartan (Y s) l := by
  rw [torusWord_eq_rootDiagUnit, torusWord_eq_rootDiagUnit]
  constructor
  · intro h l
    have h1 := congrFun (rootDiagUnit_injective h) l
    simp only [torusChar] at h1
    rw [← omegaUnit_zpow_eq_one_iff, zpow_sub, h1, mul_inv_cancel]
  · intro h
    congr 1
    funext l
    simp only [torusChar]
    rw [← mul_inv_eq_one, ← zpow_sub]
    exact (omegaUnit_zpow_eq_one_iff _).mpr (h l)

theorem torusWord_nsmul
    {n : ℕ} (X : Fin n → Fin Tag.E6.rank) (c : Fin n → ZMod 3) (k : ℕ) :
    torusWord X (k • c) = torusWord X c ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero, torusWord_zero]
  | succ k ih => rw [succ_nsmul, torusWord_add, ih, pow_succ]

theorem torusWord_mem_torusGroup
    {n : ℕ} (X : Fin n → Fin Tag.E6.rank) (c : Fin n → ZMod 3) :
    torusWord X c ∈ torusGroup Tag.E6 K := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).mp hg
  exact Subgroup.subset_closure ⟨(X t, _), rfl⟩

theorem torusWord_one
    (i : Fin Tag.E6.rank) (m : ZMod 3) :
    torusWord ![i] ![m] = torusElt Tag.E6 K i (omegaUnit ^ m.val) := by
  simp [torusWord]

theorem torusWord_two
    (i j : Fin Tag.E6.rank) (m m' : ZMod 3) :
    torusWord ![i, j] ![m, m'] =
      torusElt Tag.E6 K i (omegaUnit ^ m.val) * torusElt Tag.E6 K j (omegaUnit ^ m'.val) := by
  simp [torusWord, List.ofFn_succ]

@[expose] def torusHom6
    : Multiplicative (Fin 6 → ZMod 3) →* ModGL Tag.E6 K where
  toFun c := torusWord i6 c.toAdd
  map_one' := torusWord_zero i6
  map_mul' c d := torusWord_add i6 c.toAdd d.toAdd

theorem exists_omegaUnit_pow_eq (s : Kˣ) : ∃ m : ZMod 3, omegaUnit ^ m.val = s := by
  have h : ∀ x : K, x ≠ 0 → ∃ m : ZMod 3, ω ^ m.val = x := by decide
  obtain ⟨m, hm⟩ := h s s.ne_zero
  exact ⟨m, Units.ext (by rw [Units.val_pow_eq_pow_val, omegaUnit, Units.val_mk0, hm])⟩

theorem single_weight : ∀ (i : Fin 6) (m : ZMod 3) (l : Fin Tag.E6.rank),
    (3 : ℤ) ∣ (∑ t : Fin 1, (((![m] : Fin 1 → ZMod 3) t).val : ℤ) *
        Tag.E6.cartan ((![i6 i] : Fin 1 → Fin Tag.E6.rank) t) l) -
      ∑ s, (((Pi.single i m : Fin 6 → ZMod 3) s).val : ℤ) * Tag.E6.cartan (i6 s) l := by
  decide +kernel

theorem torusElt_eq_torusWord
    (i : Fin 6) (m : ZMod 3) :
    torusElt Tag.E6 K (i6 i) (omegaUnit ^ m.val) = torusWord i6 (Pi.single i m) := by
  rw [← torusWord_one, torusWord_eq_torusWord_iff]
  exact single_weight i m

theorem torusGroup_eq_range
    : torusGroup Tag.E6 K = torusHom6.range := by
  refine le_antisymm ?_ ?_
  · rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, s⟩, rfl⟩
    obtain ⟨m, rfl⟩ := exists_omegaUnit_pow_eq s
    exact ⟨Multiplicative.ofAdd (Pi.single i m), (torusElt_eq_torusWord i m).symm⟩
  · rintro _ ⟨c, rfl⟩
    exact torusWord_mem_torusGroup i6 c.toAdd

theorem mem_torusGroup_iff
    {h : ModGL Tag.E6 K} :
    h ∈ torusGroup Tag.E6 K ↔ ∃ c : Fin 6 → ZMod 3, h = torusWord i6 c := by
  rw [torusGroup_eq_range]
  exact ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc.symm⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem torusWord6_eq_iff
    (c d : Fin 6 → ZMod 3) :
    torusWord i6 c = torusWord i6 d ↔
      c - d = 0 ∨ c - d = ![1, 0, 2, 0, 1, 2] ∨ c - d = ![2, 0, 1, 0, 2, 1] := by
  rw [← torusWord6_eq_one_iff, show c = (c - d) + d by abel, torusWord_add, add_sub_cancel_right]
  exact ⟨fun h => mul_right_cancel (h.trans (one_mul _).symm), fun h => by rw [h, one_mul]⟩

abbrev stdTorus0
    : Subgroup (ModGL Tag.E6 K) := graphFixedTorus TwistTag.E6 K barHom

abbrev stdBorel0
    : Subgroup (ModGL Tag.E6 K) := graphFixedBorel TwistTag.E6 K barHom

abbrev stdUnipotent0
    : Subgroup (ModGL Tag.E6 K) := graphFixedPosUnipotent TwistTag.E6 K barHom

theorem units_map_barHom_omegaUnit : Units.map barHom.toMonoidHom omegaUnit = omegaUnit ^ 2 := by
  ext
  rw [Units.coe_map, Units.val_pow_eq_pow_val, omegaUnit, Units.val_mk0]
  rfl

theorem twistHom_torusWord
    (c : Fin 6 → ZMod 3) :
    twistHom TwistTag.E6 K barHom (torusWord i6 c) = rootDiagUnit Tag.E6 fun l =>
      omegaUnit ^ (2 * ∑ t, ((c t).val : ℤ) * Tag.E6.cartan (i6 t) (TwistTag.E6.perm.symm l)) := by
  rw [torusWord_eq_rootDiagUnit]
  erw [twistHom_rootDiagUnit_eq]
  congr 1
  funext l
  simp only [torusChar]
  rw [map_zpow, units_map_barHom_omegaUnit, ← zpow_natCast, ← zpow_mul]
  rfl

theorem torusWord_mem_adjointGroup
    {n : ℕ} (X : Fin n → Fin Tag.E6.rank) (c : Fin n → ZMod 3) :
    torusWord X c ∈ adjointGroup TwistTag.E6.tag K := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).mp hg
  exact torusElt_mem_adjointGroup (τ := TwistTag.E6.tag) (X t) _

theorem torusWord_mem_stdFixedGroup_iff
    (c : Fin 6 → ZMod 3) :
    torusWord i6 c ∈ stdFixedGroup ↔ ∀ l : Fin Tag.E6.rank,
      (3 : ℤ) ∣ 2 * (∑ t, ((c t).val : ℤ) * Tag.E6.cartan (i6 t) (TwistTag.E6.perm.symm l)) -
        ∑ t, ((c t).val : ℤ) * Tag.E6.cartan (i6 t) l := by
  have hC := torusWord_mem_adjointGroup i6 c
  refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).trans
    ⟨fun h' l => ?_, fun h => ⟨hC, ?_⟩⟩
  · have h2 := h'.2
    rw [twistHom_torusWord, torusWord_eq_rootDiagUnit] at h2
    have h1 := congrFun (rootDiagUnit_injective h2) l
    simp only [torusChar] at h1
    rw [← omegaUnit_zpow_eq_one_iff, zpow_sub, h1, mul_inv_cancel]
  · rw [twistHom_torusWord, torusWord_eq_rootDiagUnit]
    congr 1
    funext l
    simp only [torusChar]
    rw [← mul_inv_eq_one, ← zpow_sub]
    exact (omegaUnit_zpow_eq_one_iff _).mpr (h l)

theorem fixed_iff : ∀ c : Fin 6 → ZMod 3,
    (∀ l : Fin Tag.E6.rank,
      (3 : ℤ) ∣ 2 * (∑ t, ((c t).val : ℤ) * Tag.E6.cartan (i6 t) (TwistTag.E6.perm.symm l)) -
        ∑ t, ((c t).val : ℤ) * Tag.E6.cartan (i6 t) l) ↔
      ∃ a b : ZMod 3, c = ![a, 0, b, 0, 2 * b, 2 * a] := by
  decide +kernel

theorem torusWord_mem_stdTorus0_iff
    (c : Fin 6 → ZMod 3) :
    torusWord i6 c ∈ stdTorus0 ↔
      ∃ a b : ZMod 3, c = ![a, 0, b, 0, 2 * b, 2 * a] := by
  rw [← fixed_iff, ← torusWord_mem_stdFixedGroup_iff]
  exact ⟨fun h => h.2, fun h => ⟨torusWord_mem_torusGroup i6 c, h⟩⟩

theorem mem_stdTorus0_iff
    {h : ModGL Tag.E6 K} :
    h ∈ stdTorus0 ↔
      ∃ a b : ZMod 3, h = torusWord i6 ![a, 0, b, 0, 2 * b, 2 * a] := by
  constructor
  · intro hh
    obtain ⟨c, rfl⟩ := mem_torusGroup_iff.mp hh.1
    obtain ⟨a, b, rfl⟩ := (torusWord_mem_stdTorus0_iff c).mp hh
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact (torusWord_mem_stdTorus0_iff _).mpr ⟨a, b, rfl⟩

@[expose] def fixedTorusGen
    : ModGL Tag.E6 K :=
  torusElt Tag.E6 K (i6 2) omegaUnit * torusElt Tag.E6 K (i6 4) (omegaUnit ^ 2)

theorem fixedTorusGen_eq
    : fixedTorusGen = torusWord i6 ![0, 0, 1, 0, 2, 0] := by
  have h : fixedTorusGen = torusWord ![i6 2, i6 4] ![1, 2] := by
    rw [torusWord_two, fixedTorusGen]
    rfl
  rw [h, torusWord_eq_torusWord_iff]
  decide +kernel

theorem gen_weight : ∀ a b : ZMod 3, ∀ l : Fin Tag.E6.rank,
    (3 : ℤ) ∣ (∑ t, (((![a, 0, b, 0, 2 * b, 2 * a] : Fin 6 → ZMod 3) t).val : ℤ) *
        Tag.E6.cartan (i6 t) l) -
      ∑ t, ((((a + b).val • ![0, 0, 1, 0, 2, 0] : Fin 6 → ZMod 3) t).val : ℤ) *
        Tag.E6.cartan (i6 t) l := by
  decide +kernel

theorem torusWord_fixed_eq_pow
    (a b : ZMod 3) :
    torusWord i6 ![a, 0, b, 0, 2 * b, 2 * a] = fixedTorusGen ^ (a + b).val := by
  rw [fixedTorusGen_eq, ← torusWord_nsmul, torusWord_eq_torusWord_iff]
  exact gen_weight a b

theorem fixedTorusGen_mem_stdTorus0 :
    fixedTorusGen ∈ stdTorus0 := by
  rw [fixedTorusGen_eq, torusWord_mem_stdTorus0_iff]
  exact ⟨0, 1, by decide⟩

theorem stdTorus0_eq_zpowers :
    stdTorus0 = Subgroup.zpowers fixedTorusGen := by
  refine le_antisymm (fun h hh => ?_) ?_
  · obtain ⟨a, b, rfl⟩ := mem_stdTorus0_iff.mp hh
    rw [torusWord_fixed_eq_pow]
    exact Subgroup.npow_mem_zpowers _ _
  · exact Subgroup.zpowers_le.mpr fixedTorusGen_mem_stdTorus0

theorem fixedTorusGen_ne_one
    : fixedTorusGen ≠ 1 := by
  rw [fixedTorusGen_eq, Ne, torusWord6_eq_one_iff]
  decide

theorem fixedTorusGen_pow_three
    : fixedTorusGen ^ 3 = 1 := by
  rw [fixedTorusGen_eq, ← torusWord_nsmul, torusWord6_eq_one_iff]
  decide

theorem orderOf_fixedTorusGen
    : orderOf fixedTorusGen = 3 :=
  orderOf_eq_prime fixedTorusGen_pow_three fixedTorusGen_ne_one

theorem card_stdTorus0 :
    Nat.card stdTorus0 = 3 := by
  rw [stdTorus0_eq_zpowers]
  exact (Nat.card_zpowers fixedTorusGen).trans orderOf_fixedTorusGen

theorem mem_orbitField_E3 (c : K) : c ∈ orbitField TwistTag.E6 K barHom (foldedIndex 2) := by
  rw [mem_orbitField, show (TwistTag.E6.orbit (foldedIndex 2)).card = 2 by decide, pow_two,
    RingHom.coe_mul, Function.comp_apply]
  exact bar_bar c

@[expose] def omegaOrbitUnit : (orbitField TwistTag.E6 K barHom (foldedIndex 2))ˣ :=
  Units.mk0 ⟨ω, mem_orbitField_E3 ω⟩ fun h => absurd (congrArg Subtype.val h) (by decide)

theorem perm_pow_orbitMin_E3_zero :
    (TwistTag.E6.perm ^ 0) (TwistTag.E6.orbitMin (foldedIndex 2)) = i6 2 :=
  (by decide : (TwistTag.E6.perm ^ 0) (TwistTag.E6.orbitMin (foldedIndex 2)) =
    (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank))

theorem perm_pow_orbitMin_E3_one :
    (TwistTag.E6.perm ^ 1) (TwistTag.E6.orbitMin (foldedIndex 2)) = i6 4 :=
  (by decide : (TwistTag.E6.perm ^ 1) (TwistTag.E6.orbitMin (foldedIndex 2)) =
    (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank))

theorem units_map_zero_omegaOrbitUnit :
    Units.map ((barHom ^ 0).comp (orbitField TwistTag.E6 K barHom (foldedIndex 2)).subtype
      ).toMonoidHom omegaOrbitUnit = omegaUnit := by
  ext
  rw [Units.coe_map, pow_zero]
  rfl

theorem units_map_one_omegaOrbitUnit :
    Units.map ((barHom ^ 1).comp (orbitField TwistTag.E6 K barHom (foldedIndex 2)).subtype
      ).toMonoidHom omegaOrbitUnit = omegaUnit ^ 2 := by
  ext
  rw [Units.coe_map, pow_one, Units.val_pow_eq_pow_val, omegaUnit, Units.val_mk0]
  rfl

theorem orbitH_omegaOrbitUnit :
    (orbitH TwistTag.E6 K barHom (foldedIndex 2) omegaOrbitUnit : ModGL TwistTag.E6.tag K) =
      fixedTorusGen := by
  rw [coe_orbitH, show (TwistTag.E6.orbit (foldedIndex 2)).card = 2 by decide,
    show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_cons, List.prod_nil, mul_one, perm_pow_orbitMin_E3_zero,
    perm_pow_orbitMin_E3_one, units_map_zero_omegaOrbitUnit, units_map_one_omegaOrbitUnit]
  rfl

theorem fixedTorusGen_mem_stdGroup :
    fixedTorusGen ∈ stdGroup := by
  have h := orbitH_mem_graphFixedRootGroup TwistTag.E6 barHom (foldedIndex 2) omegaOrbitUnit
  rw [orbitH_omegaOrbitUnit] at h
  exact h

theorem fixedTorusGen_mem_torusA
    : fixedTorusGen ∈ torusA :=
  mul_mem (Subgroup.subset_closure ⟨i6 2, Or.inr (Or.inl rfl), _, rfl⟩)
    (Subgroup.subset_closure ⟨i6 4, Or.inr (Or.inr (Or.inr (Or.inl rfl))), _, rfl⟩)

theorem fixedTorusGen_mem_torusD
    : fixedTorusGen ∈ torusD :=
  mul_mem (Subgroup.subset_closure ⟨i6 2, Or.inr (Or.inl rfl), _, rfl⟩)
    (Subgroup.subset_closure ⟨i6 4, Or.inr (Or.inr (Or.inr rfl)), _, rfl⟩)

theorem stdTorus0_le_groupA_inf_groupD :
    stdTorus0 ≤ groupA ⊓ groupD := by
  rw [stdTorus0_eq_zpowers]
  exact Subgroup.zpowers_le.mpr
    ⟨subsystemTorus_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setA) fixedTorusGen_mem_torusA,
      subsystemTorus_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setD)
        fixedTorusGen_mem_torusD⟩

theorem stdTorus0_le_stdGroup :
    stdTorus0 ≤ stdGroup := by
  rw [stdTorus0_eq_zpowers]
  exact Subgroup.zpowers_le.mpr fixedTorusGen_mem_stdGroup

theorem barHom_surjective : Function.Surjective barHom := fun c => ⟨barHom c, bar_bar c⟩

theorem stdFixedGroup_eq_stdGroup :
    stdFixedGroup = stdGroup := by
  rw [stdFixedGroup, twistedFixedGroup_eq_sup_graphFixedTorus barHom_surjective]
  exact sup_eq_right.mpr stdTorus0_le_stdGroup

theorem stdTorus0_eq_stdTorus :
    stdTorus0 = stdTorus :=
  (inf_eq_left.mpr stdTorus0_le_stdGroup).symm

theorem stdBorel_eq_stdBorel0 :
    stdBorel = stdBorel0 :=
  inf_eq_left.mpr ((graphFixedBorel_le TwistTag.E6 K barHom).trans stdFixedGroup_eq_stdGroup.le)

end CFSG.LieType.Chevalley.C2E6Std
