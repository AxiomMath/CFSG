module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace UnitaryFieldData

variable {p f : ℕ} {K : Type*} [Field K]

theorem one_lt_pow (h : UnitaryFieldData p f K) : 1 < p ^ f :=
  Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt

theorem card_eq_sq (h : UnitaryFieldData p f K) : Nat.card K = (p ^ f) ^ 2 := by
  rw [h.card, ← pow_mul, mul_comm]

theorem bar_eq_zero_iff (h : UnitaryFieldData p f K) {c : K} : h.bar c = 0 ↔ c = 0 :=
  map_eq_zero h.bar

theorem norm_mem_fixedField (h : UnitaryFieldData p f K) (c : K) : h.norm c ∈ h.fixedField := by
  rw [mem_fixedField, norm, map_mul, bar_bar, mul_comm]

theorem norm_eq_pow (h : UnitaryFieldData p f K) (c : K) : h.norm c = c ^ (p ^ f + 1) := by
  rw [norm, bar_apply, pow_succ']

@[expose] noncomputable def normHom (h : UnitaryFieldData p f K) : K →* h.fixedField where
  toFun c := ⟨h.norm c, h.norm_mem_fixedField c⟩
  map_one' := Subtype.ext (by simp [norm])
  map_mul' a b := Subtype.ext (by simp only [norm, map_mul, Subfield.coe_mul]; ring)

@[simp] theorem coe_normHom (h : UnitaryFieldData p f K) (c : K) :
    (h.normHom c : K) = h.norm c :=
  rfl

theorem mem_ker_normUnits (h : UnitaryFieldData p f K) {u : Kˣ} :
    u ∈ (Units.map h.normHom).ker ↔ h.norm u = 1 := by
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one, Subtype.ext_iff,
    coe_normHom, OneMemClass.coe_one]

theorem ker_normUnits (h : UnitaryFieldData p f K) :
    (Units.map h.normHom).ker = rootsOfUnity (p ^ f + 1) K := by
  ext u
  rw [mem_ker_normUnits, mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
    norm_eq_pow]

theorem card_units_fixedField_le (h : UnitaryFieldData p f K) :
    Nat.card h.fixedFieldˣ ≤ p ^ f - 1 := by
  have := h.finite
  have hq := h.one_lt_pow
  have : NeZero (p ^ f - 1) := ⟨by omega⟩
  let φ : h.fixedFieldˣ →* Kˣ := Units.map h.fixedField.subtype.toMonoidHom
  have hφ : Function.Injective φ := Units.map_injective h.fixedField.subtype_injective
  have hmem : ∀ u : h.fixedFieldˣ, φ u ∈ rootsOfUnity (p ^ f - 1) K := by
    intro u
    rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
    have hu : h.bar ((u : h.fixedField) : K) = (u : h.fixedField) := (u : h.fixedField).2
    have hu0 : ((u : h.fixedField) : K) ≠ 0 := by
      simp
    rw [bar_apply, ← Nat.sub_add_cancel hq.le, pow_succ] at hu
    exact mul_eq_right₀ hu0 |>.mp hu
  calc Nat.card h.fixedFieldˣ ≤ Nat.card (rootsOfUnity (p ^ f - 1) K) :=
        Nat.card_le_card_of_injective (fun u => ⟨φ u, hmem u⟩)
          fun a b hab => hφ (congrArg Subtype.val hab)
    _ ≤ p ^ f - 1 := card_rootsOfUnity K _

theorem card_ker_normUnits_and_surjective (h : UnitaryFieldData p f K) :
    Nat.card (Units.map h.normHom).ker = p ^ f + 1 ∧ Function.Surjective (Units.map h.normHom) := by
  have := h.finite
  have hq := h.one_lt_pow
  have hK : Nat.card Kˣ = (p ^ f + 1) * (p ^ f - 1) := by
    rw [Nat.card_units, h.card_eq_sq]
    zify [hq.le, Nat.one_le_pow 2 (p ^ f) (by omega)]
    ring
  have h1 : Nat.card (Units.map h.normHom).ker ≤ p ^ f + 1 := by
    rw [ker_normUnits]
    exact card_rootsOfUnity K _
  have h2 : Nat.card (Units.map h.normHom).range ≤ p ^ f - 1 :=
    (Subgroup.card_le_card_group _).trans h.card_units_fixedField_le
  have h3 := Subgroup.card_mul_index (Units.map h.normHom).ker
  rw [Subgroup.index_ker, hK] at h3
  have hker : Nat.card (Units.map h.normHom).ker = p ^ f + 1 := by
    by_contra hne
    have hlt : Nat.card (Units.map h.normHom).ker < p ^ f + 1 := lt_of_le_of_ne h1 hne
    have : Nat.card (Units.map h.normHom).ker * Nat.card (Units.map h.normHom).range <
        (p ^ f + 1) * (p ^ f - 1) :=
      calc _ ≤ Nat.card (Units.map h.normHom).ker * (p ^ f - 1) := Nat.mul_le_mul_left _ h2
        _ < (p ^ f + 1) * (p ^ f - 1) := Nat.mul_lt_mul_of_pos_right hlt (by omega)
    omega
  have hrange : Nat.card (Units.map h.normHom).range = p ^ f - 1 := by
    rw [hker] at h3
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  refine ⟨hker, MonoidHom.range_eq_top.mp ((Subgroup.card_eq_iff_eq_top _).mp ?_)⟩
  exact le_antisymm (Subgroup.card_le_card_group _) (hrange ▸ h.card_units_fixedField_le)

theorem card_fixedField (h : UnitaryFieldData p f K) : Nat.card h.fixedField = p ^ f := by
  have := h.finite
  have hq := h.one_lt_pow
  have hsurj := h.card_ker_normUnits_and_surjective.2
  have hrange : Nat.card (Units.map h.normHom).range = Nat.card h.fixedFieldˣ := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  have h3 := Subgroup.card_mul_index (Units.map h.normHom).ker
  rw [Subgroup.index_ker, hrange, h.card_ker_normUnits_and_surjective.1, Nat.card_units,
    Nat.card_units, h.card_eq_sq] at h3
  have hpos : 0 < Nat.card h.fixedField := Nat.card_pos
  have hsq : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
    zify [hq.le, Nat.one_le_pow 2 (p ^ f) (by omega)]
    ring
  rw [hsq] at h3
  have := Nat.eq_of_mul_eq_mul_left (by omega) h3
  omega

theorem normHom_surjective (h : UnitaryFieldData p f K) : Function.Surjective h.normHom := by
  intro a
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha]; exact Subtype.ext (by simp [norm])⟩
  · obtain ⟨u, hu⟩ := h.card_ker_normUnits_and_surjective.2 (Units.mk0 a ha)
    exact ⟨u, by simpa using congrArg Units.val hu⟩

theorem norm_div_bar (h : UnitaryFieldData p f K) {r : K} (hr : r ≠ 0) :
    h.norm (r / h.bar r) = 1 := by
  have hr' : h.bar r ≠ 0 := (h.bar_eq_zero_iff).not.mpr hr
  rw [norm, map_div₀, bar_bar]
  field_simp

theorem exists_div_bar_eq (h : UnitaryFieldData p f K) {u : K} (hu : h.norm u = 1) :
    ∃ r : K, r ≠ 0 ∧ r / h.bar r = u := by
  have hex : ∃ x : K, x + u * h.bar x ≠ 0 := by
    by_contra! hz
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    have h1 := hz 1
    have h2 := hz c
    rw [map_one, mul_one] at h1
    exact hc (by linear_combination h.bar c * h1 - h2)
  obtain ⟨x, hx⟩ := hex
  have hu' : u * h.bar u = 1 := hu
  have hb : u * h.bar (x + u * h.bar x) = x + u * h.bar x := by
    rw [map_add, map_mul, bar_bar]
    linear_combination x * hu'
  have hb0 : h.bar (x + u * h.bar x) ≠ 0 := (h.bar_eq_zero_iff).not.mpr hx
  exact ⟨x + u * h.bar x, hx, (div_eq_iff hb0).mpr hb.symm⟩

end UnitaryFieldData

theorem unitary_field_norm {p f : ℕ} {K : Type*} [Field K] (h : UnitaryFieldData p f K) :
    Function.Surjective h.normHom ∧ Function.Surjective (Units.map h.normHom) ∧
      Nat.card (Units.map h.normHom).ker = p ^ f + 1 ∧
      Set.range (fun r : Kˣ => r / Units.map (h.bar : K →* K) r) = {u : Kˣ | h.norm u = 1} := by
  refine ⟨h.normHom_surjective, h.card_ker_normUnits_and_surjective.2,
    h.card_ker_normUnits_and_surjective.1, Set.ext fun u => ⟨?_, fun hu => ?_⟩⟩
  · rintro ⟨r, rfl⟩
    simp only [Set.mem_ofPred_eq, Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_ofClass]
    exact h.norm_div_bar r.ne_zero
  · obtain ⟨r, hr, hru⟩ := h.exists_div_bar_eq hu
    exact ⟨Units.mk0 r hr, Units.ext (by simpa using hru)⟩

end CFSG.LocalAnalysis.ComponentInitial
