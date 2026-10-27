module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY4Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.SmallF3.FritzII

abbrev fz21b_X : Type := Multiplicative (ZMod 2 × ZMod 4 × ZMod 4)

abbrev fz21b_X0 : Subgroup fz21b_X := (powMonoidHom 2 : fz21b_X →* fz21b_X).ker

abbrev fz21b_Z : Subgroup fz21b_X := (powMonoidHom 2 : fz21b_X →* fz21b_X).range

instance : DecidablePred (· ∈ fz21b_X0) :=
  inferInstanceAs (DecidablePred (· ∈ (powMonoidHom 2 : fz21b_X →* fz21b_X).ker))

instance : DecidablePred (· ∈ fz21b_Z) :=
  inferInstanceAs (DecidablePred (· ∈ (powMonoidHom 2 : fz21b_X →* fz21b_X).range))

instance : Fintype fz21b_Z := inferInstance

instance : Fintype fz21b_X0 := inferInstance

lemma fz21b_X0_card : Nat.card fz21b_X0 = 8 := by
  rw [Nat.card_eq_fintype_card]; decide

lemma fz21b_Z_card : Nat.card fz21b_Z = 4 := by
  rw [Nat.card_eq_fintype_card]; decide

lemma fz21b_Z_aut_card : Nat.card (MulAut fz21b_Z) = 6 := by
  rw [Nat.card_eq_fintype_card]; decide

lemma fz21b_X_pow_four : ∀ x : fz21b_X, x ^ 4 = 1 := by decide

lemma fz21b_Z_le_X0 : fz21b_Z ≤ fz21b_X0 := by
  intro z hz
  rw [fz21b_Z, MonoidHom.mem_range] at hz
  obtain ⟨y, rfl⟩ := hz
  rw [fz21b_X0, MonoidHom.mem_ker]
  change (y ^ 2 : fz21b_X) ^ 2 = 1
  have h : (y ^ 2 : fz21b_X) ^ 2 = y ^ 4 := by rw [← pow_mul]
  rw [h]; exact fz21b_X_pow_four y

instance : fz21b_Z.Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  exact MulEquiv.map_range_powMonoidHom e 2

lemma fz21b_X0_index : Nat.card (fz21b_X0 ⧸ fz21b_Z.subgroupOf fz21b_X0) = 2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (fz21b_Z.subgroupOf fz21b_X0)
  have hZ : Nat.card (fz21b_Z.subgroupOf fz21b_X0) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe fz21b_Z_le_X0).toEquiv]
    exact fz21b_Z_card
  rw [fz21b_X0_card, hZ] at h
  omega

end CFSG.OddStandard.SmallF3.FritzII
