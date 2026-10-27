module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}
private lemma zmod4_val_one : (1 : ZMod 4).val = 1 := by rw [ZMod.val_one_eq_one_mod]

private lemma zmod4_val_zero : (0 : ZMod 4).val = 0 := ZMod.val_zero

private lemma zpow_val_add {g : G} (hg : orderOf g = 4) (x y : ZMod 4) :
    g ^ ((x + y).val) = g ^ x.val * g ^ y.val := by
  have hmod : (x.val + y.val) % 4 = (x.val + y.val) % orderOf g := by rw [hg]
  rw [ZMod.val_add, hmod, pow_mod_orderOf, pow_add]

private lemma zpow_mul_rearrange {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (i j k i' j' k' : ℕ) :
    a ^ i * b ^ j * c ^ k * (a ^ i' * b ^ j' * c ^ k')
      = a ^ i * a ^ i' * b ^ j * b ^ j' * c ^ k * c ^ k' := by
  have h1 : c ^ k * a ^ i' = a ^ i' * c ^ k := (hac.pow_pow i' k).symm.eq
  have h2 : b ^ j * a ^ i' = a ^ i' * b ^ j := (hab.pow_pow i' j).symm.eq
  have h3 : c ^ k * b ^ j' = b ^ j' * c ^ k := (hbc.pow_pow j' k).symm.eq
  calc
    a ^ i * b ^ j * c ^ k * (a ^ i' * b ^ j' * c ^ k')
        = a ^ i * b ^ j * (c ^ k * a ^ i') * b ^ j' * c ^ k' := by group
    _ = a ^ i * b ^ j * (a ^ i' * c ^ k) * b ^ j' * c ^ k' := by rw [h1]
    _ = a ^ i * (b ^ j * a ^ i') * c ^ k * b ^ j' * c ^ k' := by group
    _ = a ^ i * (a ^ i' * b ^ j) * c ^ k * b ^ j' * c ^ k' := by rw [h2]
    _ = a ^ i * a ^ i' * b ^ j * (c ^ k * b ^ j') * c ^ k' := by group
    _ = a ^ i * a ^ i' * b ^ j * (b ^ j' * c ^ k) * c ^ k' := by rw [h3]
    _ = a ^ i * a ^ i' * b ^ j * b ^ j' * c ^ k * c ^ k' := by group

private noncomputable def z4powHom {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (ha : orderOf a = 4) (hb : orderOf b = 4) (hc : orderOf c = 4) :
    Outside.Z4pow 3 →* G :=
  MonoidHom.mk' (fun f =>
      a ^ (Multiplicative.toAdd f 0).val * b ^ (Multiplicative.toAdd f 1).val *
        c ^ (Multiplicative.toAdd f 2).val) (by
    intro f g
    have h0 : (Multiplicative.toAdd (f * g) 0).val
        = ((Multiplicative.toAdd f 0) + (Multiplicative.toAdd g 0)).val := rfl
    have h1 : (Multiplicative.toAdd (f * g) 1).val
        = ((Multiplicative.toAdd f 1) + (Multiplicative.toAdd g 1)).val := rfl
    have h2 : (Multiplicative.toAdd (f * g) 2).val
        = ((Multiplicative.toAdd f 2) + (Multiplicative.toAdd g 2)).val := rfl
    rw [h0, h1, h2, zpow_val_add ha, zpow_val_add hb, zpow_val_add hc]
    rw [zpow_mul_rearrange hab hac hbc]
    group)

private lemma z4powHom_apply {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (ha : orderOf a = 4) (hb : orderOf b = 4) (hc : orderOf c = 4)
    (f : Outside.Z4pow 3) :
    z4powHom hab hac hbc ha hb hc f =
      a ^ (Multiplicative.toAdd f 0).val * b ^ (Multiplicative.toAdd f 1).val *
        c ^ (Multiplicative.toAdd f 2).val := rfl

private lemma z4powHom_injective {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (ha : orderOf a = 4) (hb : orderOf b = 4) (hc : orderOf c = 4)
    (h1 : zpowers a ⊓ zpowers b = ⊥) (h2 : (zpowers a ⊔ zpowers b) ⊓ zpowers c = ⊥) :
    Function.Injective (z4powHom hab hac hbc ha hb hc) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  rw [z4powHom_apply] at hf
  have hck_inf : c ^ (Multiplicative.toAdd f 2).val ∈
      (zpowers a ⊔ zpowers b) ⊓ zpowers c := by
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.npow_mem_zpowers c _⟩
    have heq : c ^ (Multiplicative.toAdd f 2).val =
        (a ^ (Multiplicative.toAdd f 0).val * b ^ (Multiplicative.toAdd f 1).val)⁻¹ :=
      eq_inv_of_mul_eq_one_right hf
    rw [heq]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers a _))
      (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers b _)))
  have hck_one : c ^ (Multiplicative.toAdd f 2).val = 1 := by
    have hh := hck_inf
    rw [h2] at hh
    simpa using hh
  have hklt : (Multiplicative.toAdd f 2).val < 4 := by
    simpa using ZMod.val_lt (Multiplicative.toAdd f 2)
  have hkvd : 4 ∣ (Multiplicative.toAdd f 2).val := by
    have hh := (orderOf_dvd_iff_pow_eq_one (x := c)
      (n := (Multiplicative.toAdd f 2).val)).mpr hck_one
    simpa [hc] using hh
  have hk : (Multiplicative.toAdd f 2).val = 0 := Nat.eq_zero_of_dvd_of_lt hkvd hklt
  have hab_one : a ^ (Multiplicative.toAdd f 0).val * b ^ (Multiplicative.toAdd f 1).val = 1 := by
    have hh := hf
    rw [hck_one, mul_one] at hh
    exact hh
  have hbj : b ^ (Multiplicative.toAdd f 1).val = 1 := by
    have hmem : b ^ (Multiplicative.toAdd f 1).val ∈ zpowers a ⊓ zpowers b := by
      refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.npow_mem_zpowers b _⟩
      have heq : b ^ (Multiplicative.toAdd f 1).val =
          (a ^ (Multiplicative.toAdd f 0).val)⁻¹ :=
        eq_inv_of_mul_eq_one_right hab_one
      rw [heq]
      exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers a _)
    have hh := hmem
    rw [h1] at hh
    simpa using hh
  have hjlt : (Multiplicative.toAdd f 1).val < 4 := by
    simpa using ZMod.val_lt (Multiplicative.toAdd f 1)
  have hjvd : 4 ∣ (Multiplicative.toAdd f 1).val := by
    have hh := (orderOf_dvd_iff_pow_eq_one (x := b)
      (n := (Multiplicative.toAdd f 1).val)).mpr hbj
    simpa [hb] using hh
  have hj : (Multiplicative.toAdd f 1).val = 0 := Nat.eq_zero_of_dvd_of_lt hjvd hjlt
  have hai : a ^ (Multiplicative.toAdd f 0).val = 1 := by
    have hh := hab_one
    rw [hbj, mul_one] at hh
    exact hh
  have hilt : (Multiplicative.toAdd f 0).val < 4 := by
    simpa using ZMod.val_lt (Multiplicative.toAdd f 0)
  have hivd : 4 ∣ (Multiplicative.toAdd f 0).val := by
    have hh := (orderOf_dvd_iff_pow_eq_one (x := a)
      (n := (Multiplicative.toAdd f 0).val)).mpr hai
    simpa [ha] using hh
  have hi : (Multiplicative.toAdd f 0).val = 0 := Nat.eq_zero_of_dvd_of_lt hivd hilt
  have h0 : Multiplicative.toAdd f 0 = 0 := (ZMod.val_eq_zero _).mp hi
  have h1' : Multiplicative.toAdd f 1 = 0 := (ZMod.val_eq_zero _).mp hj
  have h2' : Multiplicative.toAdd f 2 = 0 := (ZMod.val_eq_zero _).mp hk
  have hF : Multiplicative.toAdd f = 0 := by
    funext x
    fin_cases x
    · exact h0
    · exact h1'
    · exact h2'
  rw [← ofAdd_toAdd f, hF]
  rfl

private lemma z4powHom_range {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (ha : orderOf a = 4) (hb : orderOf b = 4) (hc : orderOf c = 4) :
    (z4powHom hab hac hbc ha hb hc).range =
      zpowers a ⊔ zpowers b ⊔ zpowers c := by
  apply le_antisymm
  · rintro x ⟨f, rfl⟩
    rw [z4powHom_apply]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.npow_mem_zpowers a _)))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers b _))))
      (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers c _))
  · apply sup_le
    · apply sup_le
      · rw [Subgroup.zpowers_le]
        refine ⟨Multiplicative.ofAdd (Pi.single 0 1), ?_⟩
        rw [z4powHom_apply]
        simp [Pi.single_eq_same, Pi.single_eq_of_ne, zmod4_val_one, zmod4_val_zero]
      · rw [Subgroup.zpowers_le]
        refine ⟨Multiplicative.ofAdd (Pi.single 1 1), ?_⟩
        rw [z4powHom_apply]
        simp [Pi.single_eq_same, Pi.single_eq_of_ne, zmod4_val_one, zmod4_val_zero]
    · rw [Subgroup.zpowers_le]
      refine ⟨Multiplicative.ofAdd (Pi.single 2 1), ?_⟩
      rw [z4powHom_apply]
      simp [Pi.single_eq_same, Pi.single_eq_of_ne, zmod4_val_one, zmod4_val_zero]

theorem q13d_exists_mulEquiv_Z4cube {a b c : G} (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (ha : orderOf a = 4) (hb : orderOf b = 4) (hc : orderOf c = 4)
    (h1 : zpowers a ⊓ zpowers b = ⊥) (h2 : (zpowers a ⊔ zpowers b) ⊓ zpowers c = ⊥) :
    Nonempty (↥(zpowers a ⊔ zpowers b ⊔ zpowers c) ≃* Outside.Z4pow 3) := by
  have hab' : Commute a b := hab
  have hac' : Commute a c := hac
  have hbc' : Commute b c := hbc
  have hinj : Function.Injective (z4powHom hab' hac' hbc' ha hb hc) :=
    z4powHom_injective hab' hac' hbc' ha hb hc h1 h2
  have hrange : (z4powHom hab' hac' hbc' ha hb hc).range =
      zpowers a ⊔ zpowers b ⊔ zpowers c :=
    z4powHom_range hab' hac' hbc' ha hb hc
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
