module

public import CFSG.GH74.Uniqueness.Section15HeringDefs

public section

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup MulAction

variable {F : Type*} [Field F] {G : Type*} [Group G] [MulAction G F] {m : ℕ}

theorem exists_mulSubgroup_smul_eq (hG : Hyp G F m) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ k ∈ mulSubgroup G F, k • x = y := by
  obtain ⟨k, hk, hkx⟩ := exists_mulSubgroup hG (Units.mk0 (y / x) (div_ne_zero hy hx))
  exact ⟨k, hk, by rw [hkx, Units.val_mk0, div_mul_cancel₀ y hx]⟩

theorem Hyp.isPretransitive (hG : Hyp G F m) : IsPretransitive G F :=
  (isPreprimitive_of_is_two_pretransitive hG.twoTrans).toIsPretransitive

theorem Hyp.card_group [Finite G] (hG : Hyp G F m) :
    Nat.card G = 2 ^ m * Nat.card (stabilizer G (0 : F)) := by
  have := hG.isPretransitive
  rw [← Subgroup.card_mul_index (stabilizer G (0 : F)), index_stabilizer, orbit_eq_univ,
    Set.ncard_univ, hG.card, mul_comm]

theorem Hyp.card_stabilizer [Finite F] [Finite G] (hG : Hyp G F m) :
    Nat.card (stabilizer G (0 : F)) = (2 ^ m - 1) * Nat.card (stab01 G F) := by
  set H := stabilizer G (0 : F) with hH
  have horbit : orbit H (1 : F) = {x : F | x ≠ 0} := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact smul_one_ne_zero (h.2 : (h : G) • (0 : F) = 0)
    · intro hx
      obtain ⟨k, hk, hkx⟩ := exists_mulSubgroup_smul_eq hG one_ne_zero hx
      exact ⟨⟨k, mulSubgroup_le_stabilizer hk⟩, hkx⟩
  have hcard_orbit : (orbit H (1 : F)).ncard = 2 ^ m - 1 := by
    rw [horbit, show {x : F | x ≠ 0} = ({0} : Set F)ᶜ from rfl, Set.ncard_compl,
      Set.ncard_singleton, hG.card]
  have hstab : Nat.card (stabilizer H (1 : F)) = Nat.card (stab01 G F) := by
    rw [← stabilizer_subgroupOf, ← inf_subgroupOf_left]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : stab01 G F ≤ H)).toEquiv
  rw [← Subgroup.card_mul_index (stabilizer H (1 : F)), index_stabilizer, hcard_orbit, hstab,
    mul_comm]

theorem Hyp.isMultiplyPretransitive_of_le (hG : Hyp G F m) (X₀ : Subgroup G)
    (hK : mulSubgroup G F ≤ X₀) (hmove : ∃ g ∈ X₀, g • (0 : F) ≠ 0) :
    IsMultiplyPretransitive X₀ F 2 := by
  obtain ⟨g₀, hg₀, hg₀0⟩ := hmove
  have hto0 : ∀ x : F, ∃ g ∈ X₀, g • x = 0 := by
    intro x
    by_cases hx : x = 0
    · exact ⟨1, X₀.one_mem, by rw [hx, one_smul]⟩
    · obtain ⟨k, hk, hkx⟩ := exists_mulSubgroup_smul_eq hG hx hg₀0
      refine ⟨g₀⁻¹ * k, X₀.mul_mem (X₀.inv_mem hg₀) (hK hk), ?_⟩
      rw [mul_smul, hkx, inv_smul_smul]
  rw [is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g₁, hg₁, hga⟩ := hto0 a
  obtain ⟨g₂, hg₂, hgc⟩ := hto0 c
  have hb : g₁ • b ≠ 0 := by
    rw [← hga]
    exact fun h => hab (smul_left_cancel g₁ h).symm
  have hd : g₂ • d ≠ 0 := by
    rw [← hgc]
    exact fun h => hcd (smul_left_cancel g₂ h).symm
  obtain ⟨k, hk, hkx⟩ := exists_mulSubgroup_smul_eq hG hb hd
  refine ⟨⟨g₂⁻¹ * k * g₁, X₀.mul_mem (X₀.mul_mem (X₀.inv_mem hg₂) (hK hk)) hg₁⟩, ?_, ?_⟩
  · change (g₂⁻¹ * k * g₁) • a = c
    rw [mul_smul, mul_smul, hga, (mulSubgroup_le_stabilizer hk : k • (0 : F) = 0), ← hgc,
      inv_smul_smul]
  · change (g₂⁻¹ * k * g₁) • b = d
    rw [mul_smul, mul_smul, hkx, inv_smul_smul]

theorem Hyp.ofSubgroup (hG : Hyp G F m) (X₀ : Subgroup G) (h2 : IsMultiplyPretransitive X₀ F 2)
    (hK : mulSubgroup G F ≤ X₀) : Hyp X₀ F m where
  two_le := hG.two_le
  card := hG.card
  faithful := by
    have := hG.faithful
    infer_instance
  twoTrans := h2
  stab g hg := hG.stab g hg
  mul a := by
    obtain ⟨k, hk, hkx⟩ := exists_mulSubgroup hG a
    exact ⟨⟨k, hK hk⟩, hkx⟩

structure CE (G F : Type*) [Group G] [Field F] [MulAction G F] (m : ℕ) : Prop
    extends Hyp G F m where
  noReg : ¬ HasRegularNormal G F
  notGL : ¬ (m = 3 ∧ Nonempty (G ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))
  ih : ∀ X₀ : Subgroup G, X₀ ≠ ⊤ → Hyp X₀ F m →
    HasRegularNormal X₀ F ∨ (m = 3 ∧ Nonempty (X₀ ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))

end CFSG.GH74.Uniqueness.Hering
