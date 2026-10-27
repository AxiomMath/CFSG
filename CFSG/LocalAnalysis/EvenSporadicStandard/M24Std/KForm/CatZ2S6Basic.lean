module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm

open Subgroup
open scoped commutatorElement

abbrev Z2S6 : Type := Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)

@[expose] def a6Factor : Subgroup Z2S6 :=
  (⊥ : Subgroup (Multiplicative (ZMod 2))).prod (alternatingGroup (Fin 6))

theorem mem_a6Factor {x : Z2S6} : x ∈ a6Factor ↔ x.1 = 1 ∧ x.2 ∈ alternatingGroup (Fin 6) := by
  simp [a6Factor, Subgroup.mem_prod]

instance a6Factor_normal : a6Factor.Normal :=
  Subgroup.prod_normal _ _

@[expose] def a6FactorEquiv : ↥a6Factor ≃* alternatingGroup (Fin 6) where
  toFun x := ⟨x.1.2, (mem_a6Factor.1 x.2).2⟩
  invFun a := ⟨(1, a.1), mem_a6Factor.2 ⟨rfl, a.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (mem_a6Factor.1 x.2).1.symm
    · rfl
  right_inv a := rfl
  map_mul' x y := rfl

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem card_a6Factor : Nat.card a6Factor = 360 := by
  rw [Nat.card_congr a6FactorEquiv.toEquiv, card_alternatingGroup_six]

theorem card_z2s6 : Nat.card Z2S6 = 1440 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 6)),
    Fintype.card_perm, Fintype.card_fin]
  rfl

theorem commutatorElement_mem_a6Factor (x y : Z2S6) : ⁅x, y⁆ ∈ a6Factor := by
  rw [mem_a6Factor]
  constructor
  · show ⁅x.1, y.1⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  · rw [Equiv.Perm.mem_alternatingGroup]
    have h : (⁅x, y⁆ : Z2S6).2 = ⁅x.2, y.2⁆ := rfl
    rw [h, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)

theorem commutator_le_a6Factor (P Q : Subgroup Z2S6) : ⁅P, Q⁆ ≤ a6Factor :=
  Subgroup.commutator_le.2 fun x _ y _ => commutatorElement_mem_a6Factor x y

theorem z2s6_pow_four_of_pow_eight (x : Z2S6) (h : x ^ 8 = 1) : x ^ 4 = 1 := by
  have hperm : ∀ g : Equiv.Perm (Fin 6), g ^ 8 = 1 → g ^ 4 = 1 := by decide +kernel
  have h2 : ∀ a : Multiplicative (ZMod 2), a ^ 4 = 1 := by decide
  apply Prod.ext
  · exact h2 _
  · exact hperm x.2 (by simpa using congrArg Prod.snd h)

theorem z2s6_orderOf_ne_eight (x : Z2S6) : orderOf x ≠ 8 := by
  intro h8
  have h1 : x ^ 8 = 1 := by simpa [h8] using pow_orderOf_eq_one x
  have h2 : x ^ 4 = 1 := z2s6_pow_four_of_pow_eight x h1
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [h8] at h3
  exact absurd h3 (by norm_num)

theorem z2s6_data_of_injective {F : Type} [Group F] (Φ : F →* Z2S6)
    (hΦ : Function.Injective Φ) (hA : a6Factor ≤ Φ.range) :
    ∃ D : Subgroup F, D.Normal ∧ Nonempty (↥D ≃* alternatingGroup (Fin 6)) ∧
      (∀ P : Subgroup F, ⁅P, P⁆ = P → P ≤ D) ∧ Nat.card F ∣ 1440 ∧ 360 ∣ Nat.card F ∧
      (∀ x : F, orderOf x ≠ 8) ∧ (∀ a b : F, a * b * a⁻¹ * b⁻¹ ∈ D) := by
  have hmap : (a6Factor.comap Φ).map Φ = a6Factor := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hA
  refine ⟨a6Factor.comap Φ, inferInstance,
    ⟨((a6Factor.comap Φ).equivMapOfInjective Φ hΦ).trans
      ((MulEquiv.subgroupCongr hmap).trans a6FactorEquiv)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    have h1 : P.map Φ ≤ a6Factor := by
      calc P.map Φ = ⁅P, P⁆.map Φ := by rw [hP]
        _ = ⁅P.map Φ, P.map Φ⁆ := Subgroup.map_commutator _ _ _
        _ ≤ a6Factor := commutator_le_a6Factor _ _
    exact Subgroup.map_le_iff_le_comap.1 h1
  · have := Subgroup.card_dvd_of_injective Φ hΦ
    rwa [card_z2s6] at this
  · have h1 : Nat.card a6Factor ∣ Nat.card Φ.range := Subgroup.card_dvd_of_le hA
    have h2 : Nat.card Φ.range = Nat.card F :=
      (Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv).symm
    rwa [card_a6Factor, h2] at h1
  · intro x
    rw [← orderOf_injective Φ hΦ x]
    exact z2s6_orderOf_ne_eight _
  · intro a b
    rw [Subgroup.mem_comap]
    have := commutatorElement_mem_a6Factor (Φ a) (Φ b)
    simpa [commutatorElement_def] using this

end CFSG.EvenSporadicStandard.M24Std.KForm
